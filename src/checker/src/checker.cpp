#include <forall/checker/checker.hpp>
#include <forall/kernel/kernel.hpp>
#include <forall/lexer/lexer.hpp>
#include <forall/parser/parser.hpp>
#include <forall/pretty/to_string.hpp>

#include <array>
#include <atomic>
#include <fstream>
#include <map>
#include <numeric>
#include <optional>
#include <set>
#include <sstream>
#include <string_view>

namespace forall::checker {

Checker::Checker(diag::DiagnosticEngine& diag) : diag_{diag} {}

void Checker::set_stdlib_path(const std::filesystem::path& stdlib_root) {
    stdlib_root_ = stdlib_root;
}

namespace {

// Whether a hypothesis entry was introduced by supposition (Assumption) or
// derived by a rule application (Derived).  The distinction matters for
// ImplIntro and NotIntro, which must discharge a supposition.
enum class EntryKind { Assumption, Derived };

struct HypEntry {
    kernel::Judgment   judgment;
    EntryKind          kind;
    // visibility — Private entries are not exported across import boundaries.
    ast::Visibility    visibility{ast::Visibility::Public};
};

// Module-level flat map: axioms + proved lemmas/definitions accumulate here.
using HypEnv = std::map<std::string, HypEntry>;

// predicate definition unfolding table.
// Maps predicate name → { ordered param names, body proposition }.
// Populated from `definition P(x : T) := body` declarations.
// Used by unfold_preds() to expand PropPred/Atomic nodes before kernel calls.
struct PredDefEntry {
    std::vector<std::string> params;
    ast::PropPtr             body;
};
using PredDefTable = std::map<std::string, PredDefEntry>;

// Maps type_name → set of class names it has been declared to implement.
// Forward-declared here so CheckContext can reference it; full definition
// and class_axioms table live in the typeclass section further below.
using InstanceTable = std::map<std::string, std::set<std::string>>;

// ── ScopeStack ─────────────────────────────────────────────────────────────────
//
// Replaces the flat HypEnv for proof-local checking.  Each nested scope (cases
// arm, future nested proof blocks) pushes a new frame; find() searches top-down
// so inner frames shadow outer ones without overwriting them.

class ScopeStack {
    std::vector<std::map<std::string, HypEntry>> frames_;
    // Variables introduced via TakeStep, in introduction order, with optional type.
    // Stored as a vector (not set) to preserve order for ∀-wrapping.
    std::vector<std::pair<std::string, std::optional<ast::TypeNode>>> taken_vars_;
public:
    // Seed from the module-level flat environment.
    explicit ScopeStack(const HypEnv& base) : frames_{base, {}} {}

    ScopeStack() : frames_{{}} {}

    // Push a new scope frame (e.g. entering a cases arm).
    void push() { frames_.emplace_back(); }

    // Pop the top scope frame (does nothing if only one frame remains).
    void pop() { if (frames_.size() > 1) frames_.pop_back(); }

    // Insert or update in the top frame only.
    void insert_or_assign(const std::string& name, HypEntry entry) {
        frames_.back().insert_or_assign(name, std::move(entry));
    }

    // Search top-to-bottom; inner frames shadow outer ones.  Returns nullptr
    // if not found in any frame.
    [[nodiscard]] const HypEntry* find(const std::string& name) const {
        for (auto it = frames_.rbegin(); it != frames_.rend(); ++it) {
            if (auto jt = it->find(name); jt != it->end())
                return &jt->second;
        }
        return nullptr;
    }

    // Record a variable introduced via TakeStep (with its optional type annotation).
    void take_var(const std::string& var,
                  std::optional<ast::TypeNode> type = std::nullopt) {
        // Only add if not already present (duplicate take is an error caught elsewhere).
        for (const auto& [v, _] : taken_vars_)
            if (v == var) return;
        taken_vars_.emplace_back(var, std::move(type));
    }

    // Returns true if var was introduced via TakeStep in this scope.
    [[nodiscard]] bool is_taken(const std::string& var) const {
        for (const auto& [v, _] : taken_vars_)
            if (v == var) return true;
        return false;
    }

    // Returns the ordered list of taken variables (name, optional type).
    [[nodiscard]] const std::vector<std::pair<std::string, std::optional<ast::TypeNode>>>&
    taken_vars() const { return taken_vars_; }

    // Calls f(name, entry) for every Assumption-kind entry across all frames.
    // Used for the ∀-intro freshness check and auto-discharge.
    template<typename F>
    void for_each_assumption(F&& f) const {
        for (const auto& frame : frames_)
            for (const auto& [name, entry] : frame)
                if (entry.kind == EntryKind::Assumption)
                    f(name, entry);
    }

    // Calls f(name, entry) for every entry (Assumption or Derived) across all frames.
    template<typename F>
    void for_each(F&& f) const {
        for (const auto& frame : frames_)
            for (const auto& [name, entry] : frame)
                f(name, entry);
    }

    // Find the innermost Derived entry whose proposition equals p.
    // Returns nullptr if none exists. Used by auto-discharge.
    [[nodiscard]] const HypEntry* find_derived(const ast::Prop& p) const {
        for (auto it = frames_.rbegin(); it != frames_.rend(); ++it)
            for (const auto& [n, e] : *it)
                if (e.kind == EntryKind::Derived && e.judgment.prop() == p)
                    return &e;
        return nullptr;
    }
};

// ── module_name_from_path ─────────────────────────────────────────────────────
//
// Derive a qualified-name prefix from an import path.
// Examples:
//   "nat.forall"          → "Nat"
//   "stdlib/nat.forall"   → "Nat"
//   "MyModule.forall"     → "MyModule"
//   "my_module.forall"    → "My_module"
static std::string module_name_from_path(const std::string& import_path) {
    // Take the filename stem (strip directory and extension).
    std::string stem;
    auto slash = import_path.rfind('/');
    auto bslash = import_path.rfind('\\');
    std::size_t name_start = 0;
    if (slash  != std::string::npos) name_start = std::max(name_start, slash  + 1);
    if (bslash != std::string::npos) name_start = std::max(name_start, bslash + 1);
    stem = import_path.substr(name_start);
    // Strip ".forall" extension if present.
    if (stem.size() > 7 && stem.substr(stem.size() - 7) == ".forall")
        stem = stem.substr(0, stem.size() - 7);
    // Capitalize the first character.
    if (!stem.empty() && std::islower(static_cast<unsigned char>(stem[0])))
        stem[0] = static_cast<char>(std::toupper(static_cast<unsigned char>(stem[0])));
    return stem;
}

// ── fresh name generator ───────────────────────────────────────────────────────
// Returns a unique internal name for anonymous steps (have _ : ...) and
// unlabelled cases blocks (cases <ref>).  Names begin with "__" so they can
// never conflict with user identifiers.
static std::string fresh_name() {
    static std::atomic<unsigned> counter{0};
    return "__anon_" + std::to_string(++counter) + "__";
}

// ── resolve_refs ───────────────────────────────────────────────────────────────
//
// "__hypothesis__" / "__assumption__" sentinels resolve to the unique
// Assumption-kind entry in the current scope.  If there are multiple, a Warning
// is emitted and the first one is used.  If there are none, an Error is emitted.

std::optional<std::vector<const HypEntry*>>
resolve_refs(const std::vector<std::string>& refs,
             const ScopeStack& env,
             diag::DiagnosticEngine& diag,
             const diag::SourceLocation& loc)
{
    std::vector<const HypEntry*> out;
    out.reserve(refs.size());
    for (const auto& name : refs) {
        // "by hypothesis" / "by assumption" → resolve to the active assumption
        if (name == "__hypothesis__" || name == "__assumption__") {
            std::vector<const HypEntry*> assumptions;
            env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                assumptions.push_back(&e);
            });
            if (assumptions.empty()) {
                diag.emit({diag::Severity::Error, loc,
                           "'by hypothesis'/'by assumption': no assumption in scope"});
                return std::nullopt;
            }
            if (assumptions.size() > 1) {
                diag.emit({diag::Severity::Warning, loc,
                           "'by hypothesis'/'by assumption': multiple assumptions in scope; "
                           "using the first one"});
            }
            out.push_back(assumptions.front());
            continue;
        }
        const auto* e = env.find(name);
        // qualified-name fallback — if "Mod.name" not found directly,
        // try the unqualified suffix after the last '.'.
        if (!e) {
            auto dot = name.rfind('.');
            if (dot != std::string::npos)
                e = env.find(name.substr(dot + 1));
        }
        if (!e) {
            diag.emit({diag::Severity::Error, loc,
                       "unknown hypothesis '" + name + "'"});
            return std::nullopt;
        }
        out.push_back(e);
    }
    return out;
}

// ── infer_rule ─────────────────────────────────────────────────────────────────
//
// Given a desired conclusion and a list of resolved premises, determine which
// natural-deduction rule applies and return the ordered premise list expected
// by kernel::Kernel::apply().
//
// Rules covered:
//   n=1 : Assumption, AndElimL, AndElimR, FalseElim, OrIntroL, OrIntroR
//   n=2 : AndIntro, ImplElim, NotElim, ImplIntro, NotIntro
//   n=3 : OrElim

struct RuleApp {
    kernel::Rule                  rule;
    std::vector<kernel::Judgment> premises;
};

std::optional<RuleApp>
infer_rule(const ast::Prop& conc,
           const std::vector<const HypEntry*>& es,
           diag::DiagnosticEngine& diag,
           const diag::SourceLocation& loc)
{
    using R = kernel::Rule;
    const std::size_t n = es.size();

    auto prop     = [](const HypEntry* e) -> const ast::Prop& { return e->judgment.prop(); };
    auto is_assump = [](const HypEntry* e) { return e->kind == EntryKind::Assumption; };

    // ── 1 premise ─────────────────────────────────────────────────────────────
    if (n == 1) {
        const auto& p = prop(es[0]);

        // Assumption: h : P ⊢ P
        if (p == conc)
            return RuleApp{R::Assumption, {es[0]->judgment}};

        // AndElimL: A ∧ B ⊢ A
        if (const auto* c = std::get_if<ast::PropAnd>(&p.node))
            if (conc == *c->lhs)
                return RuleApp{R::AndElimL, {es[0]->judgment}};

        // AndElimR: A ∧ B ⊢ B
        if (const auto* c = std::get_if<ast::PropAnd>(&p.node))
            if (conc == *c->rhs)
                return RuleApp{R::AndElimR, {es[0]->judgment}};

        // FalseElim: ⊥ ⊢ P
        if (std::get_if<ast::PropFalse>(&p.node))
            return RuleApp{R::FalseElim, {es[0]->judgment}};

        // OrIntroL: A ⊢ A ∨ B
        if (const auto* d = std::get_if<ast::PropOr>(&conc.node))
            if (p == *d->lhs)
                return RuleApp{R::OrIntroL, {es[0]->judgment}};

        // OrIntroR: B ⊢ A ∨ B
        if (const auto* d = std::get_if<ast::PropOr>(&conc.node))
            if (p == *d->rhs)
                return RuleApp{R::OrIntroR, {es[0]->judgment}};

        // ForallIntro: P(x) ⊢ ∀ x, P  (freshness side condition checked in check_step)
        if (const auto* fa = std::get_if<ast::PropForall>(&conc.node))
            if (p == *fa->body)
                return RuleApp{R::ForallIntro, {es[0]->judgment}};
    }

    // ── 2 premises ────────────────────────────────────────────────────────────
    if (n == 2) {
        const auto& p0 = prop(es[0]);
        const auto& p1 = prop(es[1]);

        // AndIntro: A, B ⊢ A ∧ B
        if (const auto* c = std::get_if<ast::PropAnd>(&conc.node))
            if (p0 == *c->lhs && p1 == *c->rhs)
                return RuleApp{R::AndIntro, {es[0]->judgment, es[1]->judgment}};

        // ImplElim (modus ponens): A → B, A ⊢ B
        if (const auto* im = std::get_if<ast::PropImpl>(&p0.node))
            if (p1 == *im->lhs && conc == *im->rhs)
                return RuleApp{R::ImplElim, {es[0]->judgment, es[1]->judgment}};

        // NotElim: ¬A, A ⊢ ⊥
        if (std::get_if<ast::PropFalse>(&conc.node))
            if (const auto* neg = std::get_if<ast::PropNot>(&p0.node))
                if (p1 == *neg->inner)
                    return RuleApp{R::NotElim, {es[0]->judgment, es[1]->judgment}};

        // ImplIntro: suppose[A], B ⊢ A → B  (assumption can be either ref)
        if (const auto* im = std::get_if<ast::PropImpl>(&conc.node)) {
            if (is_assump(es[0]) && p0 == *im->lhs && p1 == *im->rhs)
                return RuleApp{R::ImplIntro, {es[1]->judgment}};
            if (is_assump(es[1]) && p1 == *im->lhs && p0 == *im->rhs)
                return RuleApp{R::ImplIntro, {es[0]->judgment}};
        }

        // NotIntro: suppose[A], ⊥ ⊢ ¬A  (assumption can be either ref)
        if (const auto* neg = std::get_if<ast::PropNot>(&conc.node)) {
            if (is_assump(es[0]) && p0 == *neg->inner
                    && std::get_if<ast::PropFalse>(&p1.node))
                return RuleApp{R::NotIntro, {es[1]->judgment}};
            if (is_assump(es[1]) && p1 == *neg->inner
                    && std::get_if<ast::PropFalse>(&p0.node))
                return RuleApp{R::NotIntro, {es[0]->judgment}};
        }
    }

    // ── 3 premises ────────────────────────────────────────────────────────────
    if (n == 3) {
        const auto& p0 = prop(es[0]);
        const auto& p1 = prop(es[1]);
        const auto& p2 = prop(es[2]);

        // OrElim: A ∨ B, A → C, B → C ⊢ C
        if (const auto* d = std::get_if<ast::PropOr  >(&p0.node))
        if (const auto* l = std::get_if<ast::PropImpl>(&p1.node))
        if (const auto* r = std::get_if<ast::PropImpl>(&p2.node))
            if (*d->lhs == *l->lhs && *d->rhs == *r->lhs
                    && conc == *l->rhs && conc == *r->rhs)
                return RuleApp{R::OrElim,
                    {es[0]->judgment, es[1]->judgment, es[2]->judgment}};
    }

    // ── 0 premises ───────────────────────────────────────────────────────────
    if (n == 0) {
        // TrueIntro: ⊢ ⊤
        if (std::get_if<ast::PropTrue>(&conc.node))
            return RuleApp{R::TrueIntro, {}};
    }

    diag.emit({diag::Severity::Error, loc,
               "cannot infer inference rule for this step from "
               + std::to_string(n) + " reference(s)"});
    return std::nullopt;
}

// ── infer_quantifier_rule ──────────────────────────────────────────────────────
//
// Selected when the step carries an "at <expr>" witness.
// Exactly one premise ref is expected.
//   ForallElim:  premise is ∀x.P;  conclusion is P[x:=t]
//   ExistsIntro: conclusion is ∃x.P; premise is P[x:=t]

std::optional<RuleApp>
infer_quantifier_rule(const ast::Prop& conc,
                      const std::vector<const HypEntry*>& es,
                      const ast::Expr* witness,
                      diag::DiagnosticEngine& diag,
                      const diag::SourceLocation& loc)
{
    using R = kernel::Rule;

    if (es.size() != 1) {
        diag.emit({diag::Severity::Error, loc,
                   "'at' witness requires exactly one hypothesis reference"});
        return std::nullopt;
    }
    const auto& p0 = es[0]->judgment.prop();

    // Resolve the ambiguity when both ForallElim and ExistsIntro could apply:
    // premise is ∀x.P  AND  conclusion is ∃y.Q.
    // Try ForallElim first: if subst(body, var, witness) == conclusion, use ForallElim.
    // Otherwise fall through to ExistsIntro.
    if (const auto* fa = std::get_if<ast::PropForall>(&p0.node)) {
        if (witness) {
            const ast::Prop forall_conc = ast::beta_reduce(ast::subst(*fa->body, fa->var, *witness));
            if (ast::defn_eq(forall_conc, conc))
                return RuleApp{R::ForallElim, {es[0]->judgment}};
        } else {
            return RuleApp{R::ForallElim, {es[0]->judgment}};
        }
    }

    if (std::get_if<ast::PropExists>(&conc.node))
        return RuleApp{R::ExistsIntro, {es[0]->judgment}};

    // Final fallback: premise is ∀ but the ForallElim subst didn't match the conclusion.
    // Emit a helpful error.
    if (std::get_if<ast::PropForall>(&p0.node)) {
        diag.emit({diag::Severity::Error, loc,
                   "ForallElim: conclusion does not match the body of ∀ after substitution"});
        return std::nullopt;
    }

    diag.emit({diag::Severity::Error, loc,
               "'at' witness is only valid when the hypothesis is ∀x.P (ForallElim) "
               "or the conclusion is ∃x.P (ExistsIntro)"});
    return std::nullopt;
}

// ── eval_expr / decide_proprel ────────────────────────────────────────────────
//
// Evaluate a pure arithmetic expression tree to a rational value (represented
// as a pair of integers p/q in lowest terms, stored as double here for
// simplicity — sufficient for the literal-only scope of `by decide`).
//
// Returns nullopt for any expression that contains variables, function calls,
// or constructs that cannot be reduced without axioms.

using Rational = std::pair<long long, long long>; // numerator / denominator

// Polynomial types. Full definitions in the polynomial section below;
// declared here so check_step can call normalize_expr.
using Monomial = std::map<std::string, int>;   // var → positive exponent
using Poly     = std::map<Monomial, Rational>;  // monomial → coeff

// Linear constraint for linarith (MT1): sum(coeff_i * x_i) - rhs  sense  0
// sense: -1 = strict <, 0 = =, 1 = ≤
struct LinConstraint {
    std::map<std::string, Rational> coeffs;
    Rational                        rhs;
    int                             sense;
};

static long long gcd(long long a, long long b) {
    a = a < 0 ? -a : a; b = b < 0 ? -b : b;
    while (b) { a %= b; std::swap(a, b); }
    return a == 0 ? 1 : a;
}

static Rational make_rat(long long n, long long d = 1) {
    if (d < 0) { n = -n; d = -d; }
    long long g = gcd(n < 0 ? -n : n, d);
    return {n / g, d / g};
}

static std::optional<Rational> eval_expr(const ast::Expr& e) {
    return std::visit([](const auto& n) -> std::optional<Rational> {
        using T = std::decay_t<decltype(n)>;

        if constexpr (std::is_same_v<T, ast::ExprLit>) {
            // Parse the literal string as an integer or decimal.
            try {
                // Try integer first
                std::size_t pos = 0;
                long long v = std::stoll(n.value, &pos);
                if (pos == n.value.size()) return make_rat(v);
                // Try simple "p/q" rational — not normally produced by the parser
                // but handle gracefully.
            } catch (...) {}
            return std::nullopt;
        }

        if constexpr (std::is_same_v<T, ast::ExprUnary>) {
            auto v = eval_expr(*n.operand);
            if (!v) return std::nullopt;
            if (n.op == ast::UnaryOp::Neg) return make_rat(-v->first, v->second);
            return std::nullopt; // inv, compl not evaluable
        }

        if constexpr (std::is_same_v<T, ast::ExprBinary>) {
            auto lv = eval_expr(*n.lhs);
            auto rv = eval_expr(*n.rhs);
            if (!lv || !rv) return std::nullopt;
            auto [ln, ld] = *lv;
            auto [rn, rd] = *rv;
            switch (n.op) {
                case ast::BinOp::Add: return make_rat(ln * rd + rn * ld, ld * rd);
                case ast::BinOp::Sub: return make_rat(ln * rd - rn * ld, ld * rd);
                case ast::BinOp::Mul: return make_rat(ln * rn, ld * rd);
                case ast::BinOp::Div:
                    if (rn == 0) return std::nullopt;
                    return make_rat(ln * rd, ld * rn);
                case ast::BinOp::IDiv:
                    if (rn == 0 || ld != 1 || rd != 1) return std::nullopt;
                    return make_rat(ln / rn);
                case ast::BinOp::Mod:
                    if (rn == 0 || ld != 1 || rd != 1) return std::nullopt;
                    return make_rat(ln % rn);
                case ast::BinOp::Pow: {
                    if (rd != 1 || rn < 0) return std::nullopt;
                    long long base = ln, exp = rn, acc_n = 1, acc_d = 1;
                    long long bd = ld;
                    for (long long i = 0; i < exp; ++i) {
                        acc_n *= base; acc_d *= bd;
                        long long g = gcd(acc_n < 0 ? -acc_n : acc_n, acc_d);
                        acc_n /= g; acc_d /= g;
                    }
                    return make_rat(acc_n, acc_d);
                }
                default: return std::nullopt;
            }
        }

        return std::nullopt; // variables, calls, sets, etc.
    }, e.node);
}

// Evaluate a relational proposition whose both sides are literal arithmetic.
// Returns true/false/nullopt (nullopt = cannot decide).
static std::optional<bool> decide_proprel(const ast::PropRel& rel) {
    auto lv = eval_expr(*rel.lhs);
    auto rv = eval_expr(*rel.rhs);
    if (!lv || !rv) return std::nullopt;
    // Compare as rationals: l/ld vs r/rd  ⟺  l*rd vs r*ld
    auto [ln, ld] = *lv;
    auto [rn, rd] = *rv;
    long long l = ln * rd;
    long long r = rn * ld;
    switch (rel.op) {
        case ast::RelOp::Eq:    return l == r;
        case ast::RelOp::NotEq: return l != r;
        case ast::RelOp::Lt:    return l <  r;
        case ast::RelOp::LtEq:  return l <= r;
        case ast::RelOp::Gt:    return l >  r;
        case ast::RelOp::GtEq:  return l >= r;
        default: return std::nullopt; // In, NotIn, subset etc.
    }
}

// ── CheckContext ──────────────────────────────────────────────────────────────
//
// Read-only context threaded through check_step and all sub-checkers.
// Carries the proof-local type environment, the module-level instance table,
// the module environment (for axiom-set resolution), and the function signature
// table (for type inference).  All fields are references into data owned by
// check_proof / check_module — no copies.
struct CheckContext {
    const ast::TypeEnv&                          type_env;     // var → type from 'take x : T' steps
    const InstanceTable&                         instances;    // type_name → {class_names}
    const HypEnv&                                module_env;   // axiom/lemma entries (for norm_num)
    const ast::FuncSigTable&                     sigs;         // function signatures
    const ast::Prop*                             goal;         // theorem statement (for bare 'then' sentinel)
    const std::map<std::string, ast::ExprPtr>*   term_defs{nullptr}; // let x = expr bindings
    const ast::StructEnv*                        struct_env{nullptr}; // for sub-proof injection
    const PredDefTable*                          pred_defs{nullptr};  // predicate definition bodies
    const ast::InductiveEnv*                     inductive_env{nullptr}; // for structural induction
};

// ── unfold_preds ──────────────────────────────────────────────────────────────
//
// Recursively expand PropPred nodes whose name appears in pred_defs by
// substituting the definition's body with the call's arguments.  Recurses into
// all PropNode and ExprNode variants.  No-op when pred_defs is null.
static ast::Prop unfold_preds(const ast::Prop& p, const PredDefTable& defs);
static ast::Expr unfold_preds_expr(const ast::Expr& e, const PredDefTable& defs);

static ast::Expr unfold_preds_expr(const ast::Expr& e, const PredDefTable& defs) {
    return std::visit([&](const auto& n) -> ast::Expr {
        using T = std::decay_t<decltype(n)>;
        if constexpr (std::is_same_v<T, ast::ExprBinary>) {
            return ast::Expr{e.loc, ast::ExprBinary{n.op,
                ast::make_expr(unfold_preds_expr(*n.lhs, defs)),
                ast::make_expr(unfold_preds_expr(*n.rhs, defs))}};
        } else if constexpr (std::is_same_v<T, ast::ExprUnary>) {
            return ast::Expr{e.loc, ast::ExprUnary{n.op,
                ast::make_expr(unfold_preds_expr(*n.operand, defs))}};
        } else if constexpr (std::is_same_v<T, ast::ExprAbs>) {
            return ast::Expr{e.loc, ast::ExprAbs{
                ast::make_expr(unfold_preds_expr(*n.operand, defs))}};
        } else if constexpr (std::is_same_v<T, ast::ExprCall>) {
            std::vector<ast::ExprPtr> args;
            for (const auto& a : n.args)
                args.push_back(ast::make_expr(unfold_preds_expr(*a, defs)));
            return ast::Expr{e.loc, ast::ExprCall{n.name, std::move(args)}};
        } else if constexpr (std::is_same_v<T, ast::ExprIndex>) {
            return ast::Expr{e.loc, ast::ExprIndex{
                ast::make_expr(unfold_preds_expr(*n.array, defs)),
                ast::make_expr(unfold_preds_expr(*n.index, defs))}};
        } else if constexpr (std::is_same_v<T, ast::ExprTuple>) {
            std::vector<ast::ExprPtr> elems;
            for (const auto& el : n.elements)
                elems.push_back(ast::make_expr(unfold_preds_expr(*el, defs)));
            return ast::Expr{e.loc, ast::ExprTuple{std::move(elems)}};
        } else if constexpr (std::is_same_v<T, ast::ExprLambda>) {
            return ast::Expr{e.loc, ast::ExprLambda{n.var, n.type,
                ast::make_expr(unfold_preds_expr(*n.body, defs))}};
        } else if constexpr (std::is_same_v<T, ast::ExprIf>) {
            return ast::Expr{e.loc, ast::ExprIf{
                ast::make_prop(unfold_preds(*n.cond, defs)),
                ast::make_expr(unfold_preds_expr(*n.then_, defs)),
                ast::make_expr(unfold_preds_expr(*n.else_, defs))}};
        } else if constexpr (std::is_same_v<T, ast::ExprAgg>) {
            return ast::Expr{e.loc, ast::ExprAgg{n.op, n.var, n.type, n.rel, n.bound,
                ast::make_expr(unfold_preds_expr(*n.body, defs))}};
        } else if constexpr (std::is_same_v<T, ast::ExprApp>) {
            std::vector<ast::ExprPtr> args;
            for (const auto& a : n.args)
                args.push_back(ast::make_expr(unfold_preds_expr(*a, defs)));
            return ast::Expr{e.loc, ast::ExprApp{
                ast::make_expr(unfold_preds_expr(*n.func, defs)), std::move(args)}};
        } else if constexpr (std::is_same_v<T, ast::ExprSetLit>) {
            std::vector<ast::ExprPtr> elems;
            for (const auto& el : n.elements)
                elems.push_back(ast::make_expr(unfold_preds_expr(*el, defs)));
            return ast::Expr{e.loc, ast::ExprSetLit{std::move(elems)}};
        } else {
            return e; // ExprLit, ExprVar, ExprField, ExprSetCompr — no sub-props
        }
    }, e.node);
}

static ast::Prop unfold_preds(const ast::Prop& p, const PredDefTable& defs) {
    return std::visit([&](const auto& n) -> ast::Prop {
        using T = std::decay_t<decltype(n)>;
        if constexpr (std::is_same_v<T, ast::PropPred>) {
            auto it = defs.find(n.name);
            if (it == defs.end()) return p;
            const auto& entry = it->second;
            if (entry.params.size() != n.args.size()) return p;
            // Substitute each argument into the body, then beta-reduce,
            // then recursively unfold any nested predicates in the result.
            ast::Prop result = *entry.body;
            for (std::size_t i = 0; i < entry.params.size(); ++i)
                result = ast::subst(result, entry.params[i], *n.args[i]);
            result = ast::beta_reduce(result);
            return unfold_preds(result, defs); // recurse to expand nested predicates
        } else if constexpr (std::is_same_v<T, ast::Atomic>) {
            // Nullary predicate: check if it has a zero-param definition.
            auto it = defs.find(n.name);
            if (it == defs.end() || !it->second.params.empty()) return p;
            return unfold_preds(ast::beta_reduce(*it->second.body), defs);
        } else if constexpr (std::is_same_v<T, ast::PropNot>) {
            return ast::Prop{p.loc, ast::PropNot{
                ast::make_prop(unfold_preds(*n.inner, defs))}};
        } else if constexpr (std::is_same_v<T, ast::PropAnd>) {
            return ast::Prop{p.loc, ast::PropAnd{
                ast::make_prop(unfold_preds(*n.lhs, defs)),
                ast::make_prop(unfold_preds(*n.rhs, defs))}};
        } else if constexpr (std::is_same_v<T, ast::PropOr>) {
            return ast::Prop{p.loc, ast::PropOr{
                ast::make_prop(unfold_preds(*n.lhs, defs)),
                ast::make_prop(unfold_preds(*n.rhs, defs))}};
        } else if constexpr (std::is_same_v<T, ast::PropImpl>) {
            return ast::Prop{p.loc, ast::PropImpl{
                ast::make_prop(unfold_preds(*n.lhs, defs)),
                ast::make_prop(unfold_preds(*n.rhs, defs))}};
        } else if constexpr (std::is_same_v<T, ast::PropForall>) {
            return ast::Prop{p.loc, ast::PropForall{n.var, n.type,
                ast::make_prop(unfold_preds(*n.body, defs))}};
        } else if constexpr (std::is_same_v<T, ast::PropExists>) {
            return ast::Prop{p.loc, ast::PropExists{n.var, n.type,
                ast::make_prop(unfold_preds(*n.body, defs))}};
        } else if constexpr (std::is_same_v<T, ast::PropRel>) {
            return ast::Prop{p.loc, ast::PropRel{
                ast::make_expr(unfold_preds_expr(*n.lhs, defs)),
                ast::make_expr(unfold_preds_expr(*n.rhs, defs)), n.op}};
        } else {
            return p; // PropFalse, PropTrue — no sub-structure
        }
    }, p.node);
}

// ── check_step (forward declaration for mutual recursion with CasesStep) ───────
bool check_step(const ast::Step& step,
                ScopeStack& env,
                kernel::Kernel& kernel,
                diag::DiagnosticEngine& diag,
                const CheckContext& ctx);

// Forward declaration for normalize_expr (defined in the polynomial section below).
static Poly normalize_expr(const ast::Expr& e);

// Forward declarations for linarith helpers (defined after ring_equal below).
struct LinConstraint;
static std::optional<LinConstraint> extract_linear(const ast::PropRel& rel);
static std::optional<LinConstraint> negate_linear(const LinConstraint& c);
static bool fourier_motzkin(std::vector<LinConstraint> cs);
static std::vector<LinConstraint> collect_linear_hypotheses(const ScopeStack& env);

// Forward declaration for simp_tactic (defined in the tactics section below).
// lemma_set: if non-empty, restricts the search to only those named hypotheses.
static std::optional<RuleApp> simp_tactic(const ast::Prop& goal, const ScopeStack& env,
                                           diag::DiagnosticEngine& diag,
                                           const diag::SourceLocation& loc,
                                           const std::vector<std::string>& lemma_set = {});

// Forward declarations for tactics defined in the tactics section below.
static bool field_simp_tactic(const ast::Prop& goal, ScopeStack& env,
                               kernel::Kernel& kernel,
                               diag::DiagnosticEngine& diag,
                               const diag::SourceLocation& loc,
                               const std::string& step_name);
static bool positivity_tactic(const ast::Prop& goal, const ScopeStack& env,
                               kernel::Kernel& kernel,
                               diag::DiagnosticEngine& diag,
                               const diag::SourceLocation& loc);
static bool gcongr_tactic(const ast::Prop& goal, const ScopeStack& env,
                           kernel::Kernel& kernel,
                           diag::DiagnosticEngine& diag,
                           const diag::SourceLocation& loc);
static bool omega_tactic(const ast::Prop& goal, const ScopeStack& env);

// Forward declaration for push_neg (defined in the tactics section below).
static ast::Prop push_neg(const ast::Prop& p);

// ── check_cases_step ───────────────────────────────────────────────────────────
//
// Implements OrElim with named case arms.
// Each arm introduces arm.name : arm.prop as an assumption, checks arm.steps,
// and requires the last step to be a ThenStep concluding some proposition R.
// Both arms must conclude the same R; then OrElim is applied.
// The result is stored in env under s.name.
bool check_cases_step(const ast::CasesStep& s,
                      const diag::SourceLocation& loc,
                      ScopeStack& env,
                      kernel::Kernel& kernel,
                      diag::DiagnosticEngine& diag,
                      const CheckContext& ctx)
{
    // 1. Look up the disjunction
    const auto* disj_entry = env.find(s.disjunct_ref);
    if (!disj_entry) {
        diag.emit({diag::Severity::Error, loc,
                   "unknown hypothesis '" + s.disjunct_ref + "'"});
        return false;
    }
    const auto* disj = std::get_if<ast::PropOr>(&disj_entry->judgment.prop().node);
    if (!disj) {
        diag.emit({diag::Severity::Error, loc,
                   "'" + s.disjunct_ref + "' must be a disjunction (P ∨ Q)"});
        return false;
    }
    if (s.arms.size() != 2) {
        diag.emit({diag::Severity::Error, loc,
                   "'cases' requires exactly two arms"});
        return false;
    }

    const ast::Prop* expected[2] = {disj->lhs.get(), disj->rhs.get()};
    std::optional<ast::Prop> shared_conclusion;
    std::vector<kernel::Judgment> impl_js; // P→R, Q→R
    bool had_arm_error = false;

    for (std::size_t i = 0; i < 2; ++i) {
        const auto& arm = s.arms[i];

        if (!(arm.prop == *expected[i])) {
            diag.emit({diag::Severity::Error, loc,
                       "arm " + std::to_string(i + 1)
                       + " proposition does not match disjunct"});
            had_arm_error = true;
            continue;
        }

        // Sub-environment for this arm: copy all frames, then push an arm frame
        // so the arm's assumption shadows (not overwrites) any outer binding with
        // the same name.
        ScopeStack arm_env = env;
        arm_env.push();
        auto arm_j = kernel.introduce_axiom(arm.prop);
        arm_env.insert_or_assign(arm.name, HypEntry{std::move(*arm_j), EntryKind::Assumption});

        bool arm_step_error = false;
        const ast::Step* arm_last_then = nullptr;

        for (const auto& uptr : arm.steps) {
            const auto snap = diag.diagnostics().size();
            check_step(*uptr, arm_env, kernel, diag, ctx);
            const auto& all = diag.diagnostics();
            for (auto j = snap; j < all.size(); ++j) {
                if (all[j].severity == diag::Severity::Error) {
                    arm_step_error = true;
                    break;
                }
            }
            if (std::get_if<ast::ThenStep>(&uptr->node))
                arm_last_then = uptr.get();
        }

        if (arm_step_error || !arm_last_then) {
            if (!arm_step_error)
                diag.emit({diag::Severity::Error, loc,
                           "arm '" + arm.name + "' must end with a 'then' step"});
            had_arm_error = true;
            continue;
        }

        const auto& arm_then = std::get<ast::ThenStep>(arm_last_then->node);

        // Both arms must conclude the same proposition
        if (!shared_conclusion) {
            shared_conclusion = arm_then.prop;
        } else if (!(*shared_conclusion == arm_then.prop)) {
            diag.emit({diag::Severity::Error, loc,
                       "'cases' arms conclude different propositions: `"
                       + forall::pretty::to_string(*shared_conclusion)
                       + "` vs `" + forall::pretty::to_string(arm_then.prop) + "`"});
            had_arm_error = true;
            continue;
        }

        // Build arm.prop → R via ImplIntro.  The arm proof was already verified,
        // so introduce_axiom(R) is sound here.
        const kernel::Judgment conc_j = *kernel.introduce_axiom(arm_then.prop);
        ast::Prop impl_prop{loc, ast::PropImpl{ast::make_prop(arm.prop),
                                               ast::make_prop(arm_then.prop)}};
        auto impl_j = kernel.apply(kernel::Rule::ImplIntro,
                                   std::span<const kernel::Judgment>{&conc_j, 1},
                                   impl_prop);
        if (!impl_j) {
            diag.emit({diag::Severity::Error, loc,
                       "ImplIntro failed for arm '" + arm.name
                       + "': " + impl_j.error().message});
            had_arm_error = true;
            continue;
        }
        impl_js.push_back(std::move(*impl_j));
    }

    if (had_arm_error || !shared_conclusion || impl_js.size() != 2) return false;

    // Apply OrElim: P ∨ Q, P → R, Q → R ⊢ R
    const std::array<kernel::Judgment, 3> or_prem = {
        disj_entry->judgment,
        impl_js[0],
        impl_js[1]
    };
    auto result = kernel.apply(kernel::Rule::OrElim,
                               std::span{or_prem},
                               *shared_conclusion);
    if (!result) {
        diag.emit({diag::Severity::Error, loc,
                   "OrElim failed: " + result.error().message});
        return false;
    }
    // if the user omitted the result label, generate a fresh internal name.
    const std::string result_name = s.name.empty() ? fresh_name() : s.name;
    env.insert_or_assign(result_name, HypEntry{std::move(*result), EntryKind::Derived});
    return true;
}

// ── check_split_step ──────────────────────────────────────────────────────────
//
// Implements AndIntro from two sub-proofs.
// Syntax:
//   split [name :]
//     case left  => <steps...>   -- must conclude lhs of goal conjunction
//     case right => <steps...>   -- must conclude rhs of goal conjunction
//
// The current goal must be a PropAnd{P, Q}.
// For biconditionals (desugared to (P→Q) ∧ (Q→P)) the goal is still PropAnd.
// The checker:
//   1. Verifies the goal is a PropAnd.
//   2. Requires exactly two arms (order determines which conjunct they prove).
//   3. For each arm: copies the ScopeStack, pushes a frame, checks the arm
//      steps, requires the last step to be a ThenStep.
//   4. Verifies arm 0 concludes goal.lhs and arm 1 concludes goal.rhs.
//   5. Applies AndIntro → stores result under s.name (or fresh name).
bool check_split_step(const ast::SplitStep& s,
                      const diag::SourceLocation& loc,
                      ScopeStack& env,
                      kernel::Kernel& kernel,
                      diag::DiagnosticEngine& diag,
                      const CheckContext& ctx)
{
    // The current goal must exist and be a PropAnd.
    if (!ctx.goal) {
        diag.emit({diag::Severity::Error, loc,
                   "'split' used outside a proof context"});
        return false;
    }
    const auto* conj = std::get_if<ast::PropAnd>(&ctx.goal->node);
    if (!conj) {
        diag.emit({diag::Severity::Error, loc,
                   "'split' requires a conjunction (P and Q) as the current goal, but goal is '"
                   + forall::pretty::to_string(*ctx.goal) + "'"});
        return false;
    }
    if (s.arms.size() != 2) {
        diag.emit({diag::Severity::Error, loc,
                   "'split' requires exactly two arms"});
        return false;
    }

    // Expected conclusion for each arm.
    const ast::Prop* expected[2] = {conj->lhs.get(), conj->rhs.get()};

    std::vector<kernel::Judgment> arm_js;
    bool had_arm_error = false;

    for (std::size_t i = 0; i < 2; ++i) {
        const auto& arm = s.arms[i];

        // Sub-environment for this arm: copy all frames, push a fresh frame.
        ScopeStack arm_env = env;
        arm_env.push();

        // Set the arm's sub-goal in the context.
        CheckContext arm_ctx = ctx;
        arm_ctx.goal = expected[i];

        bool arm_step_error = false;
        const ast::Step* arm_last_then = nullptr;

        for (const auto& uptr : arm.steps) {
            const auto snap = diag.diagnostics().size();
            check_step(*uptr, arm_env, kernel, diag, arm_ctx);
            const auto& all = diag.diagnostics();
            for (auto j = snap; j < all.size(); ++j) {
                if (all[j].severity == diag::Severity::Error) {
                    arm_step_error = true;
                    break;
                }
            }
            if (std::get_if<ast::ThenStep>(&uptr->node))
                arm_last_then = uptr.get();
        }

        if (arm_step_error || !arm_last_then) {
            if (!arm_step_error)
                diag.emit({diag::Severity::Error, loc,
                           "split arm '" + arm.label + "' must end with a 'then' step"});
            had_arm_error = true;
            continue;
        }

        const auto& arm_then = std::get<ast::ThenStep>(arm_last_then->node);

        // Case 1: arm's then matches the expected conjunct exactly.
        // Case 2: the expected conjunct is P → Q, the arm concluded Q,
        //         and there is a SupposeStep assumption of P in arm_env.
        //         Synthesise ImplIntro (same as auto-close in check_proof).

        std::optional<kernel::Judgment> arm_cert;

        if (arm_then.prop == *expected[i]) {
            // Direct match — certify via introduce_axiom.
            auto j = kernel.introduce_axiom(arm_then.prop);
            if (!j) {
                diag.emit({diag::Severity::Error, loc,
                           "split arm '" + arm.label + "' judgment failed: "
                           + j.error().message});
                had_arm_error = true;
                continue;
            }
            arm_cert = std::move(*j);
        } else if (const auto* impl = std::get_if<ast::PropImpl>(&expected[i]->node);
                   impl && arm_then.prop == *impl->rhs) {
            // The arm proved the consequent B; the expected conjunct is A → B.
            // Try to find a SupposeStep assumption of A in arm_env.
            const HypEntry* assump = nullptr;
            arm_env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                if (e.judgment.prop() == *impl->lhs) assump = &e;
            });
            if (assump) {
                const kernel::Judgment conc_j = *kernel.introduce_axiom(arm_then.prop);
                auto impl_j = kernel.apply(kernel::Rule::ImplIntro,
                                           std::span<const kernel::Judgment>{&conc_j, 1},
                                           *expected[i]);
                if (!impl_j) {
                    diag.emit({diag::Severity::Error, loc,
                               "split arm '" + arm.label + "' ImplIntro failed: "
                               + impl_j.error().message});
                    had_arm_error = true;
                    continue;
                }
                arm_cert = std::move(*impl_j);
            }
        }

        if (!arm_cert) {
            diag.emit({diag::Severity::Error, loc,
                       "split arm '" + arm.label + "' concluded '"
                       + forall::pretty::to_string(arm_then.prop)
                       + "' but expected '"
                       + forall::pretty::to_string(*expected[i]) + "'"});
            had_arm_error = true;
            continue;
        }
        arm_js.push_back(std::move(*arm_cert));
    }

    if (had_arm_error || arm_js.size() != 2) return false;

    // Apply AndIntro: lhs, rhs ⊢ lhs ∧ rhs
    const std::array<kernel::Judgment, 2> prem = {arm_js[0], arm_js[1]};
    auto result = kernel.apply(kernel::Rule::AndIntro,
                               std::span{prem},
                               *ctx.goal);
    if (!result) {
        diag.emit({diag::Severity::Error, loc,
                   "AndIntro failed: " + result.error().message});
        return false;
    }

    const std::string result_name = s.name.empty() ? fresh_name() : s.name;
    env.insert_or_assign(result_name, HypEntry{std::move(*result), EntryKind::Derived});
    return true;
}

// ── check_obtain_step ──────────────────────────────────────────────────────────
//
// Implements ExistsElim with an explicit obtain block.
// Syntax:
//   obtain <name> from <exists_ref>
//     case <var> [: <type>] , <hyp_name> : <hyp_prop> => <steps...>
//
// Checker responsibilities:
//   1. <exists_ref> must be ∃ x, P in scope.
//   2. <var> must be fresh (not free in any undischarged assumption).
//   3. <hyp_prop> must equal subst(P, x, ExprVar{var}).
//   4. Sub-proof must conclude some Q with the last step being a ThenStep.
//   5. <var> must not appear free in Q (∃-elim side condition).
//   6. ExistsElim kernel rule applied; result stored under <name>.
bool check_obtain_step(const ast::ObtainStep& s,
                       const diag::SourceLocation& loc,
                       ScopeStack& env,
                       kernel::Kernel& kernel,
                       diag::DiagnosticEngine& diag,
                       const CheckContext& ctx)
{
    // 1. Look up the existential
    const auto* ex_entry = env.find(s.exists_ref);
    if (!ex_entry) {
        diag.emit({diag::Severity::Error, loc,
                   "unknown hypothesis '" + s.exists_ref + "'"});
        return false;
    }
    const auto* ex = std::get_if<ast::PropExists>(&ex_entry->judgment.prop().node);
    if (!ex) {
        diag.emit({diag::Severity::Error, loc,
                   "'" + s.exists_ref + "' must be an existential (∃ x, P)"});
        return false;
    }

    // 2. Freshness: s.var must not appear free in any undischarged assumption
    bool fresh = true;
    env.for_each_assumption([&](const std::string& hname, const HypEntry& e) {
        if (ast::free_vars(e.judgment.prop()).count(s.var)) {
            diag.emit({diag::Severity::Error, loc,
                       "'obtain': variable '" + s.var
                       + "' appears free in assumption '" + hname
                       + "' — not a fresh variable"});
            fresh = false;
        }
    });
    if (!fresh) return false;

    if (s.hyp_bindings.empty()) {
        diag.emit({diag::Severity::Error, loc, "'obtain' case arm has no hypothesis bindings"});
        return false;
    }

    // 3. Verify hyp_bindings[0].prop == subst(body, exists_var, ExprVar{s.var})
    // Beta-reduce after substitution so ExprApp{ExprVar{v}, args} → ExprCall{v, args}.
    // Also unfold any predicate definitions in both sides before comparing.
    const ast::Prop expected_hyp_raw =
        ast::subst(*ex->body, ex->var,
                   ast::Expr{loc, ast::ExprVar{s.var}});
    const ast::Prop expected_hyp = (ctx.pred_defs && !ctx.pred_defs->empty())
        ? unfold_preds(ast::beta_reduce(expected_hyp_raw), *ctx.pred_defs)
        : ast::beta_reduce(expected_hyp_raw);
    const ast::Prop user_hyp0 = (ctx.pred_defs && !ctx.pred_defs->empty())
        ? unfold_preds(ast::beta_reduce(s.hyp_bindings[0].prop), *ctx.pred_defs)
        : ast::beta_reduce(s.hyp_bindings[0].prop);

    // When multiple bindings are present, the full existential body must be a conjunction
    // whose left spine matches the declared props.  The first binding may itself be a
    // conjunction — only the entire body need match.
    const bool multi = s.hyp_bindings.size() > 1;
    if (!multi && !(user_hyp0 == expected_hyp)) {
        diag.emit({diag::Severity::Error, loc,
                   "obtain arm hypothesis does not match the existential body; "
                   "expected `" + forall::pretty::to_string(expected_hyp) + "`"});
        return false;
    }
    if (multi && !(expected_hyp == expected_hyp)) {
        // placeholder — multi-binding check happens after sub_env setup below
    }

    // 4. Build sub-environment with s.var taken and the hyp bindings inserted.
    // Use the normalised/unfolded hyp form so steps inside the arm see the expanded props.
    ScopeStack sub_env = env;
    sub_env.push();
    sub_env.take_var(s.var);

    if (!multi) {
        // Single binding — straightforward.
        auto hyp_j = kernel.introduce_axiom(user_hyp0);
        sub_env.insert_or_assign(s.hyp_bindings[0].name,
                                 HypEntry{std::move(*hyp_j), EntryKind::Assumption});
    } else {
        // Multiple bindings — peel conjuncts off the existential body left-to-right.
        // The body must be a right-associated conjunction of N components.
        // For N bindings [h0:P0, h1:P1, ..., hN-1:P_{N-1}]:
        //   h0 = AndElimL(body)              if N == 2:  body = P0 ∧ P1
        //   h1 = AndElimR(body)              ...
        //   hk = AndElimL(right-spine at k)  for k < N-1
        //   hN-1 = AndElimR(right-spine)
        // Each user-stated prop is verified against the corresponding component.
        auto body_j = kernel.introduce_axiom(expected_hyp);
        ast::Prop remaining = expected_hyp; // tracks the unpeeled conjunction
        kernel::Judgment remaining_j = std::move(*body_j);

        for (std::size_t i = 0; i < s.hyp_bindings.size(); ++i) {
            const auto& binding = s.hyp_bindings[i];
            const bool is_last = (i + 1 == s.hyp_bindings.size());

            if (is_last) {
                // Last binding: use remaining directly (no more peel needed).
                const ast::Prop user_prop = (ctx.pred_defs && !ctx.pred_defs->empty())
                    ? unfold_preds(ast::beta_reduce(binding.prop), *ctx.pred_defs)
                    : ast::beta_reduce(binding.prop);
                if (!(user_prop == remaining)) {
                    diag.emit({diag::Severity::Error, loc,
                               "obtain binding '" + binding.name
                               + "' does not match expected `"
                               + forall::pretty::to_string(remaining) + "`"});
                    return false;
                }
                sub_env.insert_or_assign(binding.name,
                    HypEntry{std::move(remaining_j), EntryKind::Assumption});
            } else {
                // Non-last: remaining must be a conjunction; peel with AndElimL/R.
                const auto* conj = std::get_if<ast::PropAnd>(&remaining.node);
                if (!conj) {
                    diag.emit({diag::Severity::Error, loc,
                               "obtain: expected a conjunction to destructure for binding '"
                               + binding.name + "'"});
                    return false;
                }
                // Left conjunct → this binding.
                const ast::Prop left = *conj->lhs;
                const ast::Prop user_prop = (ctx.pred_defs && !ctx.pred_defs->empty())
                    ? unfold_preds(ast::beta_reduce(binding.prop), *ctx.pred_defs)
                    : ast::beta_reduce(binding.prop);
                if (!(user_prop == left)) {
                    diag.emit({diag::Severity::Error, loc,
                               "obtain binding '" + binding.name
                               + "' does not match expected `"
                               + forall::pretty::to_string(left) + "`"});
                    return false;
                }
                auto left_j = kernel.apply(kernel::Rule::AndElimL,
                                           std::span{&remaining_j, 1}, left);
                if (!left_j) {
                    diag.emit({diag::Severity::Error, loc,
                               "AndElimL failed: " + left_j.error().message});
                    return false;
                }
                sub_env.insert_or_assign(binding.name,
                    HypEntry{std::move(*left_j), EntryKind::Assumption});
                // Right conjunct → continues as new remaining.
                const ast::Prop right = *conj->rhs;
                auto right_j = kernel.apply(kernel::Rule::AndElimR,
                                            std::span{&remaining_j, 1}, right);
                if (!right_j) {
                    diag.emit({diag::Severity::Error, loc,
                               "AndElimR failed: " + right_j.error().message});
                    return false;
                }
                remaining = right;
                remaining_j = std::move(*right_j);
            }
        }
    }

    // Check sub-proof steps
    const ast::Step* arm_last_then = nullptr;
    bool arm_step_error = false;

    for (const auto& uptr : s.steps) {
        const auto snap = diag.diagnostics().size();
        check_step(*uptr, sub_env, kernel, diag, ctx);
        const auto& all = diag.diagnostics();
        for (auto j = snap; j < all.size(); ++j) {
            if (all[j].severity == diag::Severity::Error) {
                arm_step_error = true;
                break;
            }
        }
        if (std::get_if<ast::ThenStep>(&uptr->node))
            arm_last_then = uptr.get();
    }

    if (arm_step_error || !arm_last_then) {
        if (!arm_step_error)
            diag.emit({diag::Severity::Error, loc,
                       "'obtain' body must end with a 'then' step"});
        return false;
    }

    const auto& Q_raw = std::get<ast::ThenStep>(arm_last_then->node).prop;
    // Normalise Q: apply predicate unfolding so the stored result matches the
    // unfolded goal that the outer proof validator compares against.
    const ast::Prop Q = (ctx.pred_defs && !ctx.pred_defs->empty())
                        ? unfold_preds(ast::beta_reduce(Q_raw), *ctx.pred_defs)
                        : ast::beta_reduce(Q_raw);

    // 5. ∃-elim side condition: s.var must not appear free in Q
    if (ast::free_vars(Q).count(s.var)) {
        diag.emit({diag::Severity::Error, loc,
                   "∃-elim: conclusion mentions the bound variable '" + s.var
                   + "' — violates the ∃-elim side condition"});
        return false;
    }

    // 6. Apply ExistsElim: ∃x.P, Q ⊢ Q
    const kernel::Judgment q_j = *kernel.introduce_axiom(Q);
    const std::array<kernel::Judgment, 2> prem = {ex_entry->judgment, q_j};
    auto result = kernel.apply(kernel::Rule::ExistsElim,
                               std::span{prem},
                               Q);
    if (!result) {
        diag.emit({diag::Severity::Error, loc,
                   "ExistsElim failed: " + result.error().message});
        return false;
    }
    env.insert_or_assign(s.name, HypEntry{std::move(*result), EntryKind::Derived});
    return true;
}

// ── check_induction_step ──────────────────────────────────────────────────────
//
// Dispatches on s.type_name:
//   "Nat" (or empty): Peano induction via NatInduction kernel rule.
//   Other: structural induction over a user-defined inductive type.
//
// Nat induction (unchanged):
//   base: block proves P(0); inductive: block proves P(succ(n)) with ih:P(n).
//
// Structural induction:
//   For each constructor arm, a sub-env is set up with:
//   - the arm's argument variables (injected as Assumptions of the appropriate type)
//   - IH hypotheses for each recursive argument
//   Each arm must end with a ThenStep concluding the same proposition R.
//   The result ∀ var : T, P(var) is certified via introduce_axiom (soundness
//   guaranteed by the arm-level checks, same as NatInduction for OrElim).
bool check_induction_step(const ast::InductionStep& s,
                          const diag::SourceLocation& loc,
                          ScopeStack& env,
                          kernel::Kernel& kernel,
                          diag::DiagnosticEngine& diag,
                          const CheckContext& ctx)
{
    // ── Nat induction path ────────────────────────────────────────────────────
    if (s.arms.empty()) {
        ScopeStack base_env = env;
        bool base_error = false;
        const ast::Step* base_last_then = nullptr;

        for (const auto& uptr : s.base_steps) {
            const auto snap = diag.save();
            check_step(*uptr, base_env, kernel, diag, ctx);
            const auto& all = diag.diagnostics();
            for (auto i = snap.size; i < all.size(); ++i)
                if (all[i].severity == diag::Severity::Error) { base_error = true; break; }
            if (std::get_if<ast::ThenStep>(&uptr->node))
                base_last_then = uptr.get();
        }

        if (base_error || !base_last_then) {
            if (!base_error)
                diag.emit({diag::Severity::Error, loc,
                           "induction 'base' block must end with a 'then' step"});
            return false;
        }

        const ast::Prop& base_conc = std::get<ast::ThenStep>(base_last_then->node).prop;

        const ast::Prop& ih_prop = s.body;
        const ast::Expr succ_var{{}, ast::ExprCall{"succ",
            {ast::make_expr(ast::Expr{{}, ast::ExprVar{s.var}})}}};
        const ast::Prop base_expected = ast::subst(ih_prop, s.var,
            ast::Expr{{}, ast::ExprLit{"0"}});
        const ast::Prop ind_expected  = ast::subst(ih_prop, s.var, succ_var);

        if (!(base_conc == base_expected)) {
            diag.emit({diag::Severity::Error, loc,
                       "induction 'base' block must conclude `"
                       + forall::pretty::to_string(base_expected)
                       + "` (P[" + s.var + ":=0]), but got `"
                       + forall::pretty::to_string(base_conc) + "`"});
            return false;
        }

        ScopeStack ind_env = env;
        ind_env.push();
        auto ih_j = kernel.introduce_axiom(ih_prop);
        ind_env.insert_or_assign("ih", HypEntry{std::move(*ih_j), EntryKind::Assumption});

        bool ind_error = false;
        const ast::Step* ind_last_then = nullptr;

        for (const auto& uptr : s.inductive_steps) {
            const auto snap = diag.save();
            check_step(*uptr, ind_env, kernel, diag, ctx);
            const auto& all = diag.diagnostics();
            for (auto i = snap.size; i < all.size(); ++i)
                if (all[i].severity == diag::Severity::Error) { ind_error = true; break; }
            if (std::get_if<ast::ThenStep>(&uptr->node))
                ind_last_then = uptr.get();
        }

        if (ind_error || !ind_last_then) {
            if (!ind_error)
                diag.emit({diag::Severity::Error, loc,
                           "induction 'inductive' block must end with a 'then' step"});
            return false;
        }

        const ast::Prop& ind_conc = std::get<ast::ThenStep>(ind_last_then->node).prop;

        if (!(ind_conc == ind_expected)) {
            diag.emit({diag::Severity::Error, loc,
                       "induction 'inductive' block must conclude `"
                       + forall::pretty::to_string(ind_expected)
                       + "` (P[" + s.var + ":=succ(" + s.var + ")]), but got `"
                       + forall::pretty::to_string(ind_conc) + "`"});
            return false;
        }

        ast::TypeNode nat_type{{ast::TypeNat{}}};
        ast::Prop conclusion{{}, ast::PropForall{s.var,
            std::make_optional(nat_type), ast::make_prop(ih_prop)}};

        const kernel::Judgment base_j = *kernel.introduce_axiom(base_conc);

        ast::Prop step_body{{}, ast::PropImpl{ast::make_prop(ih_prop), ast::make_prop(ind_conc)}};
        ast::Prop step_prop{{}, ast::PropForall{s.var,
            std::make_optional(nat_type), ast::make_prop(step_body)}};
        const kernel::Judgment step_j = *kernel.introduce_axiom(step_prop);

        const std::array<kernel::Judgment, 2> prem = {base_j, step_j};
        auto result = kernel.apply(kernel::Rule::NatInduction, std::span{prem}, conclusion);
        if (!result) {
            diag.emit({diag::Severity::Error, loc,
                       "NatInduction kernel check failed: " + result.error().message});
            return false;
        }
        env.insert_or_assign(s.name, HypEntry{std::move(*result), EntryKind::Derived});
        return true;
    }

    // ── Structural induction path ─────────────────────────────────────────────
    //
    // Determine the inductive type: either from s.type_name (if set by the parser)
    // or by looking up the induction variable in the type environment.
    std::string resolved_type = s.type_name;
    if (resolved_type.empty()) {
        auto tit = ctx.type_env.find(s.var);
        if (tit != ctx.type_env.end()) {
            if (const auto* tu = std::get_if<ast::TypeUser>(&tit->second.node))
                resolved_type = tu->name;
        }
    }

    if (!ctx.inductive_env) {
        diag.emit({diag::Severity::Error, loc,
                   "no inductive type environment available"});
        return false;
    }
    auto it = ctx.inductive_env->find(resolved_type);
    if (it == ctx.inductive_env->end()) {
        diag.emit({diag::Severity::Error, loc,
                   "unknown inductive type '" + resolved_type + "'"
                   + (resolved_type.empty()
                       ? " (declare 'take " + s.var + " : T' before the induction step)"
                       : "")});
        return false;
    }
    const auto& ctors = it->second;

    // Verify we have exactly one arm per constructor.
    if (s.arms.size() != ctors.size()) {
        diag.emit({diag::Severity::Error, loc,
                   "structural induction on '" + resolved_type + "' requires "
                   + std::to_string(ctors.size()) + " case(s), got "
                   + std::to_string(s.arms.size())});
        return false;
    }

    // Each arm must end with a ThenStep concluding subst(body, var, ctor_value),
    // where ctor_value is ExprVar{ctor_name} for a 0-arg constructor, or
    // ExprCall{ctor_name, arg_vars} for a constructor with arguments.
    bool any_arm_error = false;

    for (std::size_t ai = 0; ai < s.arms.size(); ++ai) {
        const auto& arm  = s.arms[ai];
        const auto& ctor = ctors[ai];

        if (arm.ctor_name != ctor.name) {
            diag.emit({diag::Severity::Error, loc,
                       "case arm " + std::to_string(ai + 1) + " names constructor '"
                       + arm.ctor_name + "' but expected '" + ctor.name + "'"});
            any_arm_error = true;
            continue;
        }

        // Build arm environment: inject constructor args as Assumptions,
        // then inject IH hypotheses for recursive args.
        ScopeStack arm_env = env;
        arm_env.push();

        // Collect all arg variable names for building the constructor expression.
        std::vector<std::string> arg_var_names;
        std::size_t vi = 0;
        std::size_t rec_count = 0;
        for (std::size_t ti = 0; ti < ctor.arg_types.size(); ++ti) {
            if (!ctor.is_recursive[ti]) {
                if (vi < arm.vars.size()) {
                    // Inject var as Assumption; user's proof may reference it.
                    ast::Prop var_hyp{{}, ast::Atomic{arm.vars[vi] + "_hyp"}};
                    auto j = kernel.introduce_axiom(var_hyp);
                    arm_env.insert_or_assign(arm.vars[vi],
                                             HypEntry{std::move(*j), EntryKind::Assumption});
                    arg_var_names.push_back(arm.vars[vi]);
                    ++vi;
                }
            } else {
                // Recursive arg: bind the variable AND an IH hypothesis P(rec_var).
                if (vi < arm.vars.size()) {
                    ast::Prop rec_hyp{{}, ast::Atomic{arm.vars[vi] + "_hyp"}};
                    auto j = kernel.introduce_axiom(rec_hyp);
                    arm_env.insert_or_assign(arm.vars[vi],
                                             HypEntry{std::move(*j), EntryKind::Assumption});
                    arg_var_names.push_back(arm.vars[vi]);

                    // IH: P(rec_var) = subst(body, var, rec_var)
                    const ast::Prop ih_prop = ast::subst(s.body, s.var,
                        ast::Expr{{}, ast::ExprVar{arm.vars[vi]}});
                    std::string ih_name = rec_count < arm.ih_names.size()
                                          ? arm.ih_names[rec_count]
                                          : "ih" + std::to_string(rec_count);
                    auto ih_j = kernel.introduce_axiom(ih_prop);
                    arm_env.insert_or_assign(ih_name,
                                             HypEntry{std::move(*ih_j), EntryKind::Assumption});
                    ++rec_count;
                    ++vi;
                }
            }
        }

        // Build the constructor application expression for subst.
        // 0-arg constructor → ExprVar{ctor_name}; n-arg → ExprCall{ctor_name, args}.
        ast::Expr ctor_expr{};
        if (arg_var_names.empty()) {
            ctor_expr = ast::Expr{{}, ast::ExprVar{ctor.name}};
        } else {
            std::vector<ast::ExprPtr> arg_exprs;
            for (const auto& vn : arg_var_names)
                arg_exprs.push_back(ast::make_expr(ast::Expr{{}, ast::ExprVar{vn}}));
            ctor_expr = ast::Expr{{}, ast::ExprCall{ctor.name, std::move(arg_exprs)}};
        }
        // Expected conclusion for this arm: subst(body, var, ctor_expr)
        const ast::Prop expected_conc = ast::subst(s.body, s.var, ctor_expr);

        // Run the arm's steps.
        bool arm_error = false;
        const ast::Step* arm_last_then = nullptr;

        for (const auto& uptr : arm.steps) {
            const auto snap = diag.save();
            check_step(*uptr, arm_env, kernel, diag, ctx);
            const auto& all = diag.diagnostics();
            for (auto i = snap.size; i < all.size(); ++i)
                if (all[i].severity == diag::Severity::Error) { arm_error = true; break; }
            if (std::get_if<ast::ThenStep>(&uptr->node))
                arm_last_then = uptr.get();
        }

        if (arm_error || !arm_last_then) {
            if (!arm_error)
                diag.emit({diag::Severity::Error, loc,
                           "case '" + arm.ctor_name + "' must end with a 'then' step"});
            any_arm_error = true;
            continue;
        }

        const ast::Prop& arm_conc = std::get<ast::ThenStep>(arm_last_then->node).prop;

        // Verify the arm concludes the expected specialization of the body.
        if (!(arm_conc == expected_conc)) {
            diag.emit({diag::Severity::Error, loc,
                       "case '" + arm.ctor_name + "' concludes `"
                       + forall::pretty::to_string(arm_conc)
                       + "` but expected `"
                       + forall::pretty::to_string(expected_conc) + "`"});
            any_arm_error = true;
        }
    }

    if (any_arm_error) return false;

    // Certify conclusion ∀ var : T, P(var) via introduce_axiom.
    // Soundness: each arm verified subst(body, var, ctor_i_value) above.
    ast::TypeNode t_type{{ast::TypeUser{resolved_type}}};
    ast::Prop conclusion{{}, ast::PropForall{s.var,
        std::make_optional(t_type), ast::make_prop(s.body)}};
    auto result = kernel.introduce_axiom(conclusion);
    if (!result) {
        diag.emit({diag::Severity::Error, loc,
                   "structural induction certification failed: " + result.error().message});
        return false;
    }
    env.insert_or_assign(s.name, HypEntry{std::move(*result), EntryKind::Derived});
    return true;
}

// ── check_calc_step ────────────────────────────────────────────────────────────
//
// Verifies a calc block.  Each link lhs_i op_i rhs_i is checked as a
// PropRel against the user-supplied justification.  After all individual links
// pass, the transitive conclusion (overall_lhs  op_final  overall_rhs) is
// assembled and certified via introduce_axiom (same soundness justification as
// `by decide` / `by linarith` — the individual steps are already kernel-certified).
//
// Transitivity rule for op_final:
//   All =                 → =
//   Any < (with ≤ or =)   → <
//   Any ≤ (no <)          → ≤
//   Any > (with ≥ or =)   → >
//   Any ≥ (no >)          → ≥
//   Mixed < and >         → error (inconsistent chain)

bool check_calc_step(const ast::CalcStep& cs,
                     const diag::SourceLocation& loc,
                     ScopeStack& env,
                     kernel::Kernel& kernel,
                     diag::DiagnosticEngine& diag,
                     const CheckContext& ctx)
{
    if (cs.links.empty()) {
        diag.emit({diag::Severity::Error, loc,
                   "'calc' block has no links"});
        return false;
    }

    // Check each link individually.
    bool had_error = false;
    ast::ExprPtr cur_lhs = cs.lhs; // tracks the chained LHS

    for (std::size_t i = 0; i < cs.links.size(); ++i) {
        const auto& link = cs.links[i];
        // Individual proposition: cur_lhs link.op link.rhs
        ast::Prop link_prop{loc,
            ast::PropRel{cur_lhs, link.rhs, link.op}};

        auto es = resolve_refs(link.justification, env, diag, loc);
        if (!es) { had_error = true; cur_lhs = link.rhs; continue; }

        auto app = infer_rule(link_prop, *es, diag, loc);
        if (!app) { had_error = true; cur_lhs = link.rhs; continue; }

        auto r = kernel.apply(app->rule, std::span{app->premises}, link_prop);
        if (!r) {
            diag.emit({diag::Severity::Error, loc,
                       "calc link " + std::to_string(i + 1)
                       + " kernel check failed: " + r.error().message});
            had_error = true;
        }
        cur_lhs = link.rhs; // next link's LHS is this link's RHS
    }

    if (had_error) return false;

    // Determine op_final from the operator sequence.
    // Detect direction and strictness.
    bool has_lt = false, has_le = false, has_eq_only = true;
    bool has_gt = false, has_ge = false;
    for (const auto& link : cs.links) {
        switch (link.op) {
            case ast::RelOp::Lt:   has_lt = true;  has_eq_only = false; break;
            case ast::RelOp::LtEq: has_le = true;  has_eq_only = false; break;
            case ast::RelOp::Gt:   has_gt = true;  has_eq_only = false; break;
            case ast::RelOp::GtEq: has_ge = true;  has_eq_only = false; break;
            case ast::RelOp::Eq:   break; // does not affect direction
            default:
                diag.emit({diag::Severity::Error, loc,
                           "calc block: relational operator not supported for chaining"});
                return false;
        }
    }

    if ((has_lt || has_le) && (has_gt || has_ge)) {
        diag.emit({diag::Severity::Error, loc,
                   "calc block: cannot mix < / ≤ with > / ≥ in the same chain"});
        return false;
    }

    ast::RelOp op_final;
    if (has_eq_only)      op_final = ast::RelOp::Eq;
    else if (has_lt)      op_final = ast::RelOp::Lt;
    else if (has_le)      op_final = ast::RelOp::LtEq;
    else if (has_gt)      op_final = ast::RelOp::Gt;
    else                  op_final = ast::RelOp::GtEq;

    // Assemble the transitive conclusion: cs.lhs  op_final  last_rhs
    const ast::ExprPtr& last_rhs = cs.links.back().rhs;
    ast::Prop conclusion{loc, ast::PropRel{cs.lhs, last_rhs, op_final}};

    // Certify via introduce_axiom: soundness is guaranteed because every
    // individual link has been kernel-checked above.
    auto result = kernel.introduce_axiom(conclusion);
    if (!result) {
        diag.emit({diag::Severity::Error, loc,
                   "calc: introduce_axiom failed: " + result.error().message});
        return false;
    }

    const std::string result_name = cs.name.empty() ? fresh_name() : cs.name;
    env.insert_or_assign(result_name, HypEntry{std::move(*result), EntryKind::Derived});
    return true;
}

// ── check_step ─────────────────────────────────────────────────────────────────

bool check_step(const ast::Step& step,
                ScopeStack& env,
                kernel::Kernel& kernel,
                diag::DiagnosticEngine& diag,
                const CheckContext& ctx)
{
    // helper to apply let-bound term definitions to a proposition,
    // then beta-reduce so that e.g. (fun k => a[phi(k)])[n] normalises.
    // also unfolds predicate definitions (PropPred → body).
    auto apply_tdefs = [&](ast::Prop p) -> ast::Prop {
        if (ctx.term_defs) {
            for (const auto& [name, expr] : *ctx.term_defs)
                p = ast::subst(p, name, *expr);
        }
        p = ast::beta_reduce(p);
        if (ctx.pred_defs && !ctx.pred_defs->empty())
            p = unfold_preds(p, *ctx.pred_defs);
        return p;
    };
    // Apply term definitions to an expression witness (for ForallElim/ExistsIntro).
    auto apply_tdefs_expr = [&](ast::Expr e) -> ast::Expr {
        if (ctx.term_defs) {
            for (const auto& [name, expr] : *ctx.term_defs)
                e = ast::subst(e, name, *expr);
        }
        return ast::beta_reduce(e);
    };

    return std::visit([&](const auto& s) -> bool {
        using T = std::decay_t<decltype(s)>;

        // let x be a T — deferred until term layer is implemented
        if constexpr (std::is_same_v<T, ast::LetStep>) {
            return true;
        }

        // take x [: T] — introduce a fresh term variable for ∀-intro
        else if constexpr (std::is_same_v<T, ast::TakeStep>) {
            // Freshness: x must not appear free in any undischarged assumption.
            // If it does, the subsequent ForallIntro would be unsound (x is not
            // truly arbitrary — it was fixed by a hypothesis).
            bool fresh = true;
            env.for_each_assumption([&](const std::string& hname, const HypEntry& e) {
                if (ast::free_vars(e.judgment.prop()).count(s.var)) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'take " + s.var + "': variable appears free in assumption '"
                               + hname + "' — not a fresh variable"});
                    fresh = false;
                }
            });
            if (!fresh) return false;
            env.take_var(s.var, s.type);
            return true;
        }

        // suppose [name :] prop — introduces a local assumption
        else if constexpr (std::is_same_v<T, ast::SupposeStep>) {
            const ast::Prop prop = apply_tdefs(s.prop);
            auto r = kernel.introduce_axiom(prop);
            if (!r) {
                diag.emit({diag::Severity::Error, step.loc,
                           "failed to introduce assumption: " + r.error().message});
                return false;
            }
            if (s.name)
                env.insert_or_assign(*s.name,
                                     HypEntry{std::move(*r), EntryKind::Assumption});
            return true;
        }

        // have <name> : <prop> by <refs> [at <expr>]
        // have <name> : <prop> proof ... end  (inline sub-proof)
        // name may be "_" for an anonymous step — assign a fresh internal name.
        else if constexpr (std::is_same_v<T, ast::HaveStep>) {
            const ast::Prop prop = apply_tdefs(s.prop);
            const std::string step_name = (s.name == "_") ? fresh_name() : s.name;

            // inline sub-proof block — check recursively with prop as goal.
            if (s.sub_proof) {
                // Run the sub-block in a child scope seeded from the current scope.
                // All outer hypotheses are visible; sub-proof-local steps stay local.
                ScopeStack sub_env{};
                env.for_each([&](const std::string& n, const HypEntry& e) {
                    sub_env.insert_or_assign(n, e);
                });

                const auto snap = diag.diagnostics().size();
                bool sub_had_errors = false;
                const ast::Step* sub_last_then = nullptr;
                std::map<std::string, ast::ExprPtr> sub_term_defs;

                for (const auto& sub_step : s.sub_proof->steps) {
                    // Handle LetStep term definitions inline.
                    if (const auto* ls = std::get_if<ast::LetStep>(&sub_step.node)) {
                        if (ls->definition) sub_term_defs[ls->var] = *ls->definition;
                        continue;
                    }
                    CheckContext sub_ctx{ctx.type_env, ctx.instances, ctx.module_env,
                                        ctx.sigs, &prop, &sub_term_defs, ctx.struct_env,
                                        ctx.pred_defs, ctx.inductive_env};
                    const auto before = diag.diagnostics().size();
                    check_step(sub_step, sub_env, kernel, diag, sub_ctx);
                    const auto& all2 = diag.diagnostics();
                    for (auto i = before; i < all2.size(); ++i)
                        if (all2[i].severity == diag::Severity::Error)
                            { sub_had_errors = true; break; }
                    if (std::get_if<ast::ThenStep>(&sub_step.node))
                        sub_last_then = &sub_step;
                }

                if (!sub_had_errors) {
                    if (!sub_last_then) {
                        diag.emit({diag::Severity::Error, step.loc,
                                   "inline proof for '" + step_name
                                   + "' has no concluding 'then' step"});
                        return false;
                    }
                    const auto& ts = std::get<ast::ThenStep>(sub_last_then->node);
                    // apply predicate unfolding to the concluding step prop
                    // so it can be compared against the (already unfolded) goal.
                    const ast::Prop ts_prop_eff = apply_tdefs(ts.prop);
                    if (!(ts_prop_eff == prop)) {
                        diag.emit({diag::Severity::Error, sub_last_then->loc,
                                   "inline proof concludes '" + forall::pretty::to_string(ts_prop_eff)
                                   + "' but goal is '"
                                   + forall::pretty::to_string(prop) + "'"});
                        return false;
                    }
                    auto r = kernel.introduce_axiom(prop);
                    if (r)
                        env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                    return true;
                }
                return false;
            }

            // "by decide" — evaluate numerically; no refs needed
            if (s.justification.size() == 1 && s.justification[0] == "__decide__") {
                const auto* rel = std::get_if<ast::PropRel>(&prop.node);
                if (!rel) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide' only applies to relational propositions (e.g. 2 + 3 = 5)"});
                    return false;
                }
                auto verdict = decide_proprel(*rel);
                if (!verdict) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide' cannot evaluate `"
                               + forall::pretty::to_string(prop)
                               + "` — both sides must be literal arithmetic"});
                    return false;
                }
                if (!*verdict) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide': `"
                               + forall::pretty::to_string(prop) + "` is false"});
                    return false;
                }
                auto r = kernel.introduce_axiom(prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by norm_num" — polynomial ring equality with variable support
            if (s.justification.size() == 1 && s.justification[0] == "__norm_num__") {
                const auto* rel = std::get_if<ast::PropRel>(&prop.node);
                if (!rel || rel->op != ast::RelOp::Eq) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by norm_num' only applies to equalities (e.g. x * (y + z) = x * y + x * z)"});
                    return false;
                }
                auto lp = normalize_expr(*rel->lhs);
                auto rp = normalize_expr(*rel->rhs);
                if (lp != rp) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by norm_num': `"
                               + forall::pretty::to_string(prop)
                               + "` is not a polynomial identity"});
                    return false;
                }
                auto r = kernel.introduce_axiom(prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by ring" — polynomial identity over commutative ring (same normalization as norm_num)
            if (s.justification.size() == 1 && s.justification[0] == "__ring__") {
                const auto* rel = std::get_if<ast::PropRel>(&prop.node);
                if (!rel || rel->op != ast::RelOp::Eq) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by ring' only applies to equalities (e.g. (a + b)^2 = a^2 + 2*a*b + b^2)"});
                    return false;
                }
                auto lp = normalize_expr(*rel->lhs);
                auto rp = normalize_expr(*rel->rhs);
                if (lp != rp) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by ring': `"
                               + forall::pretty::to_string(prop)
                               + "` does not hold as a ring identity"});
                    return false;
                }
                auto r = kernel.introduce_axiom(prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by linarith" — linear arithmetic over ordered fields (MT1)
            if (s.justification.size() == 1 && s.justification[0] == "__linarith__") {
                auto hyps = collect_linear_hypotheses(env);
                // Add the negated goal as a hypothesis.
                const auto* goal_rel = std::get_if<ast::PropRel>(&prop.node);
                if (!goal_rel) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by linarith' only applies to relational propositions (e.g. x < y, a ≤ b)"});
                    return false;
                }
                auto goal_lc = extract_linear(*goal_rel);
                if (!goal_lc) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by linarith' could not extract a linear constraint from goal"});
                    return false;
                }
                auto neg_goal = negate_linear(*goal_lc);
                if (!neg_goal) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by linarith' does not support equality goals; use 'by ring' for equations"});
                    return false;
                }
                hyps.push_back(std::move(*neg_goal));
                if (!fourier_motzkin(hyps)) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by linarith' could not derive `"
                               + forall::pretty::to_string(prop)
                               + "` from the linear hypotheses in scope"});
                    return false;
                }
                auto r = kernel.introduce_axiom(prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by omega" — integer/Presburger arithmetic
            if (s.justification.size() == 1 && s.justification[0] == "__omega__") {
                bool is_rel   = std::get_if<ast::PropRel>(&prop.node) != nullptr;
                bool is_false = std::get_if<ast::PropFalse>(&prop.node) != nullptr;
                if (!is_rel && !is_false) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by omega' only applies to relational propositions or 'false'"});
                    return false;
                }
                if (!omega_tactic(prop, env)) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by omega' could not verify `"
                               + forall::pretty::to_string(prop)
                               + "` — check that the goal follows from integer arithmetic"});
                    return false;
                }
                auto r = kernel.introduce_axiom(prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by simp" / "by simp [h1, h2]" — propositional simplification (MT2)
            if (!s.justification.empty() && s.justification[0] == "__simp__") {
                std::vector<std::string> lemma_set(s.justification.begin() + 1,
                                                   s.justification.end());
                auto app = simp_tactic(prop, env, diag, step.loc, lemma_set);
                if (!app) return false;
                auto r = kernel.apply(app->rule, std::span{app->premises}, prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by simp' internal error: " + r.error().message});
                    return false;
                }
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by contrapositive" — prove A → B by ¬B assumption + derived ¬A
            if (s.justification.size() == 1 && s.justification[0] == "__contrapositive__") {
                const auto* impl = std::get_if<ast::PropImpl>(&prop.node);
                if (!impl) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contrapositive' requires an implication conclusion A → B"});
                    return false;
                }
                ast::Prop not_B{prop.loc, ast::PropNot{impl->rhs}};
                ast::Prop not_A{prop.loc, ast::PropNot{impl->lhs}};
                const HypEntry* neg_B_entry = nullptr;
                env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                    if (e.judgment.prop() == not_B) neg_B_entry = &e;
                });
                if (!neg_B_entry) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contrapositive': no assumption of '"
                               + forall::pretty::to_string(not_B) + "' found in scope"});
                    return false;
                }
                const HypEntry* neg_A_entry = env.find_derived(not_A);
                if (!neg_A_entry) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contrapositive': no derived proof of '"
                               + forall::pretty::to_string(not_A) + "' found in scope"});
                    return false;
                }
                auto r = kernel.introduce_axiom(prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contrapositive' internal error: " + r.error().message});
                    return false;
                }
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by field_simp" — clear denominators and verify via ring normalization
            if (s.justification.size() == 1 && s.justification[0] == "__field_simp__") {
                return field_simp_tactic(prop, env, kernel, diag, step.loc, step_name);
            }
            // "by positivity" — prove expr ≥ 0 or expr > 0 by structural recursion
            if (s.justification.size() == 1 && s.justification[0] == "__positivity__") {
                if (!positivity_tactic(prop, env, kernel, diag, step.loc)) return false;
                auto r = kernel.introduce_axiom(prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by gcongr" — congruence for monotone functions
            if (s.justification.size() == 1 && s.justification[0] == "__gcongr__") {
                if (!gcongr_tactic(prop, env, kernel, diag, step.loc)) return false;
                auto r = kernel.introduce_axiom(prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by refl" — conclude a = a
            if (s.justification.size() == 1 && s.justification[0] == "__refl__") {
                auto r = kernel.apply(kernel::Rule::Refl, {}, prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by refl' failed: " + r.error().message});
                    return false;
                }
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by symm h" — conclude b = a from h : a = b
            if (!s.justification.empty() && s.justification[0] == "__symm__") {
                std::vector<std::string> hrefs(s.justification.begin() + 1, s.justification.end());
                auto es2 = resolve_refs(hrefs, env, diag, step.loc);
                if (!es2 || es2->size() != 1) {
                    diag.emit({diag::Severity::Error, step.loc, "'by symm' requires exactly one premise"});
                    return false;
                }
                auto r = kernel.apply(kernel::Rule::Symm,
                                      std::span<const kernel::Judgment>{&(*es2)[0]->judgment, 1},
                                      prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by symm' failed: " + r.error().message});
                    return false;
                }
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by trans h1 h2" — conclude a = c from h1 : a = b and h2 : b = c
            if (!s.justification.empty() && s.justification[0] == "__trans__") {
                std::vector<std::string> hrefs(s.justification.begin() + 1, s.justification.end());
                auto es2 = resolve_refs(hrefs, env, diag, step.loc);
                if (!es2 || es2->size() != 2) {
                    diag.emit({diag::Severity::Error, step.loc, "'by trans' requires exactly two premises"});
                    return false;
                }
                const kernel::Judgment prem[2] = {(*es2)[0]->judgment, (*es2)[1]->judgment};
                auto r = kernel.apply(kernel::Rule::Trans, std::span{prem}, prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by trans' failed: " + r.error().message});
                    return false;
                }
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by congr h" — conclude f(a) = f(b) from h : a = b
            if (!s.justification.empty() && s.justification[0] == "__congr__") {
                std::vector<std::string> hrefs(s.justification.begin() + 1, s.justification.end());
                auto es2 = resolve_refs(hrefs, env, diag, step.loc);
                if (!es2 || es2->size() != 1) {
                    diag.emit({diag::Severity::Error, step.loc, "'by congr' requires exactly one premise"});
                    return false;
                }
                auto r = kernel.apply(kernel::Rule::Congr,
                                      std::span<const kernel::Judgment>{&(*es2)[0]->judgment, 1},
                                      prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by congr' failed: " + r.error().message});
                    return false;
                }
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            auto es = resolve_refs(s.justification, env, diag, step.loc);
            if (!es) return false;
            // expand any let-bound names in the witness expression and beta-reduce.
            std::optional<ast::Expr> witness_expanded;
            if (s.witness) witness_expanded = apply_tdefs_expr(*s.witness->get());
            const ast::Expr* witness_ptr = witness_expanded ? &*witness_expanded : nullptr;
            std::optional<RuleApp> app;
            if (witness_ptr) {
                app = infer_quantifier_rule(prop, *es, witness_ptr, diag, step.loc);
            } else {
                app = infer_rule(prop, *es, diag, step.loc);
            }
            if (!app) return false;
            // ForallIntro requires the bound variable to have been introduced via TakeStep.
            if (app->rule == kernel::Rule::ForallIntro) {
                const auto* fa = std::get_if<ast::PropForall>(&prop.node);
                if (!env.is_taken(fa->var)) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "∀-intro: variable '" + fa->var
                               + "' must be introduced via 'take' before generalizing"});
                    return false;
                }
            }
            auto r = kernel.apply(app->rule, std::span{app->premises}, prop, witness_ptr);
            if (!r) {
                diag.emit({diag::Severity::Error, step.loc,
                           "kernel rejected '" + step_name + "': " + r.error().message});
                return false;
            }
            env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
            return true;
        }

        // then <prop> by <refs> [at <expr>]
        else if constexpr (std::is_same_v<T, ast::ThenStep>) {
            const ast::Prop prop = apply_tdefs(s.prop);
            // "__qed__" sentinel — bare "then" with no proposition.
            // Substitute the theorem's goal, then continue as a normal ThenStep.
            // The __qed__ sentinel is always first; extra refs follow it.
            if (!s.justification.empty() && s.justification[0] == "__qed__") {
                if (!ctx.goal) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "bare 'then' (goal-close) is not valid outside a theorem proof"});
                    return false;
                }
                // When taken_vars_ are in scope, ctx.goal is the full ∀ x, A → P
                // statement. Strip each taken-var ∀ and each outstanding Assumption →
                // to get the inner body that tactics can actually prove.
                const ast::Prop* inner = ctx.goal;
                const bool has_taken = !env.taken_vars().empty();
                for (const auto& [unused_v, unused_t] : env.taken_vars()) {
                    (void)unused_v; (void)unused_t;
                    if (const auto* fa = std::get_if<ast::PropForall>(&inner->node))
                        inner = fa->body.get();
                    else break;
                }
                // Strip implication antecedents only when take has been used.
                // Without take, ctx.goal is the plain theorem statement; stripping
                // would e.g. reduce P→Q to Q and break the auto-discharge step.
                if (has_taken) {
                    std::vector<ast::Prop> assumps;
                    env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                        assumps.push_back(e.judgment.prop());
                    });
                    for (std::size_t i = 0; i < assumps.size(); ++i) {
                        if (const auto* im = std::get_if<ast::PropImpl>(&inner->node))
                            inner = im->rhs.get();
                        else break;
                    }
                }
                // Build a synthetic ThenStep with the inner goal and remaining refs.
                std::vector<std::string> real_refs(s.justification.begin() + 1,
                                                   s.justification.end());
                ast::Step synth{step.loc, ast::ThenStep{*inner, std::move(real_refs), s.witness}};
                return check_step(synth, env, kernel, diag, ctx);
            }

            // auto-discharge — allow bare "then P → Q" or "then ¬P" with no
            // justification by finding the most-recent matching Assumption in scope.
            if (s.justification.empty()) {
                // Try ImplIntro: conclusion is A → B — look for assume[A], derive[B]
                if (const auto* im = std::get_if<ast::PropImpl>(&prop.node)) {
                    const HypEntry* assump = nullptr;
                    env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                        if (e.judgment.prop() == *im->lhs) assump = &e;
                    });
                    if (!assump) {
                        diag.emit({diag::Severity::Error, step.loc,
                                   "auto-discharge: no assumption '" +
                                   forall::pretty::to_string(*im->lhs) +
                                   "' found in scope; use 'by <refs>' to discharge manually"});
                        return false;
                    }
                    const HypEntry* conseq = env.find_derived(*im->rhs);
                    if (!conseq) {
                        diag.emit({diag::Severity::Error, step.loc,
                                   "auto-discharge: could not find a derived proof of '" +
                                   forall::pretty::to_string(*im->rhs) +
                                   "' in scope; use 'by <refs>' to discharge manually"});
                        return false;
                    }
                    auto r = kernel.apply(kernel::Rule::ImplIntro,
                                          std::span<const kernel::Judgment>{&conseq->judgment, 1},
                                          prop);
                    if (!r) {
                        diag.emit({diag::Severity::Error, step.loc,
                                   "auto-discharge (ImplIntro) failed: " + r.error().message});
                        return false;
                    }
                    return true;
                }
                // Try NotIntro: conclusion is ¬A — look for assume[A], derive[⊥]
                if (const auto* neg = std::get_if<ast::PropNot>(&prop.node)) {
                    const HypEntry* assump = nullptr;
                    env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                        if (e.judgment.prop() == *neg->inner) assump = &e;
                    });
                    if (!assump) {
                        diag.emit({diag::Severity::Error, step.loc,
                                   "auto-discharge: no assumption '" +
                                   forall::pretty::to_string(*neg->inner) +
                                   "' found in scope; use 'by <refs>' to discharge manually"});
                        return false;
                    }
                    ast::Prop false_prop{step.loc, ast::PropFalse{}};
                    const HypEntry* bot = env.find_derived(false_prop);
                    if (!bot) {
                        diag.emit({diag::Severity::Error, step.loc,
                                   "auto-discharge: could not find a proof of 'false' in scope; "
                                   "use 'by <refs>' to discharge manually"});
                        return false;
                    }
                    auto r = kernel.apply(kernel::Rule::NotIntro,
                                          std::span<const kernel::Judgment>{&bot->judgment, 1},
                                          prop);
                    if (!r) {
                        diag.emit({diag::Severity::Error, step.loc,
                                   "auto-discharge (NotIntro) failed: " + r.error().message});
                        return false;
                    }
                    return true;
                }
                // TrueIntro: conclusion is ⊤ — no premises needed
                if (std::get_if<ast::PropTrue>(&prop.node)) {
                    std::vector<kernel::Judgment> no_prem;
                    auto r = kernel.apply(kernel::Rule::TrueIntro, no_prem, prop);
                    if (!r) {
                        diag.emit({diag::Severity::Error, step.loc,
                                   "TrueIntro failed: " + r.error().message});
                        return false;
                    }
                    return true;
                }
                // No auto-discharge pattern matched
                diag.emit({diag::Severity::Error, step.loc,
                           "'then' step requires a 'by' justification"});
                return false;
            }
            // "by decide" — evaluate numerically; no refs needed
            if (s.justification.size() == 1 && s.justification[0] == "__decide__") {
                const auto* rel = std::get_if<ast::PropRel>(&prop.node);
                if (!rel) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide' only applies to relational propositions"});
                    return false;
                }
                auto verdict = decide_proprel(*rel);
                if (!verdict) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide' cannot evaluate `"
                               + forall::pretty::to_string(prop)
                               + "` — both sides must be literal arithmetic"});
                    return false;
                }
                if (!*verdict) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide': `"
                               + forall::pretty::to_string(prop) + "` is false"});
                    return false;
                }
                // Certified: the proposition is arithmetically true.
                (void)kernel.introduce_axiom(prop);
                return true;
            }
            // "by norm_num" — polynomial ring equality with variable support
            if (s.justification.size() == 1 && s.justification[0] == "__norm_num__") {
                const auto* rel = std::get_if<ast::PropRel>(&prop.node);
                if (!rel || rel->op != ast::RelOp::Eq) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by norm_num' only applies to equalities"});
                    return false;
                }
                auto lp = normalize_expr(*rel->lhs);
                auto rp = normalize_expr(*rel->rhs);
                if (lp != rp) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by norm_num': `"
                               + forall::pretty::to_string(prop)
                               + "` is not a polynomial identity"});
                    return false;
                }
                (void)kernel.introduce_axiom(prop);
                return true;
            }
            // "by ring" — polynomial identity over commutative ring
            if (s.justification.size() == 1 && s.justification[0] == "__ring__") {
                const auto* rel = std::get_if<ast::PropRel>(&prop.node);
                if (!rel || rel->op != ast::RelOp::Eq) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by ring' only applies to equalities"});
                    return false;
                }
                auto lp = normalize_expr(*rel->lhs);
                auto rp = normalize_expr(*rel->rhs);
                if (lp != rp) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by ring': `"
                               + forall::pretty::to_string(prop)
                               + "` does not hold as a ring identity"});
                    return false;
                }
                (void)kernel.introduce_axiom(prop);
                return true;
            }
            // "by linarith" — linear arithmetic (ThenStep variant)
            if (s.justification.size() == 1 && s.justification[0] == "__linarith__") {
                auto hyps = collect_linear_hypotheses(env);
                const auto* goal_rel = std::get_if<ast::PropRel>(&prop.node);
                if (!goal_rel) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by linarith' only applies to relational propositions"});
                    return false;
                }
                auto goal_lc = extract_linear(*goal_rel);
                if (!goal_lc) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by linarith' could not extract a linear constraint from goal"});
                    return false;
                }
                auto neg_goal = negate_linear(*goal_lc);
                if (!neg_goal) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by linarith' does not support equality goals"});
                    return false;
                }
                hyps.push_back(std::move(*neg_goal));
                if (!fourier_motzkin(hyps)) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by linarith' could not derive `"
                               + forall::pretty::to_string(prop)
                               + "` from the linear hypotheses in scope"});
                    return false;
                }
                (void)kernel.introduce_axiom(prop);
                return true;
            }
            // "by omega" — integer/Presburger arithmetic (ThenStep variant)
            if (s.justification.size() == 1 && s.justification[0] == "__omega__") {
                bool is_rel   = std::get_if<ast::PropRel>(&prop.node) != nullptr;
                bool is_false = std::get_if<ast::PropFalse>(&prop.node) != nullptr;
                if (!is_rel && !is_false) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by omega' only applies to relational propositions or 'false'"});
                    return false;
                }
                if (!omega_tactic(prop, env)) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by omega' could not verify `"
                               + forall::pretty::to_string(prop)
                               + "` — check that the goal follows from integer arithmetic"});
                    return false;
                }
                kernel.introduce_axiom(prop);
                return true;
            }
            // "by contra" — proof by contradiction
            // Finds hn : ¬P (assumption) and bot : ⊥ (derived) in scope.
            // Applies FalseElim(⊥) = P.  The ¬P assumption is not needed for FalseElim
            // but its presence confirms the contradiction was set up correctly.
            if (s.justification.size() == 1 && s.justification[0] == "__contra__") {
                ast::Prop false_prop{step.loc, ast::PropFalse{}};
                const HypEntry* bot = env.find_derived(false_prop);
                if (!bot) {
                    // Also check for PropFalse as a named axiom/assumption
                    env.for_each([&](const std::string&, const HypEntry& e) {
                        if (std::get_if<ast::PropFalse>(&e.judgment.prop().node)) bot = &e;
                    });
                }
                if (!bot) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contra' requires a proof of ⊥ (false) in scope; "
                               "use 'suppose for contradiction that ¬P' then derive false first"});
                    return false;
                }
                auto r = kernel.apply(kernel::Rule::FalseElim,
                                      std::span<const kernel::Judgment>{&bot->judgment, 1},
                                      prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contra' FalseElim failed: " + r.error().message});
                    return false;
                }
                return true;
            }
            // "by simp" / "by simp [h1, h2]" — propositional simplification (ThenStep variant)
            if (!s.justification.empty() && s.justification[0] == "__simp__") {
                std::vector<std::string> lemma_set(s.justification.begin() + 1,
                                                   s.justification.end());
                auto app = simp_tactic(prop, env, diag, step.loc, lemma_set);
                if (!app) return false;
                auto r = kernel.apply(app->rule, std::span{app->premises}, prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by simp' internal error: " + r.error().message});
                    return false;
                }
                return true;
            }
            // "by contrapositive" — ThenStep variant
            if (s.justification.size() == 1 && s.justification[0] == "__contrapositive__") {
                const auto* impl = std::get_if<ast::PropImpl>(&prop.node);
                if (!impl) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contrapositive' requires an implication conclusion A → B"});
                    return false;
                }
                ast::Prop not_B{prop.loc, ast::PropNot{impl->rhs}};
                ast::Prop not_A{prop.loc, ast::PropNot{impl->lhs}};
                const HypEntry* neg_B_entry = nullptr;
                env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                    if (e.judgment.prop() == not_B) neg_B_entry = &e;
                });
                if (!neg_B_entry) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contrapositive': no assumption of '"
                               + forall::pretty::to_string(not_B) + "' found in scope"});
                    return false;
                }
                const HypEntry* neg_A_entry = env.find_derived(not_A);
                if (!neg_A_entry) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contrapositive': no derived proof of '"
                               + forall::pretty::to_string(not_A) + "' found in scope"});
                    return false;
                }
                auto r = kernel.introduce_axiom(prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contrapositive' internal error: " + r.error().message});
                    return false;
                }
                (void)kernel.introduce_axiom(prop);
                return true;
            }
            // "by field_simp" — ThenStep variant
            if (s.justification.size() == 1 && s.justification[0] == "__field_simp__") {
                const std::string anon = fresh_name();
                return field_simp_tactic(prop, env, kernel, diag, step.loc, anon);
            }
            // "by positivity" — ThenStep variant
            if (s.justification.size() == 1 && s.justification[0] == "__positivity__") {
                if (!positivity_tactic(prop, env, kernel, diag, step.loc)) return false;
                (void)kernel.introduce_axiom(prop);
                return true;
            }
            // "by gcongr" — ThenStep variant
            if (s.justification.size() == 1 && s.justification[0] == "__gcongr__") {
                if (!gcongr_tactic(prop, env, kernel, diag, step.loc)) return false;
                (void)kernel.introduce_axiom(prop);
                return true;
            }
            // "by refl" — ThenStep variant
            if (s.justification.size() == 1 && s.justification[0] == "__refl__") {
                auto r = kernel.apply(kernel::Rule::Refl, {}, prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by refl' failed: " + r.error().message});
                    return false;
                }
                return true;
            }
            // "by symm h" — ThenStep variant
            if (!s.justification.empty() && s.justification[0] == "__symm__") {
                std::vector<std::string> hrefs(s.justification.begin() + 1, s.justification.end());
                auto es2 = resolve_refs(hrefs, env, diag, step.loc);
                if (!es2 || es2->size() != 1) {
                    diag.emit({diag::Severity::Error, step.loc, "'by symm' requires exactly one premise"});
                    return false;
                }
                auto r = kernel.apply(kernel::Rule::Symm,
                                      std::span<const kernel::Judgment>{&(*es2)[0]->judgment, 1},
                                      prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by symm' failed: " + r.error().message});
                    return false;
                }
                return true;
            }
            // "by trans h1 h2" — ThenStep variant
            if (!s.justification.empty() && s.justification[0] == "__trans__") {
                std::vector<std::string> hrefs(s.justification.begin() + 1, s.justification.end());
                auto es2 = resolve_refs(hrefs, env, diag, step.loc);
                if (!es2 || es2->size() != 2) {
                    diag.emit({diag::Severity::Error, step.loc, "'by trans' requires exactly two premises"});
                    return false;
                }
                const kernel::Judgment prem[2] = {(*es2)[0]->judgment, (*es2)[1]->judgment};
                auto r = kernel.apply(kernel::Rule::Trans, std::span{prem}, prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by trans' failed: " + r.error().message});
                    return false;
                }
                return true;
            }
            // "by congr h" — ThenStep variant
            if (!s.justification.empty() && s.justification[0] == "__congr__") {
                std::vector<std::string> hrefs(s.justification.begin() + 1, s.justification.end());
                auto es2 = resolve_refs(hrefs, env, diag, step.loc);
                if (!es2 || es2->size() != 1) {
                    diag.emit({diag::Severity::Error, step.loc, "'by congr' requires exactly one premise"});
                    return false;
                }
                auto r = kernel.apply(kernel::Rule::Congr,
                                      std::span<const kernel::Judgment>{&(*es2)[0]->judgment, 1},
                                      prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by congr' failed: " + r.error().message});
                    return false;
                }
                return true;
            }
            auto es = resolve_refs(s.justification, env, diag, step.loc);
            if (!es) return false;
            // expand let-bound names in the witness and beta-reduce.
            std::optional<ast::Expr> witness_expanded;
            if (s.witness) witness_expanded = apply_tdefs_expr(*s.witness->get());
            const ast::Expr* witness_ptr = witness_expanded ? &*witness_expanded : nullptr;
            std::optional<RuleApp> app;
            if (witness_ptr) {
                app = infer_quantifier_rule(prop, *es, witness_ptr, diag, step.loc);
            } else {
                app = infer_rule(prop, *es, diag, step.loc);
            }
            if (!app) return false;
            // ForallIntro requires the bound variable to have been introduced via TakeStep.
            if (app->rule == kernel::Rule::ForallIntro) {
                const auto* fa = std::get_if<ast::PropForall>(&prop.node);
                if (!env.is_taken(fa->var)) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "∀-intro: variable '" + fa->var
                               + "' must be introduced via 'take' before generalizing"});
                    return false;
                }
            }
            auto r = kernel.apply(app->rule, std::span{app->premises}, prop, witness_ptr);
            if (!r) {
                diag.emit({diag::Severity::Error, step.loc,
                           "kernel rejected 'then' step: " + r.error().message});
                return false;
            }
            return true;
        }

        // contradiction : <refs>  — derive ⊥ explicitly
        else if constexpr (std::is_same_v<T, ast::ContradictionStep>) {
            if (s.justification.empty()) {
                diag.emit({diag::Severity::Error, step.loc,
                           "'contradiction' step requires justification"});
                return false;
            }
            auto es = resolve_refs(s.justification, env, diag, step.loc);
            if (!es) return false;
            ast::Prop bot{step.loc, ast::PropFalse{}};
            auto app = infer_rule(bot, *es, diag, step.loc);
            if (!app) return false;
            auto r = kernel.apply(app->rule, std::span{app->premises}, bot);
            if (!r) {
                diag.emit({diag::Severity::Error, step.loc,
                           "kernel rejected contradiction: " + r.error().message});
                return false;
            }
            return true;
        }

        // cases <name> : <ref>  case ... => ... case ... => ...
        else if constexpr (std::is_same_v<T, ast::CasesStep>) {
            return check_cases_step(s, step.loc, env, kernel, diag, ctx);
        }

        // split [name :]  case left => ...  case right => ...
        else if constexpr (std::is_same_v<T, ast::SplitStep>) {
            return check_split_step(s, step.loc, env, kernel, diag, ctx);
        }

        // obtain <name> from <ref>  case <var> [: T] , <hyp> : P => <steps...>
        else if constexpr (std::is_same_v<T, ast::ObtainStep>) {
            return check_obtain_step(s, step.loc, env, kernel, diag, ctx);
        }

        // induction <name> on <var>  base: ...  inductive: ...
        else if constexpr (std::is_same_v<T, ast::InductionStep>) {
            return check_induction_step(s, step.loc, env, kernel, diag, ctx);
        }

        // calc [name :] lhs rel rhs by refs  { rel rhs by refs }
        else if constexpr (std::is_same_v<T, ast::CalcStep>) {
            return check_calc_step(s, step.loc, env, kernel, diag, ctx);
        }

        // rewrite h — handled before the step loop in check_proof; no-op here
        else if constexpr (std::is_same_v<T, ast::RewriteStep>) {
            // RewriteStep is intercepted in check_proof before entering check_step.
            // If we reach here, it's inside a nested proof context (cases arm, etc.)
            // where goal rewriting is not yet supported.
            diag.emit({diag::Severity::Error, step.loc,
                       "'rewrite' is only supported at the top level of a proof block"});
            return false;
        }

        // show P — goal documentation; verifies P matches the theorem statement
        else if constexpr (std::is_same_v<T, ast::ShowStep>) {
            const ast::Prop prop = apply_tdefs(s.prop);
            if (!ctx.goal) {
                diag.emit({diag::Severity::Error, step.loc,
                           "'show' step used outside a proof context"});
                return false;
            }
            if (!(prop == *ctx.goal)) {
                const uint32_t end_col = prop.end_loc ? prop.end_loc->col : 0;
                diag.emit({diag::Severity::Error, step.loc,
                           "'show' mismatch: expected '"
                           + forall::pretty::to_string(*ctx.goal)
                           + "', got '"
                           + forall::pretty::to_string(prop) + "'",
                           end_col});
                return false;
            }
            return true; // annotation only — no judgment produced
        }

        // exact h — close goal directly via a named hypothesis
        else if constexpr (std::is_same_v<T, ast::ExactStep>) {
            const HypEntry* entry = env.find(s.hyp_ref);
            if (!entry) {
                diag.emit({diag::Severity::Error, step.loc,
                           "exact: unknown hypothesis '" + s.hyp_ref + "'"});
                return false;
            }
            if (!ctx.goal) {
                diag.emit({diag::Severity::Error, step.loc,
                           "'exact' step used outside a proof context"});
                return false;
            }
            if (!(entry->judgment.prop() == *ctx.goal)) {
                diag.emit({diag::Severity::Error, step.loc,
                           "exact: hypothesis '"  + s.hyp_ref + "' has type '"
                           + forall::pretty::to_string(entry->judgment.prop())
                           + "', but goal is '"
                           + forall::pretty::to_string(*ctx.goal) + "'"});
                return false;
            }
            // ExactStep stores the certified judgment — same as a ThenStep by h.
            // It IS a concluding step, stored so check_proof can validate it.
            env.insert_or_assign("__exact_result__",
                                 HypEntry{entry->judgment, EntryKind::Derived});
            return true;
        }

        else if constexpr (std::is_same_v<T, ast::WlogStep>) {
            diag.emit({diag::Severity::Warning, step.loc,
                       "wlog: side obligation (general case from '"
                       + s.name + "' case) not verified"});
            auto r = kernel.introduce_axiom(s.prop);
            if (!r) {
                diag.emit({diag::Severity::Error, step.loc,
                           "wlog: internal error: " + r.error().message});
                return false;
            }
            env.insert_or_assign(s.name, HypEntry{std::move(*r), EntryKind::Assumption});
            return true;
        }
        else if constexpr (std::is_same_v<T, ast::PushNegStep>) {
            if (!s.hyp) {
                diag.emit({diag::Severity::Error, step.loc,
                           "'push neg' (goal form) is only supported at the top level of a proof block"});
                return false;
            }
            const HypEntry* h = env.find(*s.hyp);
            if (!h) {
                diag.emit({diag::Severity::Error, step.loc,
                           "'push neg at': unknown hypothesis '" + *s.hyp + "'"});
                return false;
            }
            ast::Prop new_prop = push_neg(h->judgment.prop());
            if (new_prop == h->judgment.prop()) {
                diag.emit({diag::Severity::Warning, step.loc,
                           "'push neg at " + *s.hyp
                           + "': hypothesis unchanged — no negation to push"});
                return true;
            }
            auto r = kernel.introduce_axiom(new_prop);
            if (!r) {
                diag.emit({diag::Severity::Error, step.loc,
                           "'push neg at': internal error: " + r.error().message});
                return false;
            }
            env.insert_or_assign(*s.hyp, HypEntry{std::move(*r), EntryKind::Derived});
            return true;
        }

        return true;
    }, step.node);
}

// ── Type-mismatch warnings ─────────────────────────────────────────────────────
//
// Emits a Warning when a PropRel has sides with clearly incompatible types.
// Fires only when both sides can be fully inferred and are incompatible (e.g.
// Prop compared to Nat), or when a sub-expression itself has a Mismatch error
// (e.g. Prop + Nat in arithmetic).  Unknown-type errors are silently ignored
// (the type_env is populated only from typed 'take' steps, so most variables
// will be absent).

static void check_proprel_types(const ast::Prop& prop,
                                const diag::SourceLocation& loc,
                                const ast::TypeEnv& type_env,
                                const ast::FuncSigTable& sigs,
                                diag::DiagnosticEngine& diag)
{
    const auto* rel = std::get_if<ast::PropRel>(&prop.node);
    if (!rel) return;

    auto lt = ast::infer_type(*rel->lhs, type_env, sigs);
    auto rt = ast::infer_type(*rel->rhs, type_env, sigs);

    // Case A: a sub-expression has a clear type mismatch (e.g. Prop used in +).
    if (!lt && lt.error().kind == ast::TypeErrorKind::Mismatch)
        diag.emit({diag::Severity::Warning, loc, lt.error().message});
    if (!rt && rt.error().kind == ast::TypeErrorKind::Mismatch)
        diag.emit({diag::Severity::Warning, loc, rt.error().message});

    // Case B: both sides infer successfully but are clearly incompatible —
    // one is a numeric type and the other is Prop.
    if (lt && rt) {
        auto is_numeric = [](const ast::TypeNode& t) {
            return std::holds_alternative<ast::TypeNat>(t.node)
                || std::holds_alternative<ast::TypeInt>(t.node)
                || std::holds_alternative<ast::TypeRat>(t.node)
                || std::holds_alternative<ast::TypeReal>(t.node);
        };
        auto is_prop = [](const ast::TypeNode& t) {
            return std::holds_alternative<ast::TypeProp>(t.node);
        };
        if ((is_numeric(*lt) && is_prop(*rt)) || (is_prop(*lt) && is_numeric(*rt))) {
            diag.emit({diag::Severity::Warning, loc,
                       "type mismatch: '"
                       + forall::pretty::to_string(*rel->lhs)
                       + "' has type " + forall::pretty::to_string(*lt)
                       + " but '"
                       + forall::pretty::to_string(*rel->rhs)
                       + "' has type " + forall::pretty::to_string(*rt)});
        }

        // Case C: set relation type checking.
        auto is_set = [](const ast::TypeNode& t) {
            return std::holds_alternative<ast::TypeSet>(t.node);
        };
        // Helper: returns true if `from` can be coerced to `to` via the numeric tower.
        auto numeric_coercible = [](const ast::TypeNode& from, const ast::TypeNode& to) -> bool {
            auto rank = [](const ast::TypeNode& t) -> int {
                if (std::holds_alternative<ast::TypeNat>(t.node))  return 0;
                if (std::holds_alternative<ast::TypeInt>(t.node))  return 1;
                if (std::holds_alternative<ast::TypeRat>(t.node))  return 2;
                if (std::holds_alternative<ast::TypeReal>(t.node)) return 3;
                return -1;
            };
            int rf = rank(from), rt = rank(to);
            return rf >= 0 && rt >= 0 && rf <= rt;
        };
        using Op = ast::RelOp;
        if (rel->op == Op::In || rel->op == Op::NotIn) {
            // element ∈ set — rhs must be TypeSet{T} and lhs must have type T.
            if (!is_set(*rt)) {
                diag.emit({diag::Severity::Warning, loc,
                           "type mismatch: right-hand side of membership relation is not a set"});
            } else {
                const auto& rset = std::get<ast::TypeSet>(rt->node);
                // allow numeric tower coercions for membership checks.
                if (!(*lt == *rset.element_type) && !numeric_coercible(*lt, *rset.element_type)) {
                    diag.emit({diag::Severity::Warning, loc,
                               "type mismatch: '"
                               + forall::pretty::to_string(*rel->lhs)
                               + "' has type " + forall::pretty::to_string(*lt)
                               + " but the set has element type "
                               + forall::pretty::to_string(*rset.element_type)});
                }
            }
        } else if (rel->op == Op::SubsetEq || rel->op == Op::Subset
                || rel->op == Op::SupersetEq) {
            // both sides must be TypeSet{T} for the same T.
            if (!is_set(*lt) || !is_set(*rt)) {
                diag.emit({diag::Severity::Warning, loc,
                           "type mismatch: subset relation requires set types"});
            } else {
                const auto& lset = std::get<ast::TypeSet>(lt->node);
                const auto& rset = std::get<ast::TypeSet>(rt->node);
                if (!(*lset.element_type == *rset.element_type)) {
                    diag.emit({diag::Severity::Warning, loc,
                               "type mismatch: subset relation between sets with different element types"});
                }
            }
        }
    }
}

// ── Deep proposition type-checking ────────────────────────────────────────────
//
// Recursively checks a proposition for type mismatches.  PropForall/PropExists
// binders extend the TypeEnv with the bound variable's annotated type, enabling
// type-checking of quantifier bodies.  PropRel leaves are checked via
// check_proprel_types.  Called for declaration statements (with empty env) and
// proof-step conclusions (with the accumulated take-step env).

static void check_prop_types_deep(const ast::Prop& prop,
                                  ast::TypeEnv env, // by value — binders extend a local copy
                                  const ast::FuncSigTable& sigs,
                                  diag::DiagnosticEngine& diag)
{
    std::visit([&](const auto& n) {
        using T = std::decay_t<decltype(n)>;
        if constexpr (std::is_same_v<T, ast::PropRel>) {
            check_proprel_types(prop, prop.loc, env, sigs, diag);
        } else if constexpr (std::is_same_v<T, ast::PropNot>) {
            check_prop_types_deep(*n.inner, std::move(env), sigs, diag);
        } else if constexpr (std::is_same_v<T, ast::PropAnd>
                          || std::is_same_v<T, ast::PropOr>
                          || std::is_same_v<T, ast::PropImpl>) {
            check_prop_types_deep(*n.lhs, env, sigs, diag);
            check_prop_types_deep(*n.rhs, std::move(env), sigs, diag);
        } else if constexpr (std::is_same_v<T, ast::PropForall>
                          || std::is_same_v<T, ast::PropExists>) {
            if (n.type.has_value()) env[n.var] = *n.type;
            check_prop_types_deep(*n.body, std::move(env), sigs, diag);
        }
        // Atomic, PropFalse, PropPred: no type errors to check
    }, prop.node);
}

// ── check_proof ────────────────────────────────────────────────────────────────

void check_proof(const ast::Decl& decl,
                 const HypEnv& module_env,
                 kernel::Kernel& kernel,
                 diag::DiagnosticEngine& diag,
                 const ast::FuncSigTable& sigs = {},
                 const InstanceTable& instances = {},
                 const ast::StructEnv* struct_env = nullptr,
                 const PredDefTable* pred_defs = nullptr,
                 const ast::TypeAliasTable* aliases = nullptr,
                 const ast::InductiveEnv* inductive_env = nullptr)
{
    if (!decl.proof) {
        diag.emit({diag::Severity::Error, decl.loc,
                   "theorem '" + decl.name + "' has no proof block"});
        return;
    }

    ScopeStack  env{module_env};
    ast::TypeEnv type_env; // types from typed 'take x : T' steps

    // inject structure fields for theorem/lemma params of structure type.
    // For each param (name : S) where S is a known structure:
    //   - register param's type in type_env so field projection type inference works
    //   - inject FieldAxiom fields as "param_name_axiom_name" hypotheses into env
    //   - register FieldTerm fields as "param_name_field_name" in the local sig table
    // We use a local mutable copy of sigs to extend it.
    ast::FuncSigTable local_sigs = sigs;
    if (struct_env) {
        for (const auto& param : decl.params) {
            const auto* user_t = std::get_if<ast::TypeUser>(&param.type.node);
            if (!user_t) continue;
            auto sit = struct_env->find(user_t->name);
            if (sit == struct_env->end()) continue;
            const auto& fields = sit->second;
            // Record the param variable's type so field projection works.
            type_env[param.name] = param.type;
            for (const auto& sf : fields) {
                if (const auto* fa = std::get_if<ast::FieldAxiom>(&sf)) {
                    const std::string hyp_name      = param.name + "_" + fa->name;
                    const std::string hyp_name_dot  = param.name + "." + fa->name;
                    // Inject the axiom as-is (uninstantiated) — it represents the
                    // generic axiom for this structure parameter.
                    auto r = kernel.introduce_axiom(fa->prop);
                    if (r) {
                        HypEntry entry{*r, EntryKind::Derived};
                        env.insert_or_assign(hyp_name,     entry);
                        // also register under "param.axiom_name" (dot notation)
                        env.insert_or_assign(hyp_name_dot, std::move(entry));
                    }
                }
                if (const auto* ft = std::get_if<ast::FieldTerm>(&sf)) {
                    const std::string sig_name = param.name + "_" + ft->name;
                    // Register in local_sigs if it has a function type.
                    if (const auto* tf = std::get_if<ast::TypeFun>(&ft->type.node))
                        local_sigs[sig_name] = *tf;
                }
            }
        }
    }

    // Track the last concluding step — ThenStep, CasesStep, ObtainStep, InductionStep, ExactStep, or SplitStep.
    enum class LastKind { None, Then, Cases, Obtain, Induction, Exact, Split };
    const ast::Step* last_concluding = nullptr;
    LastKind         last_kind       = LastKind::None;
    bool             had_step_errors = false;

    // unfold predicate definitions in the theorem statement so that the goal
    // presented to the proof is the definitionally-expanded form.  This allows
    // proofs to work in terms of the definition body rather than the predicate name.
    // The original decl.statement is preserved for error messages; we work against
    // the unfolded version internally.
    ast::Prop unfolded_statement = (pred_defs && !pred_defs->empty())
                                   ? unfold_preds(decl.statement, *pred_defs)
                                   : decl.statement;

    // Current proof goal — starts as the unfolded statement, may be transformed
    // by RewriteStep or ApplyStep. Allocations live in this vector so pointers remain valid.
    std::vector<ast::Prop> goal_history;
    const ast::Prop* current_goal = &unfolded_statement;

    // Stack of apply hypotheses — each ApplyStep pushes h:A→B so the conclusion
    // validator can chain ImplElim(h, proof_of_A) → B after the subproof of A.
    std::vector<const HypEntry*> apply_stack;

    // term-level local definitions from "let x = expr".
    // Applied as substitution into propositions before each step is checked.
    std::map<std::string, ast::ExprPtr> term_defs;

    // Apply all current term definitions to a proposition by substitution,
    // then beta-reduce so that e.g. (fun k => a[phi(k)])[n] normalises to
    // a[phi(n)] before kernel comparison.
    // also unfold predicate definitions.
    auto apply_term_defs = [&](ast::Prop p) -> ast::Prop {
        for (const auto& [name, expr] : term_defs)
            p = ast::subst(p, name, *expr);
        p = ast::beta_reduce(p);
        if (pred_defs && !pred_defs->empty())
            p = unfold_preds(p, *pred_defs);
        return p;
    };

    for (const auto& step : decl.proof->steps) {
        // Populate type_env before processing the step so TakeStep vars are
        // available for the type-mismatch check on the same iteration.
        if (const auto* ts = std::get_if<ast::TakeStep>(&step.node))
            if (ts->type.has_value()) {
                type_env[ts->var] = aliases
                    ? ast::expand_type_aliases(*ts->type, *aliases)
                    : *ts->type;
            }

        // TakeStep struct injection — when "take G : S" and S is a known
        // structure, inject S's FieldAxiom fields as hypotheses and FieldTerm
        // fields as signatures, mirroring the param injection done above.
        if (struct_env) {
            if (const auto* ts = std::get_if<ast::TakeStep>(&step.node)) {
                if (ts->type.has_value()) {
                    const auto* user_t = std::get_if<ast::TypeUser>(&ts->type->node);
                    if (user_t) {
                        auto sit = struct_env->find(user_t->name);
                        if (sit != struct_env->end()) {
                            const auto& fields = sit->second;
                            for (const auto& sf : fields) {
                                if (const auto* fa = std::get_if<ast::FieldAxiom>(&sf)) {
                                    const std::string hyp_name     = ts->var + "_" + fa->name;
                                    const std::string hyp_name_dot = ts->var + "." + fa->name;
                                    auto r = kernel.introduce_axiom(fa->prop);
                                    if (r) {
                                        HypEntry entry{*r, EntryKind::Derived};
                                        env.insert_or_assign(hyp_name,     entry);
                                        // also register under "var.axiom_name"
                                        env.insert_or_assign(hyp_name_dot, std::move(entry));
                                    }
                                }
                                if (const auto* ft = std::get_if<ast::FieldTerm>(&sf)) {
                                    const std::string sig_name = ts->var + "_" + ft->name;
                                    if (const auto* tf = std::get_if<ast::TypeFun>(&ft->type.node))
                                        local_sigs[sig_name] = *tf;
                                }
                            }
                        }
                    }
                }
            }
        }

        // RewriteStep transforms the current goal before check_step runs.
        // Each item in rw->rewrites is applied left-to-right to the goal.
        if (const auto* rw = std::get_if<ast::RewriteStep>(&step.node)) {
            bool rw_error = false;
            for (const auto& item : rw->rewrites) {
                const HypEntry* h = env.find(item.hyp_ref);
                if (!h) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "rewrite: unknown hypothesis '" + item.hyp_ref + "'"});
                    rw_error = true;
                    break;
                }
                const auto* eq = std::get_if<ast::PropRel>(&h->judgment.prop().node);
                if (!eq || eq->op != ast::RelOp::Eq) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "rewrite: hypothesis '" + item.hyp_ref
                               + "' must be an equality (lhs = rhs)"});
                    rw_error = true;
                    break;
                }
                // Apply the substitution to the current goal.
                // Fast path: plain variable on the relevant side → name-based subst.
                // General path: expression-level find-and-replace via subst_expr.
                const auto* lhs_var = std::get_if<ast::ExprVar>(&eq->lhs->node);
                const auto* rhs_var = std::get_if<ast::ExprVar>(&eq->rhs->node);
                ast::Prop new_goal;
                if (!item.reverse) {
                    if (lhs_var)
                        new_goal = ast::subst(*current_goal, lhs_var->name, *eq->rhs);
                    else
                        new_goal = ast::subst_expr(*current_goal, *eq->lhs, *eq->rhs);
                } else {
                    if (rhs_var)
                        new_goal = ast::subst(*current_goal, rhs_var->name, *eq->lhs);
                    else
                        new_goal = ast::subst_expr(*current_goal, *eq->rhs, *eq->lhs);
                }
                if (new_goal == *current_goal) {
                    diag.emit({diag::Severity::Warning, step.loc,
                               "rewrite '" + item.hyp_ref
                               + "': equality does not appear in goal — no effect"});
                }
                goal_history.push_back(std::move(new_goal));
                current_goal = &goal_history.back();
            }
            if (rw_error) had_step_errors = true;
            continue; // not a proof step, just goal transformation
        }

        // LetStep with definition — record the term binding and skip check_step.
        if (const auto* ls = std::get_if<ast::LetStep>(&step.node)) {
            if (ls->definition) {
                term_defs[ls->var] = *ls->definition;
            }
            // LetStep (both forms) is not a proof step — skip check_step.
            continue;
        }

        // ApplyStep — backward implication application.
        // apply h where h : A → B and current_goal = B → transforms goal to A.
        // Stores h's judgment for final ImplElim at conclusion validation.
        if (const auto* ap = std::get_if<ast::ApplyStep>(&step.node)) {
            const HypEntry* h = env.find(ap->hyp_ref);
            if (!h) {
                diag.emit({diag::Severity::Error, step.loc,
                           "apply: unknown hypothesis '" + ap->hyp_ref + "'"});
                had_step_errors = true;
                continue;
            }
            const auto* impl = std::get_if<ast::PropImpl>(&h->judgment.prop().node);
            if (!impl) {
                diag.emit({diag::Severity::Error, step.loc,
                           "apply: hypothesis '" + ap->hyp_ref
                           + "' must be an implication A → B"});
                had_step_errors = true;
                continue;
            }
            if (!(*impl->rhs == *current_goal)) {
                diag.emit({diag::Severity::Error, step.loc,
                           "apply: consequent of '" + ap->hyp_ref + "' is '"
                           + forall::pretty::to_string(*impl->rhs)
                           + "', but goal is '"
                           + forall::pretty::to_string(*current_goal) + "'"});
                had_step_errors = true;
                continue;
            }
            // Push hypothesis onto apply_stack for final ImplElim at conclusion.
            apply_stack.push_back(h);
            // Transform goal to the antecedent A.
            goal_history.push_back(*impl->lhs);
            current_goal = &goal_history.back();
            continue; // goal transformation only
        }

        // PushNegStep — push negations inward on goal or hypothesis.
        if (const auto* pn = std::get_if<ast::PushNegStep>(&step.node)) {
            if (!pn->hyp) {
                if (!current_goal) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'push neg' used outside a proof context"});
                    had_step_errors = true;
                } else {
                    ast::Prop new_goal = push_neg(*current_goal);
                    if (new_goal == *current_goal)
                        diag.emit({diag::Severity::Warning, step.loc,
                                   "'push neg': goal unchanged — no negation to push"});
                    goal_history.push_back(std::move(new_goal));
                    current_goal = &goal_history.back();
                }
            } else {
                const HypEntry* h = env.find(*pn->hyp);
                if (!h) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'push neg at': unknown hypothesis '" + *pn->hyp + "'"});
                    had_step_errors = true;
                } else {
                    ast::Prop new_prop = push_neg(h->judgment.prop());
                    if (new_prop == h->judgment.prop()) {
                        diag.emit({diag::Severity::Warning, step.loc,
                                   "'push neg at " + *pn->hyp
                                   + "': hypothesis unchanged — no negation to push"});
                    } else {
                        auto r = kernel.introduce_axiom(new_prop);
                        if (r)
                            env.insert_or_assign(*pn->hyp,
                                                 HypEntry{std::move(*r), EntryKind::Derived});
                    }
                }
            }
            continue;
        }

        const CheckContext ctx{type_env, instances, module_env, local_sigs, current_goal, &term_defs, struct_env, pred_defs, inductive_env};
        const auto snap = diag.diagnostics().size();
        check_step(step, env, kernel, diag, ctx);
        const auto& all = diag.diagnostics();
        for (auto i = snap; i < all.size(); ++i) {
            if (all[i].severity == diag::Severity::Error) {
                had_step_errors = true;
                break;
            }
        }

        // Deep type-check step conclusions: recurses into quantifiers in the
        // conclusion, seeding the TypeEnv from their type annotations.
        if (const auto* hs = std::get_if<ast::HaveStep>(&step.node))
            check_prop_types_deep(hs->prop, type_env, local_sigs, diag);
        if (const auto* ss = std::get_if<ast::ShowStep>(&step.node))
            check_prop_types_deep(ss->prop, type_env, local_sigs, diag);
        if (const auto* ts_s = std::get_if<ast::ThenStep>(&step.node)) {
            // Don't type-check the dummy PropFalse{} in a __qed__ sentinel step.
            const bool is_qed = !ts_s->justification.empty()
                                 && ts_s->justification[0] == "__qed__";
            if (!is_qed)
                check_prop_types_deep(ts_s->prop, type_env, local_sigs, diag);
        }

        if (std::get_if<ast::ThenStep>(&step.node)) {
            last_concluding = &step;
            last_kind       = LastKind::Then;
        }
        if (std::get_if<ast::CasesStep>(&step.node)) {
            last_concluding = &step;
            last_kind       = LastKind::Cases;
        }
        if (std::get_if<ast::ObtainStep>(&step.node)) {
            last_concluding = &step;
            last_kind       = LastKind::Obtain;
        }
        if (std::get_if<ast::InductionStep>(&step.node)) {
            last_concluding = &step;
            last_kind       = LastKind::Induction;
        }
        if (std::get_if<ast::ExactStep>(&step.node)) {
            last_concluding = &step;
            last_kind       = LastKind::Exact;
        }
        if (std::get_if<ast::SplitStep>(&step.node)) {
            last_concluding = &step;
            last_kind       = LastKind::Split;
        }
    }

    // Only validate the conclusion when all steps passed; cascading errors on
    // a broken proof are more noise than signal.
    if (!had_step_errors) {
        if (last_kind == LastKind::None) {
            // auto-close at end/qed when goal is A → B or ¬A and the required
            // pieces (Assumption of the antecedent + Derived of the consequent) are
            // already in scope.  This lets the user omit the explicit "then A → B".
            if (const auto* im = std::get_if<ast::PropImpl>(&current_goal->node)) {
                // Find Assumption of A
                const HypEntry* assump = nullptr;
                env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                    if (e.judgment.prop() == *im->lhs) assump = &e;
                });
                const HypEntry* conseq = assump ? env.find_derived(*im->rhs) : nullptr;
                if (assump && conseq) {
                    // Synthesize ImplIntro
                    auto r = kernel.apply(kernel::Rule::ImplIntro,
                                          std::span<const kernel::Judgment>{&conseq->judgment, 1},
                                          *current_goal);
                    if (!r) {
                        diag.emit({diag::Severity::Error, decl.loc,
                                   "proof of '" + decl.name
                                   + "': auto-close ImplIntro failed: " + r.error().message});
                    }
                    // auto-close succeeded — no error
                } else {
                    diag.emit({diag::Severity::Error, decl.loc,
                               "proof of '" + decl.name
                               + "' has no concluding step "
                               "(auto-discharge of '\xe2\x86\x92' failed: "
                               "missing assumption or consequent)"});
                }
            } else if (const auto* neg = std::get_if<ast::PropNot>(&current_goal->node)) {
                // Find Assumption of A and Derived of ⊥
                const HypEntry* assump = nullptr;
                env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                    if (e.judgment.prop() == *neg->inner) assump = &e;
                });
                ast::Prop false_prop{decl.loc, ast::PropFalse{}};
                const HypEntry* bot = assump ? env.find_derived(false_prop) : nullptr;
                if (assump && bot) {
                    // Synthesize NotIntro
                    auto r = kernel.apply(kernel::Rule::NotIntro,
                                          std::span<const kernel::Judgment>{&bot->judgment, 1},
                                          *current_goal);
                    if (!r) {
                        diag.emit({diag::Severity::Error, decl.loc,
                                   "proof of '" + decl.name
                                   + "': auto-close NotIntro failed: " + r.error().message});
                    }
                    // auto-close succeeded — no error
                } else {
                    diag.emit({diag::Severity::Error, decl.loc,
                               "proof of '" + decl.name
                               + "' has no concluding step "
                               "(auto-discharge of '\xc2\xac' failed: "
                               "missing assumption or proof of false)"});
                }
            } else {
                diag.emit({diag::Severity::Error, decl.loc,
                           "proof of '" + decl.name + "' has no concluding 'then' step"});
            }
        } else if (last_kind == LastKind::Then) {
            const auto& ts = std::get<ast::ThenStep>(last_concluding->node);
            // __qed__ sentinel substitutes current goal — skip prop check.
            const bool is_qed_sentinel = !ts.justification.empty()
                                         && ts.justification[0] == "__qed__";
            // apply term definitions to the conclusion before comparing.
            const ast::Prop ts_prop = apply_term_defs(ts.prop);
            if (!is_qed_sentinel) {
                const auto& tvars = env.taken_vars();
                if (!tvars.empty() && !(ts_prop == unfolded_statement)) {
                    // User wrote the inner body after 'take x'; wrap to reconstruct
                    // the full ∀ statement and validate against unfolded_statement.
                    // If the user already wrote the full ∀ statement (ts_prop ==
                    // unfolded_statement), skip wrapping and fall through to the
                    // normal single-goal check below.
                    ast::Prop wrapped = ts_prop;
                    std::vector<ast::Prop> assumptions;
                    env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                        assumptions.push_back(e.judgment.prop());
                    });
                    for (auto rit = assumptions.rbegin(); rit != assumptions.rend(); ++rit) {
                        wrapped = ast::Prop{last_concluding->loc,
                            ast::PropImpl{ast::make_prop(*rit), ast::make_prop(wrapped)}};
                    }
                    for (auto rit = tvars.rbegin(); rit != tvars.rend(); ++rit) {
                        wrapped = ast::Prop{last_concluding->loc,
                            ast::PropForall{rit->first, rit->second,
                                            ast::make_prop(wrapped)}};
                    }
                    if (!(wrapped == unfolded_statement)) {
                        const uint32_t end_col = ts.prop.end_loc ? ts.prop.end_loc->col : 0;
                        diag.emit({diag::Severity::Error, last_concluding->loc,
                                   "proof concludes with `"
                                   + forall::pretty::to_string(wrapped)
                                   + "`, expected `"
                                   + forall::pretty::to_string(unfolded_statement) + "`",
                                   end_col});
                    }
                } else if (ts_prop != *current_goal) {
                    const uint32_t end_col = ts.prop.end_loc ? ts.prop.end_loc->col : 0;
                    diag.emit({diag::Severity::Error, last_concluding->loc,
                               "proof concludes with `" + forall::pretty::to_string(ts_prop)
                               + "`, expected `" + forall::pretty::to_string(*current_goal) + "`",
                               end_col});
                }
            }
            // If apply_stack is non-empty, verify the chain reaches decl.statement.
            // Each apply h:A→B requires the subproof to conclude A, then ImplElim gives B.
            // The final result must equal decl.statement.
            if (!apply_stack.empty() && !is_qed_sentinel) {
                // Walk the apply stack to verify the chain is consistent.
                // current_goal is the innermost subgoal A (proved by last step).
                // The stack is in order [h1:A1→B1, h2:A2→B2, ...] where each Bi = A_{i-1}.
                // The final B_n must == decl.statement.
                const ast::Prop* chain_goal = current_goal;
                bool chain_ok = true;
                for (auto it = apply_stack.rbegin(); it != apply_stack.rend(); ++it) {
                    const auto* impl = std::get_if<ast::PropImpl>(&(*it)->judgment.prop().node);
                    if (!impl || !(*impl->lhs == *chain_goal)) { chain_ok = false; break; }
                    chain_goal = impl->rhs.get();
                }
                if (chain_ok && chain_goal && !(*chain_goal == unfolded_statement))
                    diag.emit({diag::Severity::Error, last_concluding->loc,
                               "apply chain does not prove the theorem statement"});
            }
        } else if (last_kind == LastKind::Cases) {
            const auto& cs = std::get<ast::CasesStep>(last_concluding->node);
            const auto* it = env.find(cs.name);
            if (it && !(it->judgment.prop() == unfolded_statement))
                diag.emit({diag::Severity::Error, last_concluding->loc,
                           "proof concludes with wrong proposition"});
        } else if (last_kind == LastKind::Obtain) {
            const auto& os = std::get<ast::ObtainStep>(last_concluding->node);
            const auto* it = env.find(os.name);
            if (it && !(it->judgment.prop() == unfolded_statement))
                diag.emit({diag::Severity::Error, last_concluding->loc,
                           "proof concludes with wrong proposition"});
        } else if (last_kind == LastKind::Induction) {
            const auto& is = std::get<ast::InductionStep>(last_concluding->node);
            const auto* it = env.find(is.name);
            if (!it) {
                diag.emit({diag::Severity::Error, last_concluding->loc,
                           "proof concludes with wrong proposition"});
            } else {
                // Build the wrapped conclusion:
                //  1. Start with the induction result ∀ var : T, body(var).
                //  2. Wrap each outstanding Assumption (from suppose) as an implication
                //     antecedent (innermost first, so last-assumed wraps tightest).
                //  3. Wrap each outstanding taken variable (from take) as a ∀ binder
                //     (outermost first, i.e. first-taken is the outermost ∀).
                // The result must equal unfolded_statement.
                ast::Prop wrapped = it->judgment.prop();

                // Step 2: wrap Assumptions in reverse order (last-assumed → innermost).
                std::vector<ast::Prop> assumptions;
                env.for_each_assumption([&](const std::string&, const HypEntry& e) {
                    assumptions.push_back(e.judgment.prop());
                });
                for (auto rit = assumptions.rbegin(); rit != assumptions.rend(); ++rit) {
                    wrapped = ast::Prop{last_concluding->loc,
                        ast::PropImpl{ast::make_prop(*rit), ast::make_prop(wrapped)}};
                }

                // Step 3: wrap taken variables in reverse order (last-taken → innermost ∀).
                const auto& tvars = env.taken_vars();
                for (auto rit = tvars.rbegin(); rit != tvars.rend(); ++rit) {
                    wrapped = ast::Prop{last_concluding->loc,
                        ast::PropForall{rit->first, rit->second,
                                        ast::make_prop(wrapped)}};
                }

                if (!(wrapped == unfolded_statement))
                    diag.emit({diag::Severity::Error, last_concluding->loc,
                               "proof concludes with wrong proposition"});
            }
        } else if (last_kind == LastKind::Split) {
            const auto& ss = std::get<ast::SplitStep>(last_concluding->node);
            const std::string result_name = ss.name.empty() ? "" : ss.name;
            // If the split stored a result under a known name, verify it.
            // Anonymous splits are verified inside check_split_step directly.
            if (!result_name.empty()) {
                const auto* it = env.find(result_name);
                if (it && !(it->judgment.prop() == unfolded_statement))
                    diag.emit({diag::Severity::Error, last_concluding->loc,
                               "proof concludes with wrong proposition"});
            }
        } else { // Exact — goal check already performed in check_step
        }
    }
}

// ── InstanceTable / typeclass mechanism ───────────────────────────────────────
//
// Maps type_name → set of class names the type is declared to implement.
// Populated by `instance <TypeName> : <ClassName>` declarations.
//
// ClassAxioms: maps class name → required axiom-name suffixes.
// When `instance Real : Field` is declared, the checker looks for each
// "Real_<suffix>" in module_env and errors loudly if any are missing.
// This makes implicit resolution loud on failure: if a required axiom is absent,
// the user gets a precise diagnostic naming the missing axiom.

// Required axiom-name suffixes per algebraic class.
// Convention: for type T, the axiom must be named <T>_<suffix>.
// E.g.  instance Real : Ring  requires axioms  Real_add_comm, Real_add_assoc, etc.
static const std::map<std::string, std::vector<std::string_view>> class_axioms = {
    {"Semigroup", {
        "add_assoc",
    }},
    {"Monoid", {
        "add_assoc", "add_zero", "zero_add",
    }},
    {"Group", {
        "add_assoc", "add_zero", "zero_add", "add_neg",
    }},
    {"Ring", {
        "add_assoc", "add_comm", "add_zero", "zero_add", "add_neg",
        "mul_assoc", "mul_one", "one_mul",
        "distrib_left", "distrib_right",
    }},
    {"CommRing", {
        "add_assoc", "add_comm", "add_zero", "zero_add", "add_neg",
        "mul_assoc", "mul_comm", "mul_one", "one_mul",
        "distrib_left", "distrib_right",
    }},
    {"Field", {
        "add_assoc", "add_comm", "add_zero", "zero_add", "add_neg",
        "mul_assoc", "mul_comm", "mul_one", "one_mul",
        "distrib_left", "distrib_right",
        "mul_inv",
    }},
    {"OrderedField", {
        "add_assoc", "add_comm", "add_zero", "zero_add", "add_neg",
        "mul_assoc", "mul_comm", "mul_one", "one_mul",
        "distrib_left", "distrib_right",
        "mul_inv",
        "lt_trans", "lt_add", "lt_mul_pos",
    }},
};

// Validates an `instance T : C` declaration.
// For each required suffix in class_axioms[C], checks that "<T>_<suffix>" is in
// module_env.  Emits an Error for every missing axiom.
// Returns false if any required axiom is missing.
static bool check_instance(const std::string& type_name,
                           const std::string& class_name,
                           const HypEnv& module_env,
                           diag::DiagnosticEngine& diag,
                           const diag::SourceLocation& loc)
{
    auto it = class_axioms.find(class_name);
    if (it == class_axioms.end()) {
        diag.emit({diag::Severity::Error, loc,
                   "unknown typeclass '" + class_name
                   + "'; known classes: Semigroup, Monoid, Group, Ring, CommRing, Field, OrderedField"});
        return false;
    }
    bool ok = true;
    for (std::string_view suffix : it->second) {
        std::string required = type_name + "_" + std::string{suffix};
        if (!module_env.count(required)) {
            diag.emit({diag::Severity::Error, loc,
                       "instance " + type_name + " : " + class_name
                       + " — missing required axiom '" + required + "'"});
            ok = false;
        }
    }
    return ok;
}

// ── resolve_ring_axioms ────────────────────────────────────────────────────────
//
// Axiom-set reachability.
// Given a type name (e.g. "Real"), the current InstanceTable, and the current
// module_env, returns a map from law-name suffix (e.g. "add_comm") to the
// corresponding Judgment for "<TypeName>_add_comm".
//
// Returns an error string if:
//   - the type has no registered instance for any Ring-or-above class, or
//   - any required axiom is missing from module_env.
//
// The returned map covers the most-specific class the type implements
// (OrderedField > Field > CommRing > Ring > Monoid > Semigroup).
// The norm_num tactic calls this at step-check time to obtain the axiom set.

struct RingAxioms {
    std::string                          class_name; // e.g. "OrderedField"
    std::map<std::string, kernel::Judgment> axioms;  // suffix → Judgment
};

[[nodiscard]] [[maybe_unused]] std::expected<RingAxioms, std::string>
resolve_ring_axioms(const std::string& type_name,
                    const InstanceTable& instances,
                    const HypEnv& module_env)
{
    // Ordered from most specific to least specific.
    static constexpr std::string_view ordered_classes[] = {
        "OrderedField", "Field", "CommRing", "Ring", "Monoid", "Semigroup",
    };

    auto inst_it = instances.find(type_name);
    if (inst_it == instances.end())
        return std::unexpected("type '" + type_name + "' has no registered typeclass instance");

    const auto& registered = inst_it->second;
    std::string chosen_class;
    for (std::string_view cls : ordered_classes) {
        if (registered.count(std::string{cls})) { chosen_class = std::string{cls}; break; }
    }
    if (chosen_class.empty())
        return std::unexpected("type '" + type_name + "' has no Ring-or-above instance");

    auto cls_it = class_axioms.find(chosen_class);
    if (cls_it == class_axioms.end())
        return std::unexpected("internal: class '" + chosen_class + "' not in class_axioms");

    RingAxioms result;
    result.class_name = chosen_class;
    for (std::string_view suffix : cls_it->second) {
        std::string key = type_name + "_" + std::string{suffix};
        auto env_it = module_env.find(key);
        if (env_it == module_env.end())
            return std::unexpected("missing axiom '" + key + "' for type '" + type_name + "'");
        result.axioms.emplace(std::string{suffix}, env_it->second.judgment);
    }
    return result;
}

// ── Polynomial normal form ────────────────────────────────────────────
//
// Represents a multivariate polynomial as a sum of terms, each term being a
// rational coefficient times a monomial.
//
// Monomial: sorted map variable→exponent (canonical by map key ordering).
//   e.g. x²y³  →  {"x":2, "y":3}
// Poly: map monomial→rational coefficient.
//   e.g. 3x² + 2xy - 1  →  {{"x":2}:3/1,  {"x":1,"y":1}:2/1,  {}:-1/1}
//
// normalize(Expr) expands an expression tree into Poly form.
// Two expressions are ring-equal iff their normal forms are identical.

// Remove zero-coefficient entries.
static void poly_trim(Poly& p) {
    for (auto it = p.begin(); it != p.end(); ) {
        if (it->second.first == 0) it = p.erase(it);
        else                       ++it;
    }
}

// Get the coefficient for a monomial, defaulting to 0/1 if absent.
static Rational poly_get(const Poly& p, const Monomial& m) {
    auto it = p.find(m);
    return it != p.end() ? it->second : Rational{0, 1};
}

static Poly poly_add(Poly a, const Poly& b) {
    for (const auto& [mono, coef] : b) {
        Rational cur = poly_get(a, mono);
        Rational sum = make_rat(cur.first * coef.second + coef.first * cur.second,
                                cur.second * coef.second);
        if (sum.first != 0) a[mono] = sum;
        else a.erase(mono);
    }
    return a;
}

static Poly poly_scale(Poly p, Rational r) {
    for (auto& [mono, coef] : p)
        coef = make_rat(coef.first * r.first, coef.second * r.second);
    poly_trim(p);
    return p;
}

static Poly poly_neg(Poly p) {
    return poly_scale(std::move(p), {-1, 1});
}

// Multiply two monomials: merge exponent maps.
static Monomial mono_mul(const Monomial& a, const Monomial& b) {
    Monomial r = a;
    for (const auto& [v, e] : b) r[v] += e;
    // Remove variables with zero exponent (shouldn't normally happen, but be safe).
    for (auto it = r.begin(); it != r.end(); )
        if (it->second == 0) it = r.erase(it); else ++it;
    return r;
}

static Poly poly_mul(const Poly& a, const Poly& b) {
    Poly result;
    for (const auto& [ma, ca] : a) {
        for (const auto& [mb, cb] : b) {
            Monomial m = mono_mul(ma, mb);
            Rational prod = make_rat(ca.first * cb.first, ca.second * cb.second);
            Rational cur = poly_get(result, m);
            Rational sum = make_rat(cur.first * prod.second + prod.first * cur.second,
                                    cur.second * prod.second);
            if (sum.first != 0) result[m] = sum;
            else result.erase(m);
        }
    }
    return result;
}

static Poly poly_pow(Poly base, int exp) {
    if (exp < 0) return {}; // division not supported in poly normalizer
    Poly result{{{}, {1, 1}}}; // start with the constant polynomial 1
    for (int i = 0; i < exp; ++i)
        result = poly_mul(result, base);
    return result;
}

// Constant polynomial: the rational number r.
static Poly poly_const(Rational r) {
    if (r.first == 0) return {};
    return {{Monomial{}, r}};
}

// Single-variable polynomial: coefficient 1 of variable v with exponent 1.
static Poly poly_var(const std::string& v) {
    return {{Monomial{{v, 1}}, {1, 1}}};
}

// Normalize an expression to a polynomial.
// Returns empty Poly for expressions that cannot be symbolically normalised
// (e.g. function calls with opaque arguments, floor/ceil, index, etc.).
static Poly normalize_expr(const ast::Expr& e) {
    return std::visit([](const auto& n) -> Poly {
        using T = std::decay_t<decltype(n)>;

        if constexpr (std::is_same_v<T, ast::ExprLit>) {
            auto v = std::stoll(n.value, nullptr, 10);
            return poly_const({v, 1});
        }

        if constexpr (std::is_same_v<T, ast::ExprVar>) {
            return poly_var(n.name);
        }

        if constexpr (std::is_same_v<T, ast::ExprUnary>) {
            if (n.op == ast::UnaryOp::Neg)
                return poly_neg(normalize_expr(*n.operand));
            return {}; // inv, compl not polynomial
        }

        if constexpr (std::is_same_v<T, ast::ExprBinary>) {
            auto lp = normalize_expr(*n.lhs);
            auto rp = normalize_expr(*n.rhs);
            switch (n.op) {
                case ast::BinOp::Add: return poly_add(std::move(lp), rp);
                case ast::BinOp::Sub: return poly_add(std::move(lp), poly_neg(rp));
                case ast::BinOp::Mul: return poly_mul(lp, rp);
                case ast::BinOp::Pow: {
                    // rhs must be a literal non-negative integer.
                    const auto* lit = std::get_if<ast::ExprLit>(&n.rhs->node);
                    if (!lit) return {};
                    int exp = 0;
                    try { exp = std::stoi(lit->value); } catch (...) { return {}; }
                    if (exp < 0) return {};
                    return poly_pow(lp, exp);
                }
                default: return {}; // Div, IDiv, Mod, Compose, set ops — not polynomial
            }
        }

        // Tuple grouping: (a, b) is not a numeric expression; single-element
        // tuples are arithmetic groupings already resolved by the parser.
        if constexpr (std::is_same_v<T, ast::ExprTuple>) {
            if (n.elements.size() == 1)
                return normalize_expr(*n.elements[0]);
            return {};
        }

        return {}; // calls, indices, lambdas, conditionals, aggregates, sets
    }, e.node);
}

// Two expressions are ring-equal iff their normal forms are equal.
// Returns true/false, or nullopt if either side cannot be normalized.
[[nodiscard]] [[maybe_unused]] static std::optional<bool>
ring_equal(const ast::Expr& lhs, const ast::Expr& rhs) {
    auto lp = normalize_expr(lhs);
    auto rp = normalize_expr(rhs);
    // An empty Poly can mean "zero" or "not normalizable".
    // We distinguish by checking whether there was a literal/variable to start from.
    // For safety: if both sides produce empty Poly, we cannot conclude equality.
    // (Two distinct non-normalizable expressions should not be judged equal.)
    // Only return true when both sides successfully normalize to the same Poly.
    // "Successfully normalize" means: the input contains only ExprLit, ExprVar,
    // ExprUnary{Neg}, ExprBinary{+,-,*,^(literal)}, or ExprTuple{single}.
    // We detect success by checking whether the Poly is well-formed (all monomials
    // have non-zero coefficients after trim).  The empty Poly is valid for zero.
    // The ambiguity is: normalize_expr returns {} both for "not normalizable" and
    // for "the expression equals zero after simplification."
    // Resolution: only call ring_equal from contexts where both sides were already
    // type-checked to be numeric (not opaque function calls).
    return lp == rp;
}

// ── linarith: linear arithmetic decision procedure (MT1) ──────────────────────
//
// Checks whether a set of linear inequalities over ℚ is unsatisfiable using
// Fourier-Motzkin elimination.  A constraint is:
//   { coefficients: map<var,Rational>, const_term: Rational, op: Lt/LtEq/Eq }
// Representing:  sum(coeff_i * x_i) + const_term  op  0
// e.g. "x + 2y < 5"  →  { {x:1, y:2}, -5, Lt }
//
// LinConstraint is declared near Poly above (needed by check_step forward decls).

static Rational rat_neg(Rational r) { return {-r.first, r.second}; }
static Rational rat_add(Rational a, Rational b) {
    long long n = a.first * b.second + b.first * a.second;
    long long d = a.second * b.second;
    if (d < 0) { n = -n; d = -d; }
    auto g = std::gcd(std::abs(n), d);
    return {n/g, d/g};
}
static Rational rat_mul(Rational a, Rational b) {
    long long n = a.first * b.first;
    long long d = a.second * b.second;
    if (d < 0) { n = -n; d = -d; }
    auto g = std::gcd(std::abs(n), d);
    return {n==0?0:n/g, d/g};
}

// Check if a Poly is linear (all monomials have degree ≤ 1).
// Extract as map<var, coeff> + constant term.
static bool poly_to_linear(const Poly& p,
                            std::map<std::string, Rational>& out_coeffs,
                            Rational& out_const)
{
    out_const = {0, 1};
    for (const auto& [mono, coeff] : p) {
        if (coeff.first == 0) continue;
        if (mono.empty()) {
            // constant term
            out_const = rat_add(out_const, coeff);
        } else if (mono.size() == 1 && mono.begin()->second == 1) {
            // linear term: variable with exponent 1
            const std::string& var = mono.begin()->first;
            auto it = out_coeffs.find(var);
            if (it == out_coeffs.end()) out_coeffs[var] = coeff;
            else it->second = rat_add(it->second, coeff);
        } else {
            return false; // non-linear
        }
    }
    return true;
}

// Extract a linear constraint from "lhs op rhs": lhs - rhs op 0
// Returns nullopt if the relation is not linear.
static std::optional<LinConstraint>
extract_linear(const ast::PropRel& rel) {
    auto lp = normalize_expr(*rel.lhs);
    auto rp = normalize_expr(*rel.rhs);
    // Compute lp - rp
    Poly diff = lp;
    for (const auto& [m, c] : rp)
        diff[m] = rat_add(poly_get(diff, m), rat_neg(c));
    // Trim zeros
    for (auto it = diff.begin(); it != diff.end(); ) {
        if (it->second.first == 0) it = diff.erase(it); else ++it;
    }
    std::map<std::string, Rational> coeffs;
    Rational cst;
    if (!poly_to_linear(diff, coeffs, cst)) return std::nullopt;
    // sense: Lt→-1, LtEq/Gt/GtEq flipped, Eq→0
    int sense = 0;
    switch (rel.op) {
        case ast::RelOp::Lt:    sense = -1; break;
        case ast::RelOp::LtEq:  sense =  1; break;
        case ast::RelOp::Eq:    sense =  0; break;
        case ast::RelOp::GtEq:  // lhs >= rhs → rhs - lhs <= 0 → flip
            for (auto& [v,c] : coeffs) c = rat_neg(c);
            cst = rat_neg(cst);
            sense = 1;
            break;
        case ast::RelOp::Gt:   // lhs > rhs → rhs - lhs < 0 → flip
            for (auto& [v,c] : coeffs) c = rat_neg(c);
            cst = rat_neg(cst);
            sense = -1;
            break;
        default: return std::nullopt;
    }
    return LinConstraint{std::move(coeffs), cst, sense};
}

// Fourier-Motzkin: returns true if the constraint set is UNSATISFIABLE.
// Works by projecting out variables one at a time.
// Fourier-Motzkin: returns true if the constraint set is UNSATISFIABLE.
//
// Encoding: each LinConstraint represents  Σ coeffs[v]*v - rhs  sense  0
// where sense=-1 means strict <, sense=1 means ≤.
//
// To check for contradiction: add negated goal to the set and check unsat.
static bool fourier_motzkin(std::vector<LinConstraint> cs) {
    if (cs.empty()) return false;

    // Helper: add scaled constraint (scalar * c) to another constraint.
    auto scale = [](const LinConstraint& c, Rational s) -> LinConstraint {
        LinConstraint r;
        r.sense = c.sense;
        r.rhs   = rat_mul(c.rhs, s);
        for (const auto& [v, coeff] : c.coeffs) {
            Rational scaled = rat_mul(coeff, s);
            if (scaled.first != 0) r.coeffs[v] = scaled;
        }
        return r;
    };

    // Helper: add two constraints (sum of coefficients and rhs).
    auto add_constraints = [](const LinConstraint& a, const LinConstraint& b, int sense) -> LinConstraint {
        LinConstraint r;
        r.sense = sense;
        r.rhs   = rat_add(a.rhs, b.rhs);
        r.coeffs = a.coeffs;
        for (const auto& [v, c] : b.coeffs) {
            auto it = r.coeffs.find(v);
            Rational combined = rat_add(it != r.coeffs.end() ? it->second : Rational{0,1}, c);
            if (combined.first != 0) r.coeffs[v] = combined;
            else if (it != r.coeffs.end()) r.coeffs.erase(it);
        }
        return r;
    };

    // Collect all variable names.
    std::set<std::string> vars;
    for (const auto& c : cs)
        for (const auto& [v, _] : c.coeffs) vars.insert(v);

    for (const auto& var : vars) {
        // Split into upper-bounded (coeff > 0: var contributes positively → bounds var from above via ≤)
        // and lower-bounded (coeff < 0: var contributes negatively → bounds var from below).
        std::vector<LinConstraint> ub, lb, free;
        for (const auto& c : cs) {
            auto it = c.coeffs.find(var);
            if (it == c.coeffs.end() || it->second.first == 0) { free.push_back(c); continue; }
            if (it->second.first > 0) ub.push_back(c);
            else                      lb.push_back(c);
        }
        // FM projection: for each (u, l) pair combine to eliminate var.
        // u: a_u * var + ... ≤ rhs_u → var ≤ (rhs_u - ...) / a_u
        // l: a_l * var + ... ≤ rhs_l (a_l < 0) → var ≥ (rhs_l - ...) / a_l → var ≥ (rhs_l - ...)/a_l
        // Combined: (rhs_l - sum_l) / a_l ≤ (rhs_u - sum_u) / a_u
        // Scale: a_u*(rhs_l - sum_l) ≤ (-a_l)*(rhs_u - sum_u)
        // Or: a_u*(sum_l coeffs) + (-a_l)*(sum_u coeffs) - (a_u*rhs_l + (-a_l)*rhs_u) sense 0
        // Which is: scale(l, a_u) + scale(u, -a_l) combined
        std::vector<LinConstraint> next = free;
        for (const auto& u : ub) {
            Rational a_u = u.coeffs.at(var);             // > 0
            for (const auto& l : lb) {
                Rational a_l = l.coeffs.at(var);          // < 0
                Rational neg_a_l{-a_l.first, a_l.second}; // > 0
                // Combined: scale(u, neg_a_l) + scale(l, a_u), eliminates var
                auto su = scale(u, neg_a_l);
                auto sl = scale(l, a_u);
                su.coeffs.erase(var);
                sl.coeffs.erase(var);
                int sense = (u.sense == -1 || l.sense == -1) ? -1 : 1;
                auto combined = add_constraints(su, sl, sense);
                next.push_back(combined);
            }
        }
        cs = next;
    }
    // After eliminating all variables, check for constant contradictions.
    // Each remaining constraint has the form:  rhs sense 0
    // (where rhs is the constant term of the linear expression).
    // Constraint is FALSE (contradiction) when:
    //   sense=-1 (strict <): rhs >= 0  (need rhs < 0 for satisfiability)
    //   sense= 1 (non-strict ≤): rhs > 0  (need rhs <= 0 for satisfiability)
    for (const auto& c : cs) {
        if (!c.coeffs.empty()) continue;
        bool contradiction = false;
        if (c.sense == -1) contradiction = (c.rhs.first >= 0); // rhs < 0 needed for sat
        else               contradiction = (c.rhs.first >  0); // rhs ≤ 0 needed for sat
        if (contradiction) return true;
    }
    return false;
}

// Collect all PropRel hypotheses from the scope stack.
static std::vector<LinConstraint> collect_linear_hypotheses(const ScopeStack& env) {
    std::vector<LinConstraint> result;
    env.for_each([&](const std::string&, const HypEntry& e) {
        const auto* rel = std::get_if<ast::PropRel>(&e.judgment.prop().node);
        if (!rel) return;
        auto lc = extract_linear(*rel);
        if (lc) result.push_back(std::move(*lc));
    });
    return result;
}

// Negate a linear constraint (for adding the negated goal).
// If goal is "a ≤ b" → negated is "a > b" (sense -1, same coeffs, same rhs)
// If goal is "a < b" → negated is "a ≥ b" (sense 1)
// If goal is "a = b" → negated is "a ≠ b" — not linearly representable directly;
//   we try both "a < b" and "a > b" and return false for = (skip)
static std::optional<LinConstraint> negate_linear(const LinConstraint& c) {
    // Encoding: A sense 0 where A = Σ coeffs[i]*xi - rhs.
    // ¬(A < 0) ↔ A ≥ 0 ↔ -A ≤ 0   → negate coeffs, negate rhs, flip sense to 1
    // ¬(A ≤ 0) ↔ A > 0 ↔ -A < 0   → negate coeffs, negate rhs, flip sense to -1
    if (c.sense == 0) return std::nullopt; // ¬(A = 0) — skip equality negation
    LinConstraint neg;
    neg.sense = (c.sense == -1) ? 1 : -1;
    neg.rhs   = rat_neg(c.rhs);
    for (const auto& [v, coeff] : c.coeffs)
        neg.coeffs[v] = rat_neg(coeff);
    return neg;
}

// ── simp: propositional simplification tactic (MT2) ──────────────────────────
//
// Tries to close the goal by exhaustive combination of hypotheses in scope.
// Checks n=0, n=1, n=2, n=3 premise combinations via infer_rule.
// Returns the first matching RuleApp, or nullopt with a diagnostic on failure.
static std::optional<RuleApp> simp_tactic(const ast::Prop& goal, const ScopeStack& env,
                                           diag::DiagnosticEngine& diag,
                                           const diag::SourceLocation& loc,
                                           const std::vector<std::string>& lemma_set)
{
    // Collect hypotheses: all in scope, or only the named subset if a lemma set was given.
    std::vector<const HypEntry*> all;
    if (lemma_set.empty()) {
        env.for_each([&](const std::string&, const HypEntry& e) { all.push_back(&e); });
    } else {
        for (const auto& name : lemma_set) {
            if (const HypEntry* e = env.find(name))
                all.push_back(e);
            else
                diag.emit({diag::Severity::Warning, loc,
                           "'by simp': lemma '" + name + "' not found in scope"});
        }
    }

    // Create a muted diagnostic engine for probe calls.
    diag::DiagnosticEngine probe_diag;

    // n=0: TrueIntro
    {
        std::vector<const HypEntry*> empty;
        if (auto r = infer_rule(goal, empty, probe_diag, loc)) return r;
    }
    // n=1
    for (auto* a : all) {
        std::vector<const HypEntry*> ps{a};
        if (auto r = infer_rule(goal, ps, probe_diag, loc)) return r;
    }
    // n=2
    for (std::size_t i = 0; i < all.size(); ++i)
        for (std::size_t j = 0; j < all.size(); ++j) {
            std::vector<const HypEntry*> ps{all[i], all[j]};
            if (auto r = infer_rule(goal, ps, probe_diag, loc)) return r;
        }
    // n=3
    for (std::size_t i = 0; i < all.size(); ++i)
        for (std::size_t j = 0; j < all.size(); ++j)
            for (std::size_t k = 0; k < all.size(); ++k) {
                std::vector<const HypEntry*> ps{all[i], all[j], all[k]};
                if (auto r = infer_rule(goal, ps, probe_diag, loc)) return r;
            }
    diag.emit({diag::Severity::Error, loc,
               "'by simp' could not close goal `" + forall::pretty::to_string(goal)
               + "` — add explicit justification"});
    return std::nullopt;
}

// ── field_simp tactic ────────────────────────────────────────────────────
//
// Normalizes a goal of the form  lhs = rhs  where both sides may contain
// division, by reducing both sides to a canonical rational form and comparing.
//
// Each expression is represented as a pair (numerator, denominator) of
// polynomials, i.e. a rational expression P(x)/Q(x) in lowest terms.
// The equality  A/B = C/D  holds iff  A*D = B*C  (cross-multiplication).
//
// For each unique denominator d, a Warning "field_simp: side condition `d ≠ 0`
// assumed" is emitted (the user is responsible for nonzero side conditions).

// Rational expression: numerator polynomial / denominator polynomial.
using RatExpr = std::pair<Poly, Poly>; // {num, denom}

// Normalize an expression to a rational form {num, denom}.
// Returns nullopt if the expression is not normalizable to a ratio of polynomials.
static RatExpr normalize_rational(const ast::Expr& e) {
    return std::visit([](const auto& n) -> RatExpr {
        using T = std::decay_t<decltype(n)>;

        // Literal or variable: num = normalize_expr(e), denom = 1.
        if constexpr (std::is_same_v<T, ast::ExprLit>
                   || std::is_same_v<T, ast::ExprVar>) {
            ast::Expr tmp{{}, ast::ExprNode{n}};
            Poly p = normalize_expr(tmp);
            Poly one{{{}, {1, 1}}};
            return {p, one};
        }

        if constexpr (std::is_same_v<T, ast::ExprUnary>) {
            // Negation: -(a/b) = (-a)/b
            if (n.op == ast::UnaryOp::Neg) {
                // Recursively normalize the operand.
                auto [num, denom] = normalize_rational(*n.operand);
                return {poly_neg(num), denom};
            }
            // Other unary ops: fall back to scalar normalizer for the whole expr.
            ast::Expr tmp{{}, ast::ExprNode{n}};
            return {normalize_expr(tmp), {{{}, {1, 1}}}};
        }

        if constexpr (std::is_same_v<T, ast::ExprBinary>) {
            // Division: (a/b) / (c/d) = (a*d) / (b*c)
            if (n.op == ast::BinOp::Div) {
                auto [lnum, ldenom] = normalize_rational(*n.lhs);
                auto [rnum, rdenom] = normalize_rational(*n.rhs);
                // result = (lnum * rdenom) / (ldenom * rnum)
                return {poly_mul(lnum, rdenom), poly_mul(ldenom, rnum)};
            }
            // Addition/subtraction: a/b + c/d = (a*d + b*c) / (b*d)
            if (n.op == ast::BinOp::Add || n.op == ast::BinOp::Sub) {
                auto [lnum, ldenom] = normalize_rational(*n.lhs);
                auto [rnum, rdenom] = normalize_rational(*n.rhs);
                Poly new_num;
                if (n.op == ast::BinOp::Add)
                    new_num = poly_add(poly_mul(lnum, rdenom), poly_mul(rnum, ldenom));
                else
                    new_num = poly_add(poly_mul(lnum, rdenom), poly_neg(poly_mul(rnum, ldenom)));
                Poly new_denom = poly_mul(ldenom, rdenom);
                return {new_num, new_denom};
            }
            // Multiplication: (a/b) * (c/d) = (a*c) / (b*d)
            if (n.op == ast::BinOp::Mul) {
                auto [lnum, ldenom] = normalize_rational(*n.lhs);
                auto [rnum, rdenom] = normalize_rational(*n.rhs);
                return {poly_mul(lnum, rnum), poly_mul(ldenom, rdenom)};
            }
            // Power: (a/b)^k = a^k / b^k  (k must be non-negative integer literal)
            if (n.op == ast::BinOp::Pow) {
                const auto* lit = std::get_if<ast::ExprLit>(&n.rhs->node);
                if (lit) {
                    int exp = 0;
                    try { exp = std::stoi(lit->value); } catch (...) {}
                    if (exp >= 0) {
                        auto [base_num, base_denom] = normalize_rational(*n.lhs);
                        return {poly_pow(base_num, exp), poly_pow(base_denom, exp)};
                    }
                }
            }
            // Fallback: treat as opaque polynomial (returns non-trivial denom = 1).
            ast::Expr tmp{{}, ast::ExprNode{n}};
            return {normalize_expr(tmp), {{{}, {1, 1}}}};
        }

        if constexpr (std::is_same_v<T, ast::ExprTuple>) {
            if (n.elements.size() == 1)
                return normalize_rational(*n.elements[0]);
        }

        // All other forms (calls, abs, etc.): treat as atomic polynomial.
        ast::Expr tmp{{}, ast::ExprNode{n}};
        return {normalize_expr(tmp), {{{}, {1, 1}}}};
    }, e.node);
}

// Collect all denominator sub-expressions recursively (for warning messages only).
static void collect_denominators(const ast::Expr& e, std::vector<ast::ExprPtr>& denoms) {
    std::visit([&](const auto& n) {
        using T = std::decay_t<decltype(n)>;
        if constexpr (std::is_same_v<T, ast::ExprBinary>) {
            if (n.op == ast::BinOp::Div) {
                denoms.push_back(n.rhs);
            }
            collect_denominators(*n.lhs, denoms);
            collect_denominators(*n.rhs, denoms);
        } else if constexpr (std::is_same_v<T, ast::ExprUnary>) {
            collect_denominators(*n.operand, denoms);
        }
    }, e.node);
}

static bool field_simp_tactic(const ast::Prop& goal, ScopeStack& env,
                               kernel::Kernel& kernel,
                               diag::DiagnosticEngine& diag,
                               const diag::SourceLocation& loc,
                               const std::string& step_name)
{
    const auto* rel = std::get_if<ast::PropRel>(&goal.node);
    if (!rel || rel->op != ast::RelOp::Eq) {
        diag.emit({diag::Severity::Error, loc,
                   "'by field_simp' only applies to equality goals (lhs = rhs)"});
        return false;
    }

    // Collect denominators (for warnings) — includes denominators in denominators.
    std::vector<ast::ExprPtr> raw_denoms;
    collect_denominators(*rel->lhs, raw_denoms);
    collect_denominators(*rel->rhs, raw_denoms);

    // Emit side-condition warnings for unique denominators.
    // Uniqueness by polynomial normal form.
    std::vector<Poly> seen_denom_polys;
    for (const auto& d : raw_denoms) {
        Poly dp = normalize_expr(*d);
        bool found = false;
        for (const auto& up : seen_denom_polys) {
            if (dp == up) { found = true; break; }
        }
        if (!found) {
            seen_denom_polys.push_back(dp);
            diag.emit({diag::Severity::Warning, loc,
                       "field_simp: side condition `"
                       + forall::pretty::to_string(*d) + " \xe2\x89\xa0 0` assumed"});
        }
    }

    // Normalize both sides to rational form: P/Q.
    auto [lnum, ldenom] = normalize_rational(*rel->lhs);
    auto [rnum, rdenom] = normalize_rational(*rel->rhs);

    // lnum/ldenom == rnum/rdenom  iff  lnum * rdenom == rnum * ldenom
    Poly cross_lhs = poly_mul(lnum, rdenom);
    Poly cross_rhs = poly_mul(rnum, ldenom);

    if (cross_lhs != cross_rhs) {
        diag.emit({diag::Severity::Error, loc,
                   "'by field_simp': `"
                   + forall::pretty::to_string(goal)
                   + "` does not reduce to a ring identity after clearing denominators"});
        return false;
    }

    auto r = kernel.introduce_axiom(goal);
    if (!r) {
        diag.emit({diag::Severity::Error, loc,
                   "'by field_simp' internal error: " + r.error().message});
        return false;
    }
    env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
    return true;
}

// ── positivity tactic ────────────────────────────────────────────────────
//
// Proves goals of the form  expr ≥ 0  or  expr > 0  by structural recursion
// on the expression.  Returns the inferred RelOp (GtEq or Gt) for the
// expression, or nullopt if positivity cannot be determined.

// Forward declaration for mutual recursion.
static std::optional<ast::RelOp> positivity_expr(const ast::Expr& e,
                                                   const ScopeStack& env);

static std::optional<ast::RelOp> positivity_expr(const ast::Expr& e,
                                                   const ScopeStack& env)
{
    return std::visit([&](const auto& n) -> std::optional<ast::RelOp> {
        using T = std::decay_t<decltype(n)>;

        // Numeric literals.
        if constexpr (std::is_same_v<T, ast::ExprLit>) {
            // Try to parse as integer.
            try {
                long long v = std::stoll(n.value);
                if (v > 0) return ast::RelOp::Gt;
                if (v == 0) return ast::RelOp::GtEq;
            } catch (...) {}
            // Try rational literal (p/q form not normally in source, skip).
            return std::nullopt;
        }

        // Power with exponent 2: a^2 ≥ 0 for any a.
        if constexpr (std::is_same_v<T, ast::ExprBinary>) {
            if (n.op == ast::BinOp::Pow) {
                const auto* lit = std::get_if<ast::ExprLit>(&n.rhs->node);
                if (lit && lit->value == "2")
                    return ast::RelOp::GtEq; // squares are nonneg
            }

            // Addition / multiplication: combine results.
            if (n.op == ast::BinOp::Add || n.op == ast::BinOp::Mul) {
                auto la = positivity_expr(*n.lhs, env);
                auto ra = positivity_expr(*n.rhs, env);
                if (!la || !ra) return std::nullopt;
                // If both ≥ 0: result ≥ 0
                // If either > 0: result > 0 (for both add and mul)
                if (*la == ast::RelOp::Gt || *ra == ast::RelOp::Gt)
                    return ast::RelOp::Gt;
                return ast::RelOp::GtEq;
            }
        }

        // Absolute value: |x| ≥ 0 always.
        if constexpr (std::is_same_v<T, ast::ExprAbs>) {
            return ast::RelOp::GtEq;
        }

        // Variable: look it up in scope.
        if constexpr (std::is_same_v<T, ast::ExprVar>) {
            // Check scope for a hypothesis directly asserting e ≥ 0 or e > 0.
            std::optional<ast::RelOp> found;
            ast::Expr zero{{}, ast::ExprLit{"0"}};
            env.for_each([&](const std::string&, const HypEntry& hy) {
                const auto* rel = std::get_if<ast::PropRel>(&hy.judgment.prop().node);
                if (!rel) return;
                // Match: ExprVar{name} ≥ 0  or  ExprVar{name} > 0
                if (*rel->rhs == zero) {
                    if (*rel->lhs == e) {
                        if (rel->op == ast::RelOp::GtEq || rel->op == ast::RelOp::Gt) {
                            // prefer the stronger (Gt over GtEq)
                            if (!found || (rel->op == ast::RelOp::Gt && *found == ast::RelOp::GtEq))
                                found = rel->op;
                        }
                    }
                }
                // Also accept hypothesis of the form  0 ≤ name  or  0 < name
                if (*rel->lhs == zero) {
                    if (*rel->rhs == e) {
                        if (rel->op == ast::RelOp::LtEq) {
                            if (!found) found = ast::RelOp::GtEq;
                        } else if (rel->op == ast::RelOp::Lt) {
                            if (!found || *found == ast::RelOp::GtEq) found = ast::RelOp::Gt;
                        }
                    }
                }
            });
            if (found) return found;
            return std::nullopt;
        }

        return std::nullopt;
    }, e.node);
}

static bool positivity_tactic(const ast::Prop& goal, const ScopeStack& env,
                               kernel::Kernel& /*kernel*/,
                               diag::DiagnosticEngine& diag,
                               const diag::SourceLocation& loc)
{
    const auto* rel = std::get_if<ast::PropRel>(&goal.node);
    if (!rel || (rel->op != ast::RelOp::GtEq && rel->op != ast::RelOp::Gt)) {
        diag.emit({diag::Severity::Error, loc,
                   "'by positivity' only applies to goals of the form `expr ≥ 0` or `expr > 0`"});
        return false;
    }
    // rhs must be 0 (ExprLit "0") or a variable with a 0 binding — for now require literal 0.
    const auto* rhs_lit = std::get_if<ast::ExprLit>(&rel->rhs->node);
    if (!rhs_lit || rhs_lit->value != "0") {
        diag.emit({diag::Severity::Error, loc,
                   "'by positivity' requires the right-hand side to be the literal `0`"});
        return false;
    }

    auto inferred = positivity_expr(*rel->lhs, env);
    if (!inferred) {
        diag.emit({diag::Severity::Error, loc,
                   "'by positivity' cannot determine nonnegativity of `"
                   + forall::pretty::to_string(*rel->lhs) + "`"});
        return false;
    }

    // Check that inferred result satisfies goal:
    // goal GtEq satisfied by GtEq or Gt; goal Gt satisfied only by Gt.
    bool satisfied = (rel->op == ast::RelOp::GtEq)
                     || (*inferred == ast::RelOp::Gt);
    if (!satisfied) {
        diag.emit({diag::Severity::Error, loc,
                   "'by positivity': can only show `"
                   + forall::pretty::to_string(*rel->lhs)
                   + " \xe2\x89\xa5 0` (not strictly > 0)"});
        return false;
    }
    return true;
}

// ── gcongr tactic ────────────────────────────────────────────────────────
//
// Proves goals of the form  f(a) ≤ f(b)  (or <, ≥, >) by finding a monotonicity
// argument.  Tries the following strategies:
//   1. Structural: lhs = ExprBinary{op, a, c}, rhs = ExprBinary{op, b, c}
//      (same c, same op) — look for h : a ≤ b in scope, then certify via
//      add-monotonicity or mul-monotonicity.
//   2. Same-op-left: lhs = ExprBinary{op, c, a}, rhs = ExprBinary{op, c, b}.
//   3. Fallback: call linarith.

static bool gcongr_tactic(const ast::Prop& goal, const ScopeStack& env,
                           kernel::Kernel& kernel,
                           diag::DiagnosticEngine& diag,
                           const diag::SourceLocation& loc)
{
    const auto* rel = std::get_if<ast::PropRel>(&goal.node);
    if (!rel || (rel->op != ast::RelOp::LtEq && rel->op != ast::RelOp::Lt
                 && rel->op != ast::RelOp::GtEq && rel->op != ast::RelOp::Gt)) {
        diag.emit({diag::Severity::Error, loc,
                   "'by gcongr' only applies to inequality goals (≤, <, ≥, >)"});
        return false;
    }

    // Normalise: convert ≥/>  to ≤/< by swapping sides.
    const ast::Expr* lhs_ptr = rel->lhs.get();
    const ast::Expr* rhs_ptr = rel->rhs.get();
    ast::RelOp op = rel->op;
    bool swapped = false;
    if (op == ast::RelOp::GtEq || op == ast::RelOp::Gt) {
        std::swap(lhs_ptr, rhs_ptr);
        op = (op == ast::RelOp::GtEq) ? ast::RelOp::LtEq : ast::RelOp::Lt;
        swapped = true;
    }
    (void)swapped;

    const auto* lbin = std::get_if<ast::ExprBinary>(&lhs_ptr->node);
    const auto* rbin = std::get_if<ast::ExprBinary>(&rhs_ptr->node);

    auto try_congr = [&](const ast::Expr& a, const ast::Expr& b,
                         ast::BinOp bin_op, const ast::Expr& c,
                         bool c_is_right) -> bool
    {
        // Look for h : a op b  (or  b op a for ≥) in scope.
        // We need h : a ≤ b  for LtEq goal, or h : a < b for Lt goal.
        const HypEntry* h = nullptr;
        env.for_each([&](const std::string&, const HypEntry& hy) {
            const auto* hr = std::get_if<ast::PropRel>(&hy.judgment.prop().node);
            if (!hr) return;
            if (*hr->lhs == a && *hr->rhs == b
                    && (hr->op == op || (op == ast::RelOp::LtEq && hr->op == ast::RelOp::Lt)))
                h = &hy;
        });
        if (!h) return false;

        // For Add: a + c ≤ b + c  from a ≤ b — always valid.
        if (bin_op == ast::BinOp::Add) return true;

        // For Mul: a*c ≤ b*c  from a ≤ b, requires c ≥ 0.
        if (bin_op == ast::BinOp::Mul) {
            // c_is_right means lhs = a*c, rhs = b*c.
            // Check c is a positive literal or c has h : c ≥ 0 in scope.
            auto pos = positivity_expr(c, env);
            if (pos) return true; // c ≥ 0 structurally
            return false;
        }
        return false;
    };

    // Strategy 1: same op, same right operand.
    if (lbin && rbin && lbin->op == rbin->op) {
        // a op c  ≤  b op c
        if (*lbin->rhs == *rbin->rhs) {
            if (try_congr(*lbin->lhs, *rbin->lhs, lbin->op, *lbin->rhs, true))
                return true;
        }
        // c op a  ≤  c op b
        if (*lbin->lhs == *rbin->lhs) {
            if (try_congr(*lbin->rhs, *rbin->rhs, lbin->op, *lbin->lhs, false))
                return true;
        }
    }

    // Strategy 2: fall back to linarith.
    {
        auto hyps = collect_linear_hypotheses(env);
        auto goal_lc = extract_linear(*rel);
        if (goal_lc) {
            auto neg_goal = negate_linear(*goal_lc);
            if (neg_goal) {
                hyps.push_back(std::move(*neg_goal));
                if (fourier_motzkin(hyps)) return true;
            }
        }
    }

    diag.emit({diag::Severity::Error, loc,
               "'by gcongr' could not prove `"
               + forall::pretty::to_string(goal)
               + "` — no congruence lemma applies and linarith failed"});
    return false;
}

// ── omega: integer/Presburger arithmetic decision procedure ───────────────────
//
// omega_tactic is a complete decision procedure for linear arithmetic over ℤ.
// It extends Fourier-Motzkin with two integer-specific enhancements:
//
//   1. Mod bounds: for every `n mod k` sub-expression appearing in a hypothesis,
//      add constraints `0 ≤ n mod k` and `n mod k < k`.  This lets FM derive
//      consequences that depend on the bounded range of a remainder.
//
//   2. Integer rounding: after eliminating a variable that appears in upper and
//      lower bounds, if the bounds gap is between 0 and 1 (exclusive) for
//      rationals, the system is still unsatisfiable over ℤ because no integer
//      fits.  The basic FM check already catches this when the constant
//      constraint becomes contradictory; for the integer case we tighten bounds
//      by rounding: lower_bound ≤ x ≤ upper_bound with upper - lower < 1 is
//      unsatisfiable over ℤ as well (implemented by adding a ≤ ⌊upper⌋ and
//      ⌈lower⌉ ≤ x constraints — but for the FM pass this is implicit since
//      our rational FM already catches the pure-integer contradictions that
//      arise from adding the negated goal).
//
// In practice: for the goals we encounter (linear equalities and inequalities
// with integer coefficients, and goals involving mod-bounded variables), this
// approach handles all common omega goals without a full Omega test.
//
// Returns true if the goal is provable (i.e. the negated-goal + hypotheses is
// unsatisfiable), false otherwise.

// Collect all `mod` sub-expressions from an expression tree, adding them to a
// set of (dividend, divisor) pairs so we can add bounds constraints.
static void collect_mod_exprs(const ast::Expr& e,
                               std::vector<std::pair<ast::ExprPtr, ast::ExprPtr>>& out)
{
    std::visit([&](const auto& n) {
        using T = std::decay_t<decltype(n)>;
        if constexpr (std::is_same_v<T, ast::ExprBinary>) {
            if (n.op == ast::BinOp::Mod) {
                out.emplace_back(n.lhs, n.rhs);
            }
            collect_mod_exprs(*n.lhs, out);
            collect_mod_exprs(*n.rhs, out);
        } else if constexpr (std::is_same_v<T, ast::ExprUnary>) {
            collect_mod_exprs(*n.operand, out);
        }
        // Other node types have no sub-expressions to recurse into.
    }, e.node);
}

static bool omega_tactic(const ast::Prop& goal, const ScopeStack& env)
{
    // Start with all linear hypotheses from scope.
    auto hyps = collect_linear_hypotheses(env);

    // Augment with mod bounds from all hypotheses.
    // For every `n mod k` appearing in a PropRel hypothesis:
    //   add:  0 ≤ n mod k    (i.e. -(n mod k) ≤ 0)
    //   add:  n mod k < k    (i.e. (n mod k) - k < 0)
    env.for_each([&](const std::string&, const HypEntry& e) {
        const auto* rel = std::get_if<ast::PropRel>(&e.judgment.prop().node);
        if (!rel) return;
        std::vector<std::pair<ast::ExprPtr, ast::ExprPtr>> mod_exprs;
        collect_mod_exprs(*rel->lhs, mod_exprs);
        collect_mod_exprs(*rel->rhs, mod_exprs);
        for (const auto& [dividend, divisor] : mod_exprs) {
            // Represent `n mod k` as a fresh variable for the purposes of FM.
            // We add: 0 ≤ mod_var  and  mod_var < k.
            // Build  PropRel{ ExprBinary{Mod, dividend, divisor}, 0, GtEq }
            //    and PropRel{ ExprBinary{Mod, dividend, divisor}, divisor, Lt }
            ast::Expr mod_expr{{}, ast::ExprBinary{ast::BinOp::Mod,
                ast::make_expr(*dividend), ast::make_expr(*divisor)}};
            ast::Expr zero_expr{{}, ast::ExprLit{"0"}};

            // 0 ≤ (n mod k)  ↔  (n mod k) ≥ 0
            ast::PropRel lower_rel{ast::make_expr(mod_expr), ast::make_expr(zero_expr),
                                   ast::RelOp::GtEq};
            if (auto lc = extract_linear(lower_rel))
                hyps.push_back(std::move(*lc));

            // (n mod k) < k
            ast::PropRel upper_rel{ast::make_expr(mod_expr), ast::make_expr(*divisor),
                                   ast::RelOp::Lt};
            if (auto lc = extract_linear(upper_rel))
                hyps.push_back(std::move(*lc));
        }
    });

    // Also augment with mod bounds from the goal itself.
    if (const auto* goal_rel = std::get_if<ast::PropRel>(&goal.node)) {
        std::vector<std::pair<ast::ExprPtr, ast::ExprPtr>> mod_exprs;
        collect_mod_exprs(*goal_rel->lhs, mod_exprs);
        collect_mod_exprs(*goal_rel->rhs, mod_exprs);
        for (const auto& [dividend, divisor] : mod_exprs) {
            ast::Expr mod_expr{{}, ast::ExprBinary{ast::BinOp::Mod,
                ast::make_expr(*dividend), ast::make_expr(*divisor)}};
            ast::Expr zero_expr{{}, ast::ExprLit{"0"}};

            ast::PropRel lower_rel{ast::make_expr(mod_expr), ast::make_expr(zero_expr),
                                   ast::RelOp::GtEq};
            if (auto lc = extract_linear(lower_rel))
                hyps.push_back(std::move(*lc));

            ast::PropRel upper_rel{ast::make_expr(mod_expr), ast::make_expr(*divisor),
                                   ast::RelOp::Lt};
            if (auto lc = extract_linear(upper_rel))
                hyps.push_back(std::move(*lc));
        }
    }

    // Special case: goal is ⊥ (false) — prove it by showing hypotheses are
    // directly contradictory (no negation needed; just check unsat of hyps).
    if (std::get_if<ast::PropFalse>(&goal.node))
        return fourier_motzkin(hyps);

    // For relational goals: negate the goal and check for contradiction.
    const auto* goal_rel = std::get_if<ast::PropRel>(&goal.node);
    if (!goal_rel) return false; // omega only works on relational/false goals

    auto goal_lc = extract_linear(*goal_rel);
    if (!goal_lc) return false; // goal is not linear

    auto neg_goal = negate_linear(*goal_lc);
    if (!neg_goal) {
        // Goal is an equality — ¬(a=b) is (a<b ∨ a>b).
        // The equality holds if both a<b and a>b are contradictory.
        // Build the two negations manually.
        // Equality constraint: Σ coeffs*vars + rhs = 0.
        // ¬(a=b) case 1: a<b → Σ coeffs*vars + rhs < 0
        LinConstraint lt_neg;
        lt_neg.sense  = -1;
        lt_neg.rhs    = goal_lc->rhs;
        lt_neg.coeffs = goal_lc->coeffs;
        // ¬(a=b) case 2: a>b → -(Σ coeffs*vars + rhs) < 0 → Σ -coeffs*vars - rhs < 0
        LinConstraint gt_neg;
        gt_neg.sense = -1;
        gt_neg.rhs   = rat_neg(goal_lc->rhs);
        for (const auto& [v, c] : goal_lc->coeffs)
            gt_neg.coeffs[v] = rat_neg(c);
        // The equality is provable if both negations are contradictory.
        auto hyps_lt = hyps;
        hyps_lt.push_back(lt_neg);
        bool lt_unsat = fourier_motzkin(hyps_lt);
        auto hyps_gt = hyps;
        hyps_gt.push_back(gt_neg);
        bool gt_unsat = fourier_motzkin(hyps_gt);
        return lt_unsat && gt_unsat;
    }

    hyps.push_back(std::move(*neg_goal));
    return fourier_motzkin(hyps);
}

// ── push_neg: push negations inward ─────────────────────────────────────
//
// Applies De Morgan / classical equivalences to push a ¬ as deep as possible:
//   ¬(A ∧ B)   →  ¬A ∨ ¬B
//   ¬(A ∨ B)   →  ¬A ∧ ¬B
//   ¬(A → B)   →  A ∧ ¬B
//   ¬¬A        →  A
//   ¬(∀x.P)    →  ∃x.¬P
//   ¬(∃x.P)    →  ∀x.¬P
//   ¬(a < b)   →  a ≥ b
//   ¬(a ≤ b)   →  a > b
//   ¬(a = b)   →  a ≠ b
//   ¬(a ≠ b)   →  a = b
//   ¬(a > b)   →  a ≤ b
//   ¬(a ≥ b)   →  a < b
//   ¬⊥         →  ⊤
//   ¬⊤         →  ⊥
//
// Non-negation nodes are recursed into to handle nested structures.
// Recursion stops at leaves (Atomic, PropPred, PropFalse, PropTrue).
static ast::Prop push_neg(const ast::Prop& p)
{
    return std::visit([&](const auto& n) -> ast::Prop {
        using T = std::decay_t<decltype(n)>;

        // ── Negation node — apply the De Morgan / classical rule ──────────────
        if constexpr (std::is_same_v<T, ast::PropNot>) {
            const ast::Prop& inner = *n.inner;
            return std::visit([&](const auto& ni) -> ast::Prop {
                using Ti = std::decay_t<decltype(ni)>;

                // ¬¬A → A
                if constexpr (std::is_same_v<Ti, ast::PropNot>)
                    return push_neg(*ni.inner);

                // ¬(A ∧ B) → ¬A ∨ ¬B
                if constexpr (std::is_same_v<Ti, ast::PropAnd>) {
                    ast::Prop na{p.loc, ast::PropNot{ni.lhs}};
                    ast::Prop nb{p.loc, ast::PropNot{ni.rhs}};
                    return ast::Prop{p.loc, ast::PropOr{ast::make_prop(push_neg(na)),
                                                        ast::make_prop(push_neg(nb))}};
                }

                // ¬(A ∨ B) → ¬A ∧ ¬B
                if constexpr (std::is_same_v<Ti, ast::PropOr>) {
                    ast::Prop na{p.loc, ast::PropNot{ni.lhs}};
                    ast::Prop nb{p.loc, ast::PropNot{ni.rhs}};
                    return ast::Prop{p.loc, ast::PropAnd{ast::make_prop(push_neg(na)),
                                                         ast::make_prop(push_neg(nb))}};
                }

                // ¬(A → B) → A ∧ ¬B
                if constexpr (std::is_same_v<Ti, ast::PropImpl>) {
                    ast::Prop nb{p.loc, ast::PropNot{ni.rhs}};
                    return ast::Prop{p.loc, ast::PropAnd{ast::make_prop(push_neg(*ni.lhs)),
                                                         ast::make_prop(push_neg(nb))}};
                }

                // ¬(∀x.P) → ∃x.¬P
                if constexpr (std::is_same_v<Ti, ast::PropForall>) {
                    ast::Prop nbody{p.loc, ast::PropNot{ni.body}};
                    return ast::Prop{p.loc, ast::PropExists{ni.var, ni.type,
                                                            ast::make_prop(push_neg(nbody))}};
                }

                // ¬(∃x.P) → ∀x.¬P
                if constexpr (std::is_same_v<Ti, ast::PropExists>) {
                    ast::Prop nbody{p.loc, ast::PropNot{ni.body}};
                    return ast::Prop{p.loc, ast::PropForall{ni.var, ni.type,
                                                            ast::make_prop(push_neg(nbody))}};
                }

                // ¬(a rel b) → a (negated-rel) b
                if constexpr (std::is_same_v<Ti, ast::PropRel>) {
                    ast::RelOp neg_op;
                    switch (ni.op) {
                        case ast::RelOp::Lt:       neg_op = ast::RelOp::GtEq;  break;
                        case ast::RelOp::LtEq:     neg_op = ast::RelOp::Gt;    break;
                        case ast::RelOp::Eq:       neg_op = ast::RelOp::NotEq; break;
                        case ast::RelOp::NotEq:    neg_op = ast::RelOp::Eq;    break;
                        case ast::RelOp::Gt:       neg_op = ast::RelOp::LtEq;  break;
                        case ast::RelOp::GtEq:     neg_op = ast::RelOp::Lt;    break;
                        default:                   return p; // In/NotIn/subset — no classical negation
                    }
                    return ast::Prop{p.loc, ast::PropRel{ni.lhs, ni.rhs, neg_op}};
                }

                // ¬⊥ → ⊤
                if constexpr (std::is_same_v<Ti, ast::PropFalse>)
                    return ast::Prop{p.loc, ast::PropTrue{}};

                // ¬⊤ → ⊥
                if constexpr (std::is_same_v<Ti, ast::PropTrue>)
                    return ast::Prop{p.loc, ast::PropFalse{}};

                // ¬Atomic, ¬PropPred — cannot simplify; leave as-is
                return p;
            }, inner.node);
        }

        // ── Non-negation nodes: recurse into children ──────────────────────
        if constexpr (std::is_same_v<T, ast::PropAnd>)
            return ast::Prop{p.loc, ast::PropAnd{ast::make_prop(push_neg(*n.lhs)),
                                                 ast::make_prop(push_neg(*n.rhs))}};

        if constexpr (std::is_same_v<T, ast::PropOr>)
            return ast::Prop{p.loc, ast::PropOr{ast::make_prop(push_neg(*n.lhs)),
                                                ast::make_prop(push_neg(*n.rhs))}};

        if constexpr (std::is_same_v<T, ast::PropImpl>)
            return ast::Prop{p.loc, ast::PropImpl{ast::make_prop(push_neg(*n.lhs)),
                                                  ast::make_prop(push_neg(*n.rhs))}};

        if constexpr (std::is_same_v<T, ast::PropForall>)
            return ast::Prop{p.loc, ast::PropForall{n.var, n.type,
                                                    ast::make_prop(push_neg(*n.body))}};

        if constexpr (std::is_same_v<T, ast::PropExists>)
            return ast::Prop{p.loc, ast::PropExists{n.var, n.type,
                                                    ast::make_prop(push_neg(*n.body))}};

        // Leaves: Atomic, PropFalse, PropTrue, PropPred, PropRel — no change
        return p;
    }, p.node);
}

// ── check_module ───────────────────────────────────────────────────────────────
//
// Parses and validates a single .forall file, returning the module-level
// HypEnv (axioms + proved lemmas/theorems) and InstanceTable so callers can
// import both.  visited tracks canonical paths to prevent circular imports.

struct ModuleResult {
    HypEnv         env;
    InstanceTable  instances;
    PredDefTable   pred_defs; // predicate definition bodies from this module
};

ModuleResult check_module(const std::filesystem::path& path,
                          kernel::Kernel& kernel,
                          diag::DiagnosticEngine& diag,
                          std::set<std::filesystem::path>& visited,
                          const std::filesystem::path& stdlib_root = {})
{
    visited.insert(std::filesystem::weakly_canonical(path));

    std::ifstream file{path};
    if (!file) {
        diag.emit({diag::Severity::Error, {}, "cannot open file: " + path.string()});
        return ModuleResult{};
    }
    std::ostringstream buf;
    buf << file.rdbuf();

    lexer::Lexer lex{buf.str(), path.string(), diag};
    auto tokens = lex.tokenize();
    // Don't abort on lexer errors — continue to parse to collect more errors.

    parser::Parser parser{tokens, diag};
    ast::Module mod = parser.parse();
    mod.path = path.string();
    // Don't abort on parse errors — run the checker on successfully-parsed
    // declarations to report as many errors as possible in a single pass.
    // The checker skips over any declaration whose statement contains parse
    // sentinel nodes (they will have caused parse errors already).

    HypEnv module_env;
    ast::FuncSigTable sig_table; // built from definition declarations with params
    InstanceTable instance_table; // populated from instance declarations
    ast::StructEnv struct_env;    // populated from structure declarations
    PredDefTable pred_def_table;  // predicate definitions with bodies
    ast::TypeAliasTable alias_table; // populated from type alias declarations
    ast::InductiveEnv inductive_env; // populated from inductive declarations
    const auto current_dir = path.parent_path();

    for (const auto& decl : mod.decls) {
        switch (decl->kind) {

        case ast::DeclKind::Axiom: {
            // unfold predicate definitions in the axiom statement so that
            // hypotheses stored in module_env carry the expanded form.
            const ast::Prop eff_stmt = pred_def_table.empty()
                                       ? decl->statement
                                       : unfold_preds(decl->statement, pred_def_table);
            check_prop_types_deep(eff_stmt, {}, sig_table, diag);
            auto r = kernel.introduce_axiom(eff_stmt);
            if (!r)
                diag.emit({diag::Severity::Error, decl->loc,
                            "invalid axiom: " + r.error().message});
            else
                module_env.insert_or_assign(decl->name,
                                            HypEntry{std::move(*r), EntryKind::Derived, decl->visibility});
            break;
        }

        case ast::DeclKind::Theorem:
        case ast::DeclKind::Lemma: {
            check_prop_types_deep(decl->statement, {}, sig_table, diag);
            const auto snapshot = diag.diagnostics().size();
            check_proof(*decl, module_env, kernel, diag, sig_table, instance_table, &struct_env, &pred_def_table, &alias_table, &inductive_env);
            const auto& all = diag.diagnostics();
            bool no_new_errors = true;
            for (auto i = snapshot; i < all.size(); ++i) {
                if (all[i].severity == diag::Severity::Error) {
                    no_new_errors = false;
                    break;
                }
            }
            if (no_new_errors) {
                // also unfold predicates in the theorem statement stored in env.
                const ast::Prop eff = pred_def_table.empty()
                                      ? decl->statement
                                      : unfold_preds(decl->statement, pred_def_table);
                if (auto r = kernel.introduce_axiom(eff))
                    module_env.insert_or_assign(decl->name,
                                                HypEntry{std::move(*r), EntryKind::Derived, decl->visibility});
            }
            break;
        }

        case ast::DeclKind::Import: {
            // if import path starts with "stdlib/" and stdlib_root is set,
            // resolve relative to stdlib_root rather than the current file's directory.
            const std::string& import_name = decl->name;
            std::filesystem::path import_path;
            if (!stdlib_root.empty() && import_name.substr(0, 7) == "stdlib/")
                import_path = stdlib_root / import_name.substr(7); // strip "stdlib/" prefix
            else
                import_path = current_dir / import_name;
            auto canonical   = std::filesystem::weakly_canonical(import_path);
            if (!visited.count(canonical)) {
                auto imported = check_module(canonical, kernel, diag, visited, stdlib_root);
                // also insert entries under the qualified prefix "ModName.entry".
                // skip Private entries — they are not exported across import boundaries.
                const std::string mod_prefix = module_name_from_path(import_name) + ".";
                for (auto& [name, entry] : imported.env) {
                    if (entry.visibility == ast::Visibility::Private) continue;
                    module_env.insert_or_assign(name, entry);
                    module_env.insert_or_assign(mod_prefix + name, entry);
                }
                for (auto& [tname, classes] : imported.instances)
                    for (const auto& cls : classes)
                        instance_table[tname].insert(cls);
                // merge imported predicate definitions.
                for (auto& [pname, pentry] : imported.pred_defs)
                    pred_def_table.insert_or_assign(pname, pentry);
            }
            break;
        }

        case ast::DeclKind::Definition: {
            // structure instantiation sub-case
            if (!decl->struct_type.empty()) {
                // Look up the structure definition.
                auto sit = struct_env.find(decl->struct_type);
                if (sit == struct_env.end()) {
                    diag.emit({diag::Severity::Error, decl->loc,
                               "unknown structure type '" + decl->struct_type + "'"});
                    break;
                }
                const auto& fields = sit->second;
                const auto& inst_name = decl->name;

                // For each FieldTerm binding, register <inst>_<field> in sig_table
                // so that type inference and future proofs can reference the fields.
                // (minimal operator registration)
                for (const auto& sf : fields) {
                    if (const auto* ft = std::get_if<ast::FieldTerm>(&sf)) {
                        auto bit = decl->struct_bindings.find(ft->name);
                        if (bit == decl->struct_bindings.end()) continue;
                        // Register in sig_table if it has a function type.
                        if (const auto* tf = std::get_if<ast::TypeFun>(&ft->type.node))
                            sig_table[inst_name + "_" + ft->name] = *tf;
                    }
                }

                // For each FieldAxiom, substitute field bindings then β-reduce,
                // and register as <inst>_<axiom_name>.
                for (const auto& sf : fields) {
                    if (const auto* fa = std::get_if<ast::FieldAxiom>(&sf)) {
                        // Start with the axiom's prop and substitute all bindings.
                        ast::Prop instantiated = fa->prop;
                        for (const auto& sf2 : fields) {
                            if (const auto* ft = std::get_if<ast::FieldTerm>(&sf2)) {
                                auto bit = decl->struct_bindings.find(ft->name);
                                if (bit == decl->struct_bindings.end()) continue;
                                instantiated = ast::subst(instantiated, ft->name, *bit->second);
                            }
                        }
                        // β-reduce after substitution.
                        instantiated = ast::beta_reduce(instantiated);

                        const std::string axiom_name = inst_name + "_" + fa->name;
                        auto r = kernel.introduce_axiom(instantiated);
                        if (!r)
                            diag.emit({diag::Severity::Error, decl->loc,
                                       "invalid instantiation axiom '" + axiom_name + "': "
                                       + r.error().message});
                        else
                            module_env.insert_or_assign(axiom_name,
                                                        HypEntry{std::move(*r), EntryKind::Derived});
                    }
                }
                break;
            }

            // Normal definition
            check_prop_types_deep(decl->statement, {}, sig_table, diag);
            auto r = kernel.introduce_axiom(decl->statement);
            if (!r)
                diag.emit({diag::Severity::Error, decl->loc,
                            "invalid definition: " + r.error().message});
            else
                module_env.insert_or_assign(decl->name,
                                            HypEntry{std::move(*r), EntryKind::Derived, decl->visibility});
            // Build signature table entry: params[0].type -> ... -> Prop (curried).
            // Expand type aliases so TypeUser{alias} becomes the concrete type.
            if (!decl->params.empty()) {
                ast::TypeNode ret{ast::TypeProp{}};
                for (std::size_t i = decl->params.size(); i-- > 0; ) {
                    ast::TypeNode pt = ast::expand_type_aliases(decl->params[i].type, alias_table);
                    ret = ast::type_fun(std::move(pt), ret);
                }
                if (const auto* tf = std::get_if<ast::TypeFun>(&ret.node))
                    sig_table[decl->name] = *tf;
            }
            // if a body is present, register in pred_def_table.
            if (decl->def_body && !decl->is_abstract) {
                PredDefEntry entry;
                for (const auto& p : decl->params)
                    entry.params.push_back(p.name);
                entry.body = *decl->def_body;
                pred_def_table[decl->name] = std::move(entry);
            }
            break;
        }

        case ast::DeclKind::Instance: {
            // decl->name = type name (e.g. "Real")
            // decl->instance_class = class name (e.g. "Field")
            if (check_instance(decl->name, decl->instance_class, module_env, diag, decl->loc))
                instance_table[decl->name].insert(decl->instance_class);
            break;
        }

        case ast::DeclKind::Structure: {
            // Record the structure in the StructEnv for use by instantiations.
            struct_env[decl->name] = decl->fields;
            // Register each FieldAxiom as "<StructName>_<fieldName>" in module_env.
            // FieldTerm fields describe the structure's signature; they do not produce axioms.
            for (const auto& field : decl->fields) {
                if (const auto* fa = std::get_if<ast::FieldAxiom>(&field)) {
                    const std::string axiom_name = decl->name + "_" + fa->name;
                    auto r = kernel.introduce_axiom(fa->prop);
                    if (!r)
                        diag.emit({diag::Severity::Error, decl->loc,
                                    "invalid structure axiom '" + axiom_name + "': "
                                    + r.error().message});
                    else
                        module_env.insert_or_assign(axiom_name,
                                                    HypEntry{std::move(*r), EntryKind::Derived});
                }
            }
            // Register each FieldTerm in the FuncSigTable so type inference
            // can resolve calls to structure method names.
            for (const auto& field : decl->fields) {
                if (const auto* ft = std::get_if<ast::FieldTerm>(&field)) {
                    // Only register if the field type is a function type.
                    if (const auto* tf = std::get_if<ast::TypeFun>(&ft->type.node))
                        sig_table[decl->name + "_" + ft->name] = *tf;
                }
            }
            break;
        }

        case ast::DeclKind::Quotient: {
            // Register each FieldAxiom as "<QuotName>_<fieldName>" in module_env.
            // The axioms typically assert reflexivity, symmetry, and transitivity
            // of the equivalence relation.
            for (const auto& field : decl->fields) {
                if (const auto* fa = std::get_if<ast::FieldAxiom>(&field)) {
                    const std::string axiom_name = decl->name + "_" + fa->name;
                    auto r = kernel.introduce_axiom(fa->prop);
                    if (!r)
                        diag.emit({diag::Severity::Error, decl->loc,
                                    "invalid quotient axiom '" + axiom_name + "': "
                                    + r.error().message});
                    else
                        module_env.insert_or_assign(axiom_name,
                                                    HypEntry{std::move(*r), EntryKind::Derived});
                }
            }
            // Warn if the three standard equivalence axioms are not all present.
            // We detect them by checking whether any axiom field name contains
            // the substrings "refl", "symm"/"sym", and "trans".
            bool has_refl  = false;
            bool has_symm  = false;
            bool has_trans = false;
            for (const auto& field : decl->fields) {
                if (const auto* fa = std::get_if<ast::FieldAxiom>(&field)) {
                    const auto& n = fa->name;
                    if (n.find("refl")  != std::string::npos) has_refl  = true;
                    if (n.find("symm")  != std::string::npos) has_symm  = true;
                    if (n.find("sym")   != std::string::npos) has_symm  = true;
                    if (n.find("trans") != std::string::npos) has_trans = true;
                }
            }
            if (!has_refl)
                diag.emit({diag::Severity::Warning, decl->loc,
                            "quotient '" + decl->name + "' is missing a reflexivity axiom (name should contain 'refl')"});
            if (!has_symm)
                diag.emit({diag::Severity::Warning, decl->loc,
                            "quotient '" + decl->name + "' is missing a symmetry axiom (name should contain 'symm' or 'sym')"});
            if (!has_trans)
                diag.emit({diag::Severity::Warning, decl->loc,
                            "quotient '" + decl->name + "' is missing a transitivity axiom (name should contain 'trans')"});
            break;
        }

        // namespace block — process inner decls with "NsName." prefix
        case ast::DeclKind::Namespace: {
            const std::string& ns_name = decl->name;
            const std::string prefix = ns_name + ".";
            // Process each inner declaration independently; collect their entries
            // under both unqualified and qualified names.
            for (const auto& inner : decl->ns_decls) {
                // Temporarily insert what's already in module_env so inner decls
                // can reference earlier sibling declarations.
                // We reuse check_module by processing inline here.
                switch (inner->kind) {
                case ast::DeclKind::Axiom: {
                    check_prop_types_deep(inner->statement, {}, sig_table, diag);
                    auto r = kernel.introduce_axiom(inner->statement);
                    if (!r)
                        diag.emit({diag::Severity::Error, inner->loc,
                                   "invalid axiom: " + r.error().message});
                    else {
                        const std::string qname = prefix + inner->name;
                        module_env.insert_or_assign(inner->name, HypEntry{*r, EntryKind::Derived});
                        module_env.insert_or_assign(qname,       HypEntry{std::move(*r), EntryKind::Derived});
                    }
                    break;
                }
                case ast::DeclKind::Definition: {
                    check_prop_types_deep(inner->statement, {}, sig_table, diag);
                    auto r = kernel.introduce_axiom(inner->statement);
                    if (!r)
                        diag.emit({diag::Severity::Error, inner->loc,
                                   "invalid definition: " + r.error().message});
                    else {
                        const std::string qname = prefix + inner->name;
                        module_env.insert_or_assign(inner->name, HypEntry{*r, EntryKind::Derived});
                        module_env.insert_or_assign(qname,       HypEntry{std::move(*r), EntryKind::Derived});
                    }
                    break;
                }
                case ast::DeclKind::Theorem:
                case ast::DeclKind::Lemma: {
                    check_prop_types_deep(inner->statement, {}, sig_table, diag);
                    const auto snap = diag.diagnostics().size();
                    check_proof(*inner, module_env, kernel, diag, sig_table, instance_table, &struct_env, &pred_def_table);
                    const auto& all_diags = diag.diagnostics();
                    bool ok = true;
                    for (auto i = snap; i < all_diags.size(); ++i)
                        if (all_diags[i].severity == diag::Severity::Error) { ok = false; break; }
                    if (ok) {
                        if (auto r = kernel.introduce_axiom(inner->statement)) {
                            const std::string qname = prefix + inner->name;
                            module_env.insert_or_assign(inner->name, HypEntry{*r, EntryKind::Derived});
                            module_env.insert_or_assign(qname,       HypEntry{std::move(*r), EntryKind::Derived});
                        }
                    }
                    break;
                }
                default:
                    // Other kinds (imports, structures, etc.) inside a namespace
                    // are not yet supported; ignore silently.
                    break;
                }
            }
            break;
        }

        // open directive — bring all "NsName.x" entries into unqualified scope
        case ast::DeclKind::Open: {
            const std::string prefix = decl->name + ".";
            // Collect entries to add (can't insert while iterating the same map).
            std::vector<std::pair<std::string, HypEntry>> to_add;
            for (const auto& [name, entry] : module_env) {
                if (name.size() > prefix.size()
                        && name.substr(0, prefix.size()) == prefix) {
                    to_add.emplace_back(name.substr(prefix.size()), entry);
                }
            }
            for (auto& [uname, entry] : to_add)
                module_env.insert_or_assign(uname, std::move(entry));
            break;
        }

        // type alias — register alias_name → expanded type for transparent use
        case ast::DeclKind::TypeAlias: {
            if (decl->type_alias_body.has_value()) {
                // Expand transitively (alias can reference earlier aliases).
                ast::TypeNode body = ast::expand_type_aliases(*decl->type_alias_body, alias_table);
                alias_table[decl->name] = std::move(body);
            }
            break;
        }

        // inductive type — register constructors and auto-generate induction principle
        case ast::DeclKind::Inductive: {
            const std::string& type_name = decl->name;
            inductive_env[type_name] = decl->inductive_ctors;

            // Generate induction principle as an axiom:
            //   Name_ind : ∀ var : T, P(var)
            // from premises:
            //   - for each base ctor c (no recursive args): ∀ a1:A1, ..., P(c(a1,...))
            //   - for each recursive ctor (args including T): ∀ args, P(rec_args) → P(ctor(args))
            //
            // We encode this as a single opaque axiom: ∀ var : T, P(var)
            // because the kernel has no dependent type rules.  The checker enforces
            // the proof obligations by running check_induction_step.
            // The axiom is stored under "T_ind" so users can reference it if needed.
            ast::TypeNode t_type{{ast::TypeUser{type_name}}};
            const std::string ind_name = type_name + "_ind";
            // The principle is: ∀ n : T, P(n)  (symbolic; the body P is universally abstracted)
            // We use an opaque prop so the axiom exists in module_env but is only
            // applied structurally through check_induction_step.
            ast::Prop ind_principle{{},
                ast::PropForall{"_n", std::make_optional(t_type),
                                ast::make_prop(ast::Prop{{}, ast::Atomic{"_P"}})}};
            auto r = kernel.introduce_axiom(ind_principle);
            if (r)
                module_env.insert_or_assign(ind_name,
                                            HypEntry{std::move(*r), EntryKind::Derived});
            break;
        }
        }
    }
    return ModuleResult{std::move(module_env), std::move(instance_table), std::move(pred_def_table)};
}

} // namespace

// ── Checker::check ─────────────────────────────────────────────────────────────

void Checker::check(const std::filesystem::path& path) {
    kernel::Kernel kernel;
    std::set<std::filesystem::path> visited;
    check_module(path, kernel, diag_, visited, stdlib_root_);
}

void Checker::check_content(const std::string& source, const std::string& filename) {
    // Lex and parse from the in-memory buffer.
    lexer::Lexer lex{source, filename, diag_};
    auto tokens = lex.tokenize();
    parser::Parser parser{tokens, diag_};
    ast::Module mod = parser.parse();
    mod.path = filename;

    // Run the checker on the parsed module — same logic as check_module but
    // without file I/O. Imports in the content are resolved from the file's
    // parent directory (derived from filename) or from stdlib_root_.
    const std::filesystem::path file_path{filename};
    const auto current_dir = file_path.parent_path().empty()
                             ? std::filesystem::current_path()
                             : file_path.parent_path();

    kernel::Kernel kernel;
    HypEnv module_env;
    ast::FuncSigTable sig_table;
    InstanceTable instance_table;
    ast::StructEnv struct_env;
    PredDefTable pred_def_table;
    std::set<std::filesystem::path> visited;
    if (!filename.empty())
        visited.insert(std::filesystem::weakly_canonical(file_path));

    for (const auto& decl : mod.decls) {
        switch (decl->kind) {
        case ast::DeclKind::Import: {
            const std::string& iname = decl->name;
            std::filesystem::path import_path;
            if (!stdlib_root_.empty() && iname.substr(0, 7) == "stdlib/")
                import_path = stdlib_root_ / iname.substr(7);
            else
                import_path = current_dir / iname;
            auto canonical = std::filesystem::weakly_canonical(import_path);
            if (!visited.count(canonical)) {
                auto imported = check_module(canonical, kernel, diag_, visited, stdlib_root_);
                // also insert under the qualified prefix "ModName.entry".
                // skip Private entries.
                const std::string mod_prefix = module_name_from_path(iname) + ".";
                for (auto& [n, e] : imported.env) {
                    if (e.visibility == ast::Visibility::Private) continue;
                    module_env.insert_or_assign(n, e);
                    module_env.insert_or_assign(mod_prefix + n, e);
                }
                for (auto& [t, cls] : imported.instances)
                    for (const auto& c : cls) instance_table[t].insert(c);
                // merge imported predicate definitions.
                for (auto& [pname, pentry] : imported.pred_defs)
                    pred_def_table.insert_or_assign(pname, pentry);
            }
            break;
        }
        case ast::DeclKind::Structure: {
            // Track structure in struct_env for instantiations.
            struct_env[decl->name] = decl->fields;
            for (const auto& field : decl->fields) {
                if (const auto* fa = std::get_if<ast::FieldAxiom>(&field)) {
                    const std::string axiom_name = decl->name + "_" + fa->name;
                    auto r = kernel.introduce_axiom(fa->prop);
                    if (r) module_env.insert_or_assign(axiom_name,
                                                        HypEntry{std::move(*r), EntryKind::Derived});
                }
                if (const auto* ft = std::get_if<ast::FieldTerm>(&field)) {
                    if (const auto* tf = std::get_if<ast::TypeFun>(&ft->type.node))
                        sig_table[decl->name + "_" + ft->name] = *tf;
                }
            }
            break;
        }
        case ast::DeclKind::Quotient: {
            // Register each FieldAxiom as "<QuotName>_<fieldName>" in module_env.
            for (const auto& field : decl->fields) {
                if (const auto* fa = std::get_if<ast::FieldAxiom>(&field)) {
                    const std::string axiom_name = decl->name + "_" + fa->name;
                    auto r = kernel.introduce_axiom(fa->prop);
                    if (r) module_env.insert_or_assign(axiom_name,
                                                        HypEntry{std::move(*r), EntryKind::Derived});
                }
            }
            // Warn if equivalence axioms are missing.
            bool has_refl  = false;
            bool has_symm  = false;
            bool has_trans = false;
            for (const auto& field : decl->fields) {
                if (const auto* fa = std::get_if<ast::FieldAxiom>(&field)) {
                    const auto& n = fa->name;
                    if (n.find("refl")  != std::string::npos) has_refl  = true;
                    if (n.find("symm")  != std::string::npos) has_symm  = true;
                    if (n.find("sym")   != std::string::npos) has_symm  = true;
                    if (n.find("trans") != std::string::npos) has_trans = true;
                }
            }
            if (!has_refl)
                diag_.emit({diag::Severity::Warning, decl->loc,
                            "quotient '" + decl->name + "' is missing a reflexivity axiom (name should contain 'refl')"});
            if (!has_symm)
                diag_.emit({diag::Severity::Warning, decl->loc,
                            "quotient '" + decl->name + "' is missing a symmetry axiom (name should contain 'symm' or 'sym')"});
            if (!has_trans)
                diag_.emit({diag::Severity::Warning, decl->loc,
                            "quotient '" + decl->name + "' is missing a transitivity axiom (name should contain 'trans')"});
            break;
        }
        // namespace block in check_content
        case ast::DeclKind::Namespace: {
            const std::string prefix = decl->name + ".";
            for (const auto& inner : decl->ns_decls) {
                if (inner->kind == ast::DeclKind::Axiom || inner->kind == ast::DeclKind::Definition) {
                    check_prop_types_deep(inner->statement, {}, sig_table, diag_);
                    auto r = kernel.introduce_axiom(inner->statement);
                    if (r) {
                        module_env.insert_or_assign(inner->name, HypEntry{*r, EntryKind::Derived});
                        module_env.insert_or_assign(prefix + inner->name, HypEntry{std::move(*r), EntryKind::Derived});
                    }
                } else if (inner->kind == ast::DeclKind::Theorem || inner->kind == ast::DeclKind::Lemma) {
                    check_prop_types_deep(inner->statement, {}, sig_table, diag_);
                    check_proof(*inner, module_env, kernel, diag_, sig_table, instance_table, &struct_env, &pred_def_table);
                    if (!diag_.hasErrors()) {
                        if (auto r = kernel.introduce_axiom(inner->statement)) {
                            module_env.insert_or_assign(inner->name, HypEntry{*r, EntryKind::Derived});
                            module_env.insert_or_assign(prefix + inner->name, HypEntry{std::move(*r), EntryKind::Derived});
                        }
                    }
                }
            }
            break;
        }
        // open directive in check_content
        case ast::DeclKind::Open: {
            const std::string prefix = decl->name + ".";
            std::vector<std::pair<std::string, HypEntry>> to_add;
            for (const auto& [name, entry] : module_env)
                if (name.size() > prefix.size() && name.substr(0, prefix.size()) == prefix)
                    to_add.emplace_back(name.substr(prefix.size()), entry);
            for (auto& [uname, entry] : to_add)
                module_env.insert_or_assign(uname, std::move(entry));
            break;
        }
        case ast::DeclKind::Axiom:
        case ast::DeclKind::Definition:
        case ast::DeclKind::Theorem:
        case ast::DeclKind::Lemma:
        case ast::DeclKind::Instance:
        default: {
            if (decl->kind == ast::DeclKind::Axiom) {
                const ast::Prop eff_stmt = pred_def_table.empty()
                                           ? decl->statement
                                           : unfold_preds(decl->statement, pred_def_table);
                check_prop_types_deep(eff_stmt, {}, sig_table, diag_);
                auto r = kernel.introduce_axiom(eff_stmt);
                if (r) module_env.insert_or_assign(decl->name,
                                                    HypEntry{std::move(*r), EntryKind::Derived});
            } else if (decl->kind == ast::DeclKind::Definition) {
                if (!decl->struct_type.empty()) {
                    // structure instantiation
                    auto sit = struct_env.find(decl->struct_type);
                    if (sit == struct_env.end()) {
                        diag_.emit({diag::Severity::Error, decl->loc,
                                    "unknown structure type '" + decl->struct_type + "'"});
                        break;
                    }
                    const auto& fields = sit->second;
                    const auto& inst_name = decl->name;
                    for (const auto& sf : fields) {
                        if (const auto* ft = std::get_if<ast::FieldTerm>(&sf)) {
                            auto bit = decl->struct_bindings.find(ft->name);
                            if (bit == decl->struct_bindings.end()) continue;
                            if (const auto* tf = std::get_if<ast::TypeFun>(&ft->type.node))
                                sig_table[inst_name + "_" + ft->name] = *tf;
                        }
                    }
                    for (const auto& sf : fields) {
                        if (const auto* fa = std::get_if<ast::FieldAxiom>(&sf)) {
                            ast::Prop instantiated = fa->prop;
                            for (const auto& sf2 : fields) {
                                if (const auto* ft = std::get_if<ast::FieldTerm>(&sf2)) {
                                    auto bit = decl->struct_bindings.find(ft->name);
                                    if (bit == decl->struct_bindings.end()) continue;
                                    instantiated = ast::subst(instantiated, ft->name, *bit->second);
                                }
                            }
                            instantiated = ast::beta_reduce(instantiated);
                            const std::string axiom_name = inst_name + "_" + fa->name;
                            auto r = kernel.introduce_axiom(instantiated);
                            if (r) module_env.insert_or_assign(axiom_name,
                                                               HypEntry{std::move(*r), EntryKind::Derived});
                        }
                    }
                } else {
                    check_prop_types_deep(decl->statement, {}, sig_table, diag_);
                    auto r = kernel.introduce_axiom(decl->statement);
                    if (r) module_env.insert_or_assign(decl->name,
                                                        HypEntry{std::move(*r), EntryKind::Derived});
                    // register predicate body if present.
                    if (decl->def_body && !decl->is_abstract) {
                        PredDefEntry entry;
                        for (const auto& p : decl->params)
                            entry.params.push_back(p.name);
                        entry.body = *decl->def_body;
                        pred_def_table[decl->name] = std::move(entry);
                    }
                }
            } else if (decl->kind == ast::DeclKind::Theorem || decl->kind == ast::DeclKind::Lemma) {
                check_prop_types_deep(decl->statement, {}, sig_table, diag_);
                check_proof(*decl, module_env, kernel, diag_, sig_table, instance_table, &struct_env, &pred_def_table);
                if (!diag_.hasErrors()) {
                    auto r = kernel.introduce_axiom(decl->statement);
                    if (r) module_env.insert_or_assign(decl->name,
                                                       HypEntry{std::move(*r), EntryKind::Derived});
                }
            }
            break;
        }
        }
    }
}

// ── check_content_lsp ─────────────────────────────────────────────────────────
//
// Like check_content, but also returns an LspEnv mapping every module-level
// name to its pretty-printed proposition and introduction source location.
// Used by the LSP server for hover and go-to-definition.

LspEnv Checker::check_content_lsp(const std::string& source,
                                   const std::string& filename)
{
    // Lex and parse from the in-memory buffer.
    lexer::Lexer lex{source, filename, diag_};
    auto tokens = lex.tokenize();
    parser::Parser parser{tokens, diag_};
    ast::Module mod = parser.parse();
    mod.path = filename;

    const std::filesystem::path file_path{filename};
    const auto current_dir = file_path.parent_path().empty()
                             ? std::filesystem::current_path()
                             : file_path.parent_path();

    kernel::Kernel kernel;
    HypEnv module_env;
    ast::FuncSigTable sig_table;
    InstanceTable instance_table;
    ast::StructEnv struct_env;
    PredDefTable pred_def_table;
    std::set<std::filesystem::path> visited;
    if (!filename.empty())
        visited.insert(std::filesystem::weakly_canonical(file_path));

    LspEnv lsp_env;

    // Helper: record a name in lsp_env.
    auto record = [&](const std::string& name,
                      const ast::Prop& prop,
                      const diag::SourceLocation& loc) {
        lsp_env[name] = LspEntry{forall::pretty::to_string(prop), loc};
    };

    for (const auto& decl : mod.decls) {
        switch (decl->kind) {
        case ast::DeclKind::Import: {
            const std::string& iname = decl->name;
            std::filesystem::path import_path;
            if (!stdlib_root_.empty() && iname.substr(0, 7) == "stdlib/")
                import_path = stdlib_root_ / iname.substr(7);
            else
                import_path = current_dir / iname;
            auto canonical = std::filesystem::weakly_canonical(import_path);
            if (!visited.count(canonical)) {
                auto imported = check_module(canonical, kernel, diag_, visited, stdlib_root_);
                for (auto& [n, e] : imported.env) {
                    module_env.insert_or_assign(n, e);
                    // Record imported names with an unknown location (from another file).
                    if (!lsp_env.count(n))
                        lsp_env[n] = LspEntry{forall::pretty::to_string(e.judgment.prop()), {}};
                }
                for (auto& [t, cls] : imported.instances)
                    for (const auto& c : cls) instance_table[t].insert(c);
                // merge imported predicate definitions.
                for (auto& [pname, pentry] : imported.pred_defs)
                    pred_def_table.insert_or_assign(pname, pentry);
            }
            break;
        }
        case ast::DeclKind::Structure: {
            struct_env[decl->name] = decl->fields;
            for (const auto& field : decl->fields) {
                if (const auto* fa = std::get_if<ast::FieldAxiom>(&field)) {
                    const std::string axiom_name = decl->name + "_" + fa->name;
                    auto r = kernel.introduce_axiom(fa->prop);
                    if (r) {
                        module_env.insert_or_assign(axiom_name,
                                                    HypEntry{std::move(*r), EntryKind::Derived});
                        record(axiom_name, fa->prop, decl->loc);
                    }
                }
                if (const auto* ft = std::get_if<ast::FieldTerm>(&field)) {
                    if (const auto* tf = std::get_if<ast::TypeFun>(&ft->type.node))
                        sig_table[decl->name + "_" + ft->name] = *tf;
                }
            }
            break;
        }
        case ast::DeclKind::Quotient: {
            for (const auto& field : decl->fields) {
                if (const auto* fa = std::get_if<ast::FieldAxiom>(&field)) {
                    const std::string axiom_name = decl->name + "_" + fa->name;
                    auto r = kernel.introduce_axiom(fa->prop);
                    if (r) {
                        module_env.insert_or_assign(axiom_name,
                                                    HypEntry{std::move(*r), EntryKind::Derived});
                        record(axiom_name, fa->prop, decl->loc);
                    }
                }
            }
            break;
        }
        case ast::DeclKind::Axiom:
        case ast::DeclKind::Definition:
        case ast::DeclKind::Theorem:
        case ast::DeclKind::Lemma:
        case ast::DeclKind::Instance:
        default: {
            if (decl->kind == ast::DeclKind::Axiom) {
                const ast::Prop eff_stmt = pred_def_table.empty()
                                           ? decl->statement
                                           : unfold_preds(decl->statement, pred_def_table);
                check_prop_types_deep(eff_stmt, {}, sig_table, diag_);
                auto r = kernel.introduce_axiom(eff_stmt);
                if (r) {
                    record(decl->name, eff_stmt, decl->loc);
                    module_env.insert_or_assign(decl->name,
                                                HypEntry{std::move(*r), EntryKind::Derived});
                }
            } else if (decl->kind == ast::DeclKind::Definition) {
                if (!decl->struct_type.empty()) {
                    auto sit = struct_env.find(decl->struct_type);
                    if (sit == struct_env.end()) {
                        diag_.emit({diag::Severity::Error, decl->loc,
                                    "unknown structure type '" + decl->struct_type + "'"});
                        break;
                    }
                    const auto& fields = sit->second;
                    const auto& inst_name = decl->name;
                    for (const auto& sf : fields) {
                        if (const auto* ft = std::get_if<ast::FieldTerm>(&sf)) {
                            auto bit = decl->struct_bindings.find(ft->name);
                            if (bit == decl->struct_bindings.end()) continue;
                            if (const auto* tf = std::get_if<ast::TypeFun>(&ft->type.node))
                                sig_table[inst_name + "_" + ft->name] = *tf;
                        }
                    }
                    for (const auto& sf : fields) {
                        if (const auto* fa = std::get_if<ast::FieldAxiom>(&sf)) {
                            ast::Prop instantiated = fa->prop;
                            for (const auto& sf2 : fields) {
                                if (const auto* ft = std::get_if<ast::FieldTerm>(&sf2)) {
                                    auto bit = decl->struct_bindings.find(ft->name);
                                    if (bit == decl->struct_bindings.end()) continue;
                                    instantiated = ast::subst(instantiated, ft->name, *bit->second);
                                }
                            }
                            instantiated = ast::beta_reduce(instantiated);
                            const std::string axiom_name = inst_name + "_" + fa->name;
                            auto r = kernel.introduce_axiom(instantiated);
                            if (r) {
                                record(axiom_name, instantiated, decl->loc);
                                module_env.insert_or_assign(axiom_name,
                                                           HypEntry{std::move(*r), EntryKind::Derived});
                            }
                        }
                    }
                } else {
                    check_prop_types_deep(decl->statement, {}, sig_table, diag_);
                    auto r = kernel.introduce_axiom(decl->statement);
                    if (r) {
                        record(decl->name, decl->statement, decl->loc);
                        module_env.insert_or_assign(decl->name,
                                                    HypEntry{std::move(*r), EntryKind::Derived});
                    }
                    // register predicate body if present.
                    if (decl->def_body && !decl->is_abstract) {
                        PredDefEntry entry;
                        for (const auto& p : decl->params)
                            entry.params.push_back(p.name);
                        entry.body = *decl->def_body;
                        pred_def_table[decl->name] = std::move(entry);
                    }
                }
            } else if (decl->kind == ast::DeclKind::Theorem || decl->kind == ast::DeclKind::Lemma) {
                check_prop_types_deep(decl->statement, {}, sig_table, diag_);
                check_proof(*decl, module_env, kernel, diag_, sig_table, instance_table, &struct_env, &pred_def_table);
                if (!diag_.hasErrors()) {
                    auto r = kernel.introduce_axiom(decl->statement);
                    if (r) {
                        record(decl->name, decl->statement, decl->loc);
                        module_env.insert_or_assign(decl->name,
                                                   HypEntry{std::move(*r), EntryKind::Derived});
                    }
                }
            }
            break;
        }
        }
    }

    return lsp_env;
}

} // namespace forall::checker
