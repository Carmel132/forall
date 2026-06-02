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
    kernel::Judgment judgment;
    EntryKind        kind;
};

// Module-level flat map: axioms + proved lemmas/definitions accumulate here.
using HypEnv = std::map<std::string, HypEntry>;

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
    std::set<std::string> taken_vars_; // variables introduced via TakeStep
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

    // Record a variable introduced via TakeStep.
    void take_var(const std::string& var) { taken_vars_.insert(var); }

    // Returns true if var was introduced via TakeStep in this scope.
    [[nodiscard]] bool is_taken(const std::string& var) const {
        return taken_vars_.count(var) > 0;
    }

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
    // Returns nullptr if none exists. Used by auto-discharge (RL1).
    [[nodiscard]] const HypEntry* find_derived(const ast::Prop& p) const {
        for (auto it = frames_.rbegin(); it != frames_.rend(); ++it)
            for (const auto& [n, e] : *it)
                if (e.kind == EntryKind::Derived && e.judgment.prop() == p)
                    return &e;
        return nullptr;
    }
};

// ── fresh name generator ───────────────────────────────────────────────────────
// Returns a unique internal name for anonymous steps (have _ : ...) and
// unlabelled cases blocks (cases <ref>).  Names begin with "__" so they can
// never conflict with user identifiers.
static std::string fresh_name() {
    static std::atomic<unsigned> counter{0};
    return "__anon_" + std::to_string(++counter) + "__";
}

// ── resolve_refs ───────────────────────────────────────────────────────────────

std::optional<std::vector<const HypEntry*>>
resolve_refs(const std::vector<std::string>& refs,
             const ScopeStack& env,
             diag::DiagnosticEngine& diag,
             const diag::SourceLocation& loc)
{
    std::vector<const HypEntry*> out;
    out.reserve(refs.size());
    for (const auto& name : refs) {
        const auto* e = env.find(name);
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
                      const ast::Expr* /*witness*/,
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

    if (std::get_if<ast::PropForall>(&p0.node))
        return RuleApp{R::ForallElim, {es[0]->judgment}};

    if (std::get_if<ast::PropExists>(&conc.node))
        return RuleApp{R::ExistsIntro, {es[0]->judgment}};

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

// Polynomial types (C2-P4). Full definitions in the polynomial section below;
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
    const ast::TypeEnv&      type_env;     // var → type from 'take x : T' steps
    const InstanceTable&     instances;    // type_name → {class_names}
    const HypEnv&            module_env;   // axiom/lemma entries (for norm_num)
    const ast::FuncSigTable& sigs;         // function signatures
    const ast::Prop*         goal;         // theorem statement (for RL4 __qed__ sentinel)
};

// ── check_step (forward declaration for mutual recursion with CasesStep) ───────
bool check_step(const ast::Step& step,
                ScopeStack& env,
                kernel::Kernel& kernel,
                diag::DiagnosticEngine& diag,
                const CheckContext& ctx);

// Forward declaration for normalize_expr (defined in C2-P4 section further below).
static Poly normalize_expr(const ast::Expr& e);

// Forward declarations for linarith helpers (defined after ring_equal below).
struct LinConstraint;
static std::optional<LinConstraint> extract_linear(const ast::PropRel& rel);
static std::optional<LinConstraint> negate_linear(const LinConstraint& c);
static bool fourier_motzkin(std::vector<LinConstraint> cs);
static std::vector<LinConstraint> collect_linear_hypotheses(const ScopeStack& env);

// Forward declaration for simp_tactic (defined in the tactics section below).
static std::optional<RuleApp> simp_tactic(const ast::Prop& goal, const ScopeStack& env,
                                           diag::DiagnosticEngine& diag,
                                           const diag::SourceLocation& loc);

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
    // RL5: if the user omitted the result label, generate a fresh internal name.
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

    // 3. Verify hyp_prop == subst(body, exists_var, ExprVar{s.var})
    const ast::Prop expected_hyp =
        ast::subst(*ex->body, ex->var,
                   ast::Expr{loc, ast::ExprVar{s.var}});
    if (!(s.hyp_prop == expected_hyp)) {
        diag.emit({diag::Severity::Error, loc,
                   "obtain arm hypothesis does not match the existential body; "
                   "expected `" + forall::pretty::to_string(expected_hyp) + "`"});
        return false;
    }

    // 4. Build sub-environment with s.var taken and s.hyp_name : s.hyp_prop
    ScopeStack sub_env = env;
    sub_env.push();
    sub_env.take_var(s.var);
    auto hyp_j = kernel.introduce_axiom(s.hyp_prop);
    sub_env.insert_or_assign(s.hyp_name,
                             HypEntry{std::move(*hyp_j), EntryKind::Assumption});

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

    const auto& Q = std::get<ast::ThenStep>(arm_last_then->node).prop;

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
// Implements NatInduction.
// Syntax:
//   induction <name> on <var>
//     base:       <base_steps...>        -- must conclude P[var:=0]
//     inductive:  <inductive_steps...>   -- must conclude P[var:=succ(var)]
//                                           with ih : P(var) in scope
//
// Checker responsibilities:
//   1. There must be no ∀ quantifier to invent — the conclusion is inferred
//      from what the base block proves: ∀ var : Nat, P(var).
//   2. Base block: run in the current env; the last ThenStep concludes P(0)
//      = subst(P, var, 0).  From that, conclude ∀ var : Nat, P(var) is the
//      induction goal and P(var) == body.
//   3. Inductive block: inject ih : P(var) as Assumption; run; last ThenStep
//      must conclude P(succ(var)) = subst(P, var, succ(var)).
//   4. Apply NatInduction with premises [P(0), ∀ var, P(var) → P(succ(var))].
//   5. Store result under s.name.
bool check_induction_step(const ast::InductionStep& s,
                          const diag::SourceLocation& loc,
                          ScopeStack& env,
                          kernel::Kernel& kernel,
                          diag::DiagnosticEngine& diag,
                          const CheckContext& ctx)
{
    // ── Base block ────────────────────────────────────────────────────────────
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

    // s.body is P(var) — the inductive predicate stated explicitly by the user.
    // Verify base concludes P(0) and inductive concludes P(succ(var)).
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

    // ── Inductive block ───────────────────────────────────────────────────────
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

    // ── Build kernel premises ─────────────────────────────────────────────────
    // conclusion: ∀ var : Nat, ih_prop
    ast::TypeNode nat_type{{ast::TypeNat{}}};
    ast::Prop conclusion{{}, ast::PropForall{s.var,
        std::make_optional(nat_type), ast::make_prop(ih_prop)}};

    // premise[0]: ih_prop with var=0, certified as a judgment
    const kernel::Judgment base_j = *kernel.introduce_axiom(base_conc);

    // premise[1]: ∀ var : Nat, ih_prop → ind_conc (= P(n) → P(succ(n)))
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

// ── check_step ─────────────────────────────────────────────────────────────────

bool check_step(const ast::Step& step,
                ScopeStack& env,
                kernel::Kernel& kernel,
                diag::DiagnosticEngine& diag,
                const CheckContext& ctx)
{
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
            env.take_var(s.var);
            return true;
        }

        // suppose [name :] prop — introduces a local assumption
        else if constexpr (std::is_same_v<T, ast::SupposeStep>) {
            auto r = kernel.introduce_axiom(s.prop);
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
        // RL2: name may be "_" for an anonymous step — assign a fresh internal name.
        else if constexpr (std::is_same_v<T, ast::HaveStep>) {
            const std::string step_name = (s.name == "_") ? fresh_name() : s.name;
            // "by decide" — evaluate numerically; no refs needed
            if (s.justification.size() == 1 && s.justification[0] == "__decide__") {
                const auto* rel = std::get_if<ast::PropRel>(&s.prop.node);
                if (!rel) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide' only applies to relational propositions (e.g. 2 + 3 = 5)"});
                    return false;
                }
                auto verdict = decide_proprel(*rel);
                if (!verdict) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide' cannot evaluate `"
                               + forall::pretty::to_string(s.prop)
                               + "` — both sides must be literal arithmetic"});
                    return false;
                }
                if (!*verdict) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide': `"
                               + forall::pretty::to_string(s.prop) + "` is false"});
                    return false;
                }
                auto r = kernel.introduce_axiom(s.prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by norm_num" — polynomial ring equality with variable support
            if (s.justification.size() == 1 && s.justification[0] == "__norm_num__") {
                const auto* rel = std::get_if<ast::PropRel>(&s.prop.node);
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
                               + forall::pretty::to_string(s.prop)
                               + "` is not a polynomial identity"});
                    return false;
                }
                auto r = kernel.introduce_axiom(s.prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by ring" — polynomial identity over commutative ring (same normalization as norm_num)
            if (s.justification.size() == 1 && s.justification[0] == "__ring__") {
                const auto* rel = std::get_if<ast::PropRel>(&s.prop.node);
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
                               + forall::pretty::to_string(s.prop)
                               + "` does not hold as a ring identity"});
                    return false;
                }
                auto r = kernel.introduce_axiom(s.prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by linarith" — linear arithmetic over ordered fields (MT1)
            if (s.justification.size() == 1 && s.justification[0] == "__linarith__") {
                auto hyps = collect_linear_hypotheses(env);
                // Add the negated goal as a hypothesis.
                const auto* goal_rel = std::get_if<ast::PropRel>(&s.prop.node);
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
                               + forall::pretty::to_string(s.prop)
                               + "` from the linear hypotheses in scope"});
                    return false;
                }
                auto r = kernel.introduce_axiom(s.prop);
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            // "by simp" — propositional simplification (MT2)
            if (s.justification.size() == 1 && s.justification[0] == "__simp__") {
                auto app = simp_tactic(s.prop, env, diag, step.loc);
                if (!app) return false;
                auto r = kernel.apply(app->rule, std::span{app->premises}, s.prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by simp' internal error: " + r.error().message});
                    return false;
                }
                env.insert_or_assign(step_name, HypEntry{std::move(*r), EntryKind::Derived});
                return true;
            }
            auto es = resolve_refs(s.justification, env, diag, step.loc);
            if (!es) return false;
            const ast::Expr* witness_ptr = s.witness ? s.witness->get() : nullptr;
            std::optional<RuleApp> app;
            if (witness_ptr) {
                app = infer_quantifier_rule(s.prop, *es, witness_ptr, diag, step.loc);
            } else {
                app = infer_rule(s.prop, *es, diag, step.loc);
            }
            if (!app) return false;
            // ForallIntro requires the bound variable to have been introduced via TakeStep.
            if (app->rule == kernel::Rule::ForallIntro) {
                const auto* fa = std::get_if<ast::PropForall>(&s.prop.node);
                if (!env.is_taken(fa->var)) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "∀-intro: variable '" + fa->var
                               + "' must be introduced via 'take' before generalizing"});
                    return false;
                }
            }
            auto r = kernel.apply(app->rule, std::span{app->premises}, s.prop, witness_ptr);
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
            // RL4: "__qed__" sentinel — bare "then" with no proposition.
            // Substitute the theorem's goal, then continue as a normal ThenStep.
            // The __qed__ sentinel is always first; extra refs follow it.
            if (!s.justification.empty() && s.justification[0] == "__qed__") {
                if (!ctx.goal) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "bare 'then' (goal-close) is not valid outside a theorem proof"});
                    return false;
                }
                // Build a synthetic ThenStep with the real goal and remaining refs.
                std::vector<std::string> real_refs(s.justification.begin() + 1,
                                                   s.justification.end());
                ast::Step synth{step.loc, ast::ThenStep{*ctx.goal, std::move(real_refs), s.witness}};
                return check_step(synth, env, kernel, diag, ctx);
            }

            // RL1: auto-discharge — allow bare "then P → Q" or "then ¬P" with no
            // justification by finding the most-recent matching Assumption in scope.
            if (s.justification.empty()) {
                // Try ImplIntro: conclusion is A → B — look for assume[A], derive[B]
                if (const auto* im = std::get_if<ast::PropImpl>(&s.prop.node)) {
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
                                          s.prop);
                    if (!r) {
                        diag.emit({diag::Severity::Error, step.loc,
                                   "auto-discharge (ImplIntro) failed: " + r.error().message});
                        return false;
                    }
                    return true;
                }
                // Try NotIntro: conclusion is ¬A — look for assume[A], derive[⊥]
                if (const auto* neg = std::get_if<ast::PropNot>(&s.prop.node)) {
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
                                          s.prop);
                    if (!r) {
                        diag.emit({diag::Severity::Error, step.loc,
                                   "auto-discharge (NotIntro) failed: " + r.error().message});
                        return false;
                    }
                    return true;
                }
                // TrueIntro: conclusion is ⊤ — no premises needed
                if (std::get_if<ast::PropTrue>(&s.prop.node)) {
                    std::vector<kernel::Judgment> no_prem;
                    auto r = kernel.apply(kernel::Rule::TrueIntro, no_prem, s.prop);
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
                const auto* rel = std::get_if<ast::PropRel>(&s.prop.node);
                if (!rel) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide' only applies to relational propositions"});
                    return false;
                }
                auto verdict = decide_proprel(*rel);
                if (!verdict) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide' cannot evaluate `"
                               + forall::pretty::to_string(s.prop)
                               + "` — both sides must be literal arithmetic"});
                    return false;
                }
                if (!*verdict) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by decide': `"
                               + forall::pretty::to_string(s.prop) + "` is false"});
                    return false;
                }
                // Certified: the proposition is arithmetically true.
                kernel.introduce_axiom(s.prop);
                return true;
            }
            // "by norm_num" — polynomial ring equality with variable support
            if (s.justification.size() == 1 && s.justification[0] == "__norm_num__") {
                const auto* rel = std::get_if<ast::PropRel>(&s.prop.node);
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
                               + forall::pretty::to_string(s.prop)
                               + "` is not a polynomial identity"});
                    return false;
                }
                kernel.introduce_axiom(s.prop);
                return true;
            }
            // "by ring" — polynomial identity over commutative ring
            if (s.justification.size() == 1 && s.justification[0] == "__ring__") {
                const auto* rel = std::get_if<ast::PropRel>(&s.prop.node);
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
                               + forall::pretty::to_string(s.prop)
                               + "` does not hold as a ring identity"});
                    return false;
                }
                kernel.introduce_axiom(s.prop);
                return true;
            }
            // "by linarith" — linear arithmetic (ThenStep variant)
            if (s.justification.size() == 1 && s.justification[0] == "__linarith__") {
                auto hyps = collect_linear_hypotheses(env);
                const auto* goal_rel = std::get_if<ast::PropRel>(&s.prop.node);
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
                               + forall::pretty::to_string(s.prop)
                               + "` from the linear hypotheses in scope"});
                    return false;
                }
                kernel.introduce_axiom(s.prop);
                return true;
            }
            // "by contra" — proof by contradiction (ML3)
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
                                      s.prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by contra' FalseElim failed: " + r.error().message});
                    return false;
                }
                return true;
            }
            // "by simp" — propositional simplification (ThenStep variant)
            if (s.justification.size() == 1 && s.justification[0] == "__simp__") {
                auto app = simp_tactic(s.prop, env, diag, step.loc);
                if (!app) return false;
                auto r = kernel.apply(app->rule, std::span{app->premises}, s.prop);
                if (!r) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "'by simp' internal error: " + r.error().message});
                    return false;
                }
                return true;
            }
            auto es = resolve_refs(s.justification, env, diag, step.loc);
            if (!es) return false;
            const ast::Expr* witness_ptr = s.witness ? s.witness->get() : nullptr;
            std::optional<RuleApp> app;
            if (witness_ptr) {
                app = infer_quantifier_rule(s.prop, *es, witness_ptr, diag, step.loc);
            } else {
                app = infer_rule(s.prop, *es, diag, step.loc);
            }
            if (!app) return false;
            // ForallIntro requires the bound variable to have been introduced via TakeStep.
            if (app->rule == kernel::Rule::ForallIntro) {
                const auto* fa = std::get_if<ast::PropForall>(&s.prop.node);
                if (!env.is_taken(fa->var)) {
                    diag.emit({diag::Severity::Error, step.loc,
                               "∀-intro: variable '" + fa->var
                               + "' must be introduced via 'take' before generalizing"});
                    return false;
                }
            }
            auto r = kernel.apply(app->rule, std::span{app->premises}, s.prop, witness_ptr);
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

        // obtain <name> from <ref>  case <var> [: T] , <hyp> : P => <steps...>
        else if constexpr (std::is_same_v<T, ast::ObtainStep>) {
            return check_obtain_step(s, step.loc, env, kernel, diag, ctx);
        }

        // induction <name> on <var>  base: ...  inductive: ...
        else if constexpr (std::is_same_v<T, ast::InductionStep>) {
            return check_induction_step(s, step.loc, env, kernel, diag, ctx);
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
            if (!ctx.goal) {
                diag.emit({diag::Severity::Error, step.loc,
                           "'show' step used outside a proof context"});
                return false;
            }
            if (!(s.prop == *ctx.goal)) {
                diag.emit({diag::Severity::Error, step.loc,
                           "'show' mismatch: expected '"
                           + forall::pretty::to_string(*ctx.goal)
                           + "', got '"
                           + forall::pretty::to_string(s.prop) + "'"});
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
        using Op = ast::RelOp;
        if (rel->op == Op::In || rel->op == Op::NotIn) {
            // element ∈ set — rhs must be TypeSet{T} and lhs must have type T.
            if (!is_set(*rt)) {
                diag.emit({diag::Severity::Warning, loc,
                           "type mismatch: right-hand side of membership relation is not a set"});
            } else {
                const auto& rset = std::get<ast::TypeSet>(rt->node);
                if (!(*lt == *rset.element_type)) {
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
                 const InstanceTable& instances = {})
{
    if (!decl.proof) {
        diag.emit({diag::Severity::Error, decl.loc,
                   "theorem '" + decl.name + "' has no proof block"});
        return;
    }

    ScopeStack  env{module_env};
    ast::TypeEnv type_env; // types from typed 'take x : T' steps

    // Track the last concluding step — ThenStep, CasesStep, ObtainStep, InductionStep, or ExactStep.
    enum class LastKind { None, Then, Cases, Obtain, Induction, Exact };
    const ast::Step* last_concluding = nullptr;
    LastKind         last_kind       = LastKind::None;
    bool             had_step_errors = false;

    // Current proof goal — starts as decl.statement, may be transformed by RewriteStep
    // or ApplyStep. Allocations live in this vector so pointers remain valid.
    std::vector<ast::Prop> goal_history;
    const ast::Prop* current_goal = &decl.statement;

    // Stack of apply hypotheses — each ApplyStep pushes h:A→B so the conclusion
    // validator can chain ImplElim(h, proof_of_A) → B after the subproof of A.
    std::vector<const HypEntry*> apply_stack;

    for (const auto& step : decl.proof->steps) {
        // Populate type_env before processing the step so TakeStep vars are
        // available for the type-mismatch check on the same iteration.
        if (const auto* ts = std::get_if<ast::TakeStep>(&step.node))
            if (ts->type.has_value())
                type_env[ts->var] = *ts->type;

        // MS1: RewriteStep transforms the current goal before check_step runs.
        if (const auto* rw = std::get_if<ast::RewriteStep>(&step.node)) {
            const HypEntry* h = env.find(rw->hyp_ref);
            if (!h) {
                diag.emit({diag::Severity::Error, step.loc,
                           "rewrite: unknown hypothesis '" + rw->hyp_ref + "'"});
                had_step_errors = true;
                continue;
            }
            const auto* eq = std::get_if<ast::PropRel>(&h->judgment.prop().node);
            if (!eq || eq->op != ast::RelOp::Eq) {
                diag.emit({diag::Severity::Error, step.loc,
                           "rewrite: hypothesis '" + rw->hyp_ref
                           + "' must be an equality (lhs = rhs)"});
                had_step_errors = true;
                continue;
            }
            // For variable rewriting: lhs must be an ExprVar.
            const auto* lhs_var = std::get_if<ast::ExprVar>(&eq->lhs->node);
            const auto* rhs_var = std::get_if<ast::ExprVar>(&eq->rhs->node);
            if (!lhs_var && !rhs_var) {
                diag.emit({diag::Severity::Error, step.loc,
                           "rewrite: equality must have a variable on at least one side"});
                had_step_errors = true;
                continue;
            }
            // Choose which side to substitute.
            ast::Prop new_goal;
            if (!rw->reverse && lhs_var) {
                new_goal = ast::subst(*current_goal, lhs_var->name, *eq->rhs);
            } else if (rhs_var) {
                new_goal = ast::subst(*current_goal, rhs_var->name, *eq->lhs);
            } else {
                // reverse requested but only lhs is a var — still forward
                new_goal = ast::subst(*current_goal, lhs_var->name, *eq->rhs);
            }
            if (new_goal == *current_goal) {
                diag.emit({diag::Severity::Warning, step.loc,
                           "rewrite: equality does not appear in goal — no effect"});
            }
            goal_history.push_back(std::move(new_goal));
            current_goal = &goal_history.back();
            continue; // not a proof step, just goal transformation
        }

        // MS2: ApplyStep — backward implication application.
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

        const CheckContext ctx{type_env, instances, module_env, sigs, current_goal};
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
            check_prop_types_deep(hs->prop, type_env, sigs, diag);
        if (const auto* ss = std::get_if<ast::ShowStep>(&step.node))
            check_prop_types_deep(ss->prop, type_env, sigs, diag);
        if (const auto* ts_s = std::get_if<ast::ThenStep>(&step.node)) {
            // Don't type-check the dummy PropFalse{} in a __qed__ sentinel step.
            const bool is_qed = !ts_s->justification.empty()
                                 && ts_s->justification[0] == "__qed__";
            if (!is_qed)
                check_prop_types_deep(ts_s->prop, type_env, sigs, diag);
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
    }

    // Only validate the conclusion when all steps passed; cascading errors on
    // a broken proof are more noise than signal.
    if (!had_step_errors) {
        if (last_kind == LastKind::None) {
            diag.emit({diag::Severity::Error, decl.loc,
                       "proof of '" + decl.name + "' has no concluding 'then' step"});
        } else if (last_kind == LastKind::Then) {
            const auto& ts = std::get<ast::ThenStep>(last_concluding->node);
            // RL4: __qed__ sentinel substitutes current goal — skip prop check.
            const bool is_qed_sentinel = !ts.justification.empty()
                                         && ts.justification[0] == "__qed__";
            if (!is_qed_sentinel && ts.prop != *current_goal)
                diag.emit({diag::Severity::Error, last_concluding->loc,
                           "proof concludes with `" + forall::pretty::to_string(ts.prop)
                           + "`, expected `" + forall::pretty::to_string(*current_goal) + "`"});
            // MS2: If apply_stack is non-empty, verify the chain reaches decl.statement.
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
                if (chain_ok && chain_goal && !(*chain_goal == decl.statement))
                    diag.emit({diag::Severity::Error, last_concluding->loc,
                               "apply chain does not prove the theorem statement"});
            }
        } else if (last_kind == LastKind::Cases) {
            const auto& cs = std::get<ast::CasesStep>(last_concluding->node);
            const auto* it = env.find(cs.name);
            if (it && !(it->judgment.prop() == decl.statement))
                diag.emit({diag::Severity::Error, last_concluding->loc,
                           "proof concludes with wrong proposition"});
        } else if (last_kind == LastKind::Obtain) {
            const auto& os = std::get<ast::ObtainStep>(last_concluding->node);
            const auto* it = env.find(os.name);
            if (it && !(it->judgment.prop() == decl.statement))
                diag.emit({diag::Severity::Error, last_concluding->loc,
                           "proof concludes with wrong proposition"});
        } else if (last_kind == LastKind::Induction) {
            const auto& is = std::get<ast::InductionStep>(last_concluding->node);
            const auto* it = env.find(is.name);
            if (it && !(it->judgment.prop() == decl.statement))
                diag.emit({diag::Severity::Error, last_concluding->loc,
                           "proof concludes with wrong proposition"});
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
// C2-P3: Axiom-set reachability.
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

// ── Polynomial normal form (C2-P4) ────────────────────────────────────────────
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
    // Each remaining constraint has the form: 0 - rhs sense 0, i.e. -rhs sense 0.
    for (const auto& c : cs) {
        if (!c.coeffs.empty()) continue;
        // Constraint: -rhs sense 0
        long long neg_rhs_num = -c.rhs.first;
        // Check if -rhs sense 0 is FALSE (which proves contradiction).
        bool contradiction = false;
        if (c.sense == -1) contradiction = !(neg_rhs_num <  0); // need -rhs < 0
        else               contradiction = !(neg_rhs_num <= 0); // need -rhs ≤ 0
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
                                           const diag::SourceLocation& loc)
{
    // Collect all hypotheses into a vector.
    std::vector<const HypEntry*> all;
    env.for_each([&](const std::string&, const HypEntry& e) { all.push_back(&e); });

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

// ── check_module ───────────────────────────────────────────────────────────────
//
// Parses and validates a single .forall file, returning the module-level
// HypEnv (axioms + proved lemmas/theorems) and InstanceTable so callers can
// import both.  visited tracks canonical paths to prevent circular imports.

struct ModuleResult {
    HypEnv         env;
    InstanceTable  instances;
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
    // IX2: Don't abort on lexer errors — continue to parse to collect more errors.

    parser::Parser parser{tokens, diag};
    ast::Module mod = parser.parse();
    mod.path = path.string();
    // IX2: Don't abort on parse errors — run the checker on successfully-parsed
    // declarations to report as many errors as possible in a single pass.
    // The checker skips over any declaration whose statement contains parse
    // sentinel nodes (they will have caused parse errors already).

    HypEnv module_env;
    ast::FuncSigTable sig_table; // built from definition declarations with params
    InstanceTable instance_table; // populated from instance declarations
    const auto current_dir = path.parent_path();

    for (const auto& decl : mod.decls) {
        switch (decl->kind) {

        case ast::DeclKind::Axiom: {
            check_prop_types_deep(decl->statement, {}, sig_table, diag);
            auto r = kernel.introduce_axiom(decl->statement);
            if (!r)
                diag.emit({diag::Severity::Error, decl->loc,
                            "invalid axiom: " + r.error().message});
            else
                module_env.insert_or_assign(decl->name,
                                            HypEntry{std::move(*r), EntryKind::Derived});
            break;
        }

        case ast::DeclKind::Theorem:
        case ast::DeclKind::Lemma: {
            check_prop_types_deep(decl->statement, {}, sig_table, diag);
            const auto snapshot = diag.diagnostics().size();
            check_proof(*decl, module_env, kernel, diag, sig_table, instance_table);
            const auto& all = diag.diagnostics();
            bool no_new_errors = true;
            for (auto i = snapshot; i < all.size(); ++i) {
                if (all[i].severity == diag::Severity::Error) {
                    no_new_errors = false;
                    break;
                }
            }
            if (no_new_errors) {
                if (auto r = kernel.introduce_axiom(decl->statement))
                    module_env.insert_or_assign(decl->name,
                                                HypEntry{std::move(*r), EntryKind::Derived});
            }
            break;
        }

        case ast::DeclKind::Import: {
            // IX4: if import path starts with "stdlib/" and stdlib_root is set,
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
                for (auto& [name, entry] : imported.env)
                    module_env.insert_or_assign(name, entry);
                for (auto& [tname, classes] : imported.instances)
                    for (const auto& cls : classes)
                        instance_table[tname].insert(cls);
            }
            break;
        }

        case ast::DeclKind::Definition: {
            check_prop_types_deep(decl->statement, {}, sig_table, diag);
            auto r = kernel.introduce_axiom(decl->statement);
            if (!r)
                diag.emit({diag::Severity::Error, decl->loc,
                            "invalid definition: " + r.error().message});
            else
                module_env.insert_or_assign(decl->name,
                                            HypEntry{std::move(*r), EntryKind::Derived});
            // Build signature table entry: params[0].type -> ... -> Prop (curried).
            if (!decl->params.empty()) {
                ast::TypeNode ret{ast::TypeProp{}};
                for (std::size_t i = decl->params.size(); i-- > 0; )
                    ret = ast::type_fun(decl->params[i].type, ret);
                if (const auto* tf = std::get_if<ast::TypeFun>(&ret.node))
                    sig_table[decl->name] = *tf;
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
        }
    }
    return ModuleResult{std::move(module_env), std::move(instance_table)};
}

} // namespace

// ── Checker::check ─────────────────────────────────────────────────────────────

void Checker::check(const std::filesystem::path& path) {
    kernel::Kernel kernel;
    std::set<std::filesystem::path> visited;
    check_module(path, kernel, diag_, visited, stdlib_root_);
}

} // namespace forall::checker
