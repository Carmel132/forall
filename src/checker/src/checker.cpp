#include <forall/checker/checker.hpp>
#include <forall/kernel/kernel.hpp>
#include <forall/lexer/lexer.hpp>
#include <forall/parser/parser.hpp>
#include <forall/pretty/to_string.hpp>

#include <array>
#include <fstream>
#include <map>
#include <set>
#include <sstream>

namespace forall::checker {

Checker::Checker(diag::DiagnosticEngine& diag) : diag_{diag} {}

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
    // Used for the ∀-intro freshness check.
    template<typename F>
    void for_each_assumption(F&& f) const {
        for (const auto& frame : frames_)
            for (const auto& [name, entry] : frame)
                if (entry.kind == EntryKind::Assumption)
                    f(name, entry);
    }
};

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

// ── check_step (forward declaration for mutual recursion with CasesStep) ───────
bool check_step(const ast::Step& step,
                ScopeStack& env,
                kernel::Kernel& kernel,
                diag::DiagnosticEngine& diag);

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
                      diag::DiagnosticEngine& diag)
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
            check_step(*uptr, arm_env, kernel, diag);
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
    env.insert_or_assign(s.name, HypEntry{std::move(*result), EntryKind::Derived});
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
                       diag::DiagnosticEngine& diag)
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
        check_step(*uptr, sub_env, kernel, diag);
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

// ── check_step ─────────────────────────────────────────────────────────────────

bool check_step(const ast::Step& step,
                ScopeStack& env,
                kernel::Kernel& kernel,
                diag::DiagnosticEngine& diag)
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
        else if constexpr (std::is_same_v<T, ast::HaveStep>) {
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
                           "kernel rejected '" + s.name + "': " + r.error().message});
                return false;
            }
            env.insert_or_assign(s.name, HypEntry{std::move(*r), EntryKind::Derived});
            return true;
        }

        // then <prop> by <refs> [at <expr>]
        else if constexpr (std::is_same_v<T, ast::ThenStep>) {
            if (s.justification.empty()) {
                diag.emit({diag::Severity::Error, step.loc,
                           "'then' step requires a 'by' justification"});
                return false;
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
            return check_cases_step(s, step.loc, env, kernel, diag);
        }

        // obtain <name> from <ref>  case <var> [: T] , <hyp> : P => <steps...>
        else if constexpr (std::is_same_v<T, ast::ObtainStep>) {
            return check_obtain_step(s, step.loc, env, kernel, diag);
        }

        return true;
    }, step.node);
}

// ── check_proof ────────────────────────────────────────────────────────────────

void check_proof(const ast::Decl& decl,
                 const HypEnv& module_env,
                 kernel::Kernel& kernel,
                 diag::DiagnosticEngine& diag)
{
    if (!decl.proof) {
        diag.emit({diag::Severity::Error, decl.loc,
                   "theorem '" + decl.name + "' has no proof block"});
        return;
    }

    ScopeStack env{module_env};

    // Track the last concluding step — ThenStep, CasesStep, or ObtainStep.
    enum class LastKind { None, Then, Cases, Obtain };
    const ast::Step* last_concluding = nullptr;
    LastKind         last_kind       = LastKind::None;
    bool             had_step_errors = false;

    for (const auto& step : decl.proof->steps) {
        const auto snap = diag.diagnostics().size();
        check_step(step, env, kernel, diag);
        const auto& all = diag.diagnostics();
        for (auto i = snap; i < all.size(); ++i) {
            if (all[i].severity == diag::Severity::Error) {
                had_step_errors = true;
                break;
            }
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
    }

    // Only validate the conclusion when all steps passed; cascading errors on
    // a broken proof are more noise than signal.
    if (!had_step_errors) {
        if (last_kind == LastKind::None) {
            diag.emit({diag::Severity::Error, decl.loc,
                       "proof of '" + decl.name + "' has no concluding 'then' step"});
        } else if (last_kind == LastKind::Then) {
            const auto& ts = std::get<ast::ThenStep>(last_concluding->node);
            if (ts.prop != decl.statement)
                diag.emit({diag::Severity::Error, last_concluding->loc,
                           "proof concludes with `" + forall::pretty::to_string(ts.prop)
                           + "`, expected `" + forall::pretty::to_string(decl.statement) + "`"});
        } else if (last_kind == LastKind::Cases) {
            const auto& cs = std::get<ast::CasesStep>(last_concluding->node);
            const auto* it = env.find(cs.name);
            if (it && !(it->judgment.prop() == decl.statement))
                diag.emit({diag::Severity::Error, last_concluding->loc,
                           "proof concludes with wrong proposition"});
        } else { // Obtain
            const auto& os = std::get<ast::ObtainStep>(last_concluding->node);
            const auto* it = env.find(os.name);
            if (it && !(it->judgment.prop() == decl.statement))
                diag.emit({diag::Severity::Error, last_concluding->loc,
                           "proof concludes with wrong proposition"});
        }
    }
}

// ── check_module ───────────────────────────────────────────────────────────────
//
// Parses and validates a single .forall file, returning the module-level
// HypEnv (axioms + proved lemmas/theorems) so callers can import it.
// visited tracks canonical paths to prevent circular imports.

HypEnv check_module(const std::filesystem::path& path,
                    kernel::Kernel& kernel,
                    diag::DiagnosticEngine& diag,
                    std::set<std::filesystem::path>& visited)
{
    visited.insert(std::filesystem::weakly_canonical(path));

    std::ifstream file{path};
    if (!file) {
        diag.emit({diag::Severity::Error, {}, "cannot open file: " + path.string()});
        return {};
    }
    std::ostringstream buf;
    buf << file.rdbuf();

    lexer::Lexer lex{buf.str(), path.string(), diag};
    auto tokens = lex.tokenize();
    if (diag.hasErrors()) return {};

    parser::Parser parser{tokens, diag};
    ast::Module mod = parser.parse();
    mod.path = path.string();
    if (diag.hasErrors()) return {};

    HypEnv module_env;
    const auto current_dir = path.parent_path();

    for (const auto& decl : mod.decls) {
        switch (decl->kind) {

        case ast::DeclKind::Axiom: {
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
            const auto snapshot = diag.diagnostics().size();
            check_proof(*decl, module_env, kernel, diag);
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
            auto import_path = current_dir / decl->name;
            auto canonical   = std::filesystem::weakly_canonical(import_path);
            if (!visited.count(canonical)) {
                auto imported = check_module(canonical, kernel, diag, visited);
                for (auto& [name, entry] : imported)
                    module_env.insert_or_assign(name, entry);
            }
            break;
        }

        case ast::DeclKind::Definition: {
            auto r = kernel.introduce_axiom(decl->statement);
            if (!r)
                diag.emit({diag::Severity::Error, decl->loc,
                            "invalid definition: " + r.error().message});
            else
                module_env.insert_or_assign(decl->name,
                                            HypEntry{std::move(*r), EntryKind::Derived});
            break;
        }
        }
    }
    return module_env;
}

} // namespace

// ── Checker::check ─────────────────────────────────────────────────────────────

void Checker::check(const std::filesystem::path& path) {
    kernel::Kernel kernel;
    std::set<std::filesystem::path> visited;
    check_module(path, kernel, diag_, visited);
}

} // namespace forall::checker
