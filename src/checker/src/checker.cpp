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

// Maps hypothesis labels to their certified judgments.
using HypEnv = std::map<std::string, HypEntry>;

// ── resolve_refs ───────────────────────────────────────────────────────────────

std::optional<std::vector<const HypEntry*>>
resolve_refs(const std::vector<std::string>& refs,
             const HypEnv& env,
             diag::DiagnosticEngine& diag,
             const diag::SourceLocation& loc)
{
    std::vector<const HypEntry*> out;
    out.reserve(refs.size());
    for (const auto& name : refs) {
        auto it = env.find(name);
        if (it == env.end()) {
            diag.emit({diag::Severity::Error, loc,
                       "unknown hypothesis '" + name + "'"});
            return std::nullopt;
        }
        out.push_back(&it->second);
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

// ── check_step (forward declaration for mutual recursion with CasesStep) ───────
bool check_step(const ast::Step& step,
                HypEnv& env,
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
                      HypEnv& env,
                      kernel::Kernel& kernel,
                      diag::DiagnosticEngine& diag)
{
    // 1. Look up the disjunction
    auto disj_it = env.find(s.disjunct_ref);
    if (disj_it == env.end()) {
        diag.emit({diag::Severity::Error, loc,
                   "unknown hypothesis '" + s.disjunct_ref + "'"});
        return false;
    }
    const auto* disj = std::get_if<ast::PropOr>(&disj_it->second.judgment.prop().node);
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

        // Sub-environment for this arm
        HypEnv arm_env = env;
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
        disj_it->second.judgment,
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

// ── check_step ─────────────────────────────────────────────────────────────────

bool check_step(const ast::Step& step,
                HypEnv& env,
                kernel::Kernel& kernel,
                diag::DiagnosticEngine& diag)
{
    return std::visit([&](const auto& s) -> bool {
        using T = std::decay_t<decltype(s)>;

        // let x be a T — deferred until term layer is implemented
        if constexpr (std::is_same_v<T, ast::LetStep>) {
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

        // have <name> : <prop> by <refs>
        else if constexpr (std::is_same_v<T, ast::HaveStep>) {
            auto es = resolve_refs(s.justification, env, diag, step.loc);
            if (!es) return false;
            auto app = infer_rule(s.prop, *es, diag, step.loc);
            if (!app) return false;
            auto r = kernel.apply(app->rule, std::span{app->premises}, s.prop);
            if (!r) {
                diag.emit({diag::Severity::Error, step.loc,
                           "kernel rejected '" + s.name + "': " + r.error().message});
                return false;
            }
            env.insert_or_assign(s.name, HypEntry{std::move(*r), EntryKind::Derived});
            return true;
        }

        // then <prop> by <refs>
        else if constexpr (std::is_same_v<T, ast::ThenStep>) {
            if (s.justification.empty()) {
                diag.emit({diag::Severity::Error, step.loc,
                           "'then' step requires a 'by' justification"});
                return false;
            }
            auto es = resolve_refs(s.justification, env, diag, step.loc);
            if (!es) return false;
            auto app = infer_rule(s.prop, *es, diag, step.loc);
            if (!app) return false;
            auto r = kernel.apply(app->rule, std::span{app->premises}, s.prop);
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

    HypEnv env{module_env};

    // Track the last concluding step — either a ThenStep or a CasesStep.
    enum class LastKind { None, Then, Cases };
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
        } else { // Cases
            const auto& cs = std::get<ast::CasesStep>(last_concluding->node);
            auto it = env.find(cs.name);
            if (it != env.end() && !(it->second.judgment.prop() == decl.statement))
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

        case ast::DeclKind::Definition:
            break;
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
