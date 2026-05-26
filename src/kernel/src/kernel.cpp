#include <forall/kernel/kernel.hpp>

namespace forall::kernel {

namespace {

KernelError err(Rule rule, std::string msg) {
    return KernelError{rule, std::move(msg)};
}


} // namespace

// ── introduce_axiom ────────────────────────────────────────────────────────────

std::expected<Judgment, KernelError>
Kernel::introduce_axiom(const ast::Prop& prop) {
    return make(prop);
}

// ── apply ──────────────────────────────────────────────────────────────────────
//
// Each rule verifies that the given premises structurally match what the rule
// requires, then certifies the conclusion by constructing a Judgment.
//
// Rules that require assumption-context tracking (ImplIntro, OrElim, NotIntro,
// Assumption) are noted; they are stubs until the checker passes a context.

std::expected<Judgment, KernelError>
Kernel::apply(Rule rule, std::span<const Judgment> premises, const ast::Prop& conclusion) {

    using namespace ast;
    auto wrong_arity = [&](std::size_t expected) -> std::expected<Judgment, KernelError> {
        return std::unexpected(err(rule,
            "expected " + std::to_string(expected) + " premise(s), got "
            + std::to_string(premises.size())));
    };
    auto mismatch = [&](std::string msg) -> std::expected<Judgment, KernelError> {
        return std::unexpected(err(rule, std::move(msg)));
    };

    switch (rule) {

    // ── Axiom: no premises, conclusion is whatever was declared ────────────────
    case Rule::Axiom:
        if (!premises.empty()) return wrong_arity(0);
        return make(conclusion);

    // ── Assumption: premise is the conclusion itself (context managed outside) ─
    case Rule::Assumption:
        if (premises.size() != 1) return wrong_arity(1);
        if (!(premises[0].prop() == conclusion))
            return mismatch("assumption must match conclusion");
        return make(conclusion);

    // ── A ∧ B from A and B ────────────────────────────────────────────────────
    case Rule::AndIntro: {
        if (premises.size() != 2) return wrong_arity(2);
        const auto* conj = std::get_if<PropAnd>(&conclusion.node);
        if (!conj)
            return mismatch("AndIntro: conclusion must be A ∧ B");
        if (!(premises[0].prop() == *conj->lhs))
            return mismatch("AndIntro: first premise must match left conjunct");
        if (!(premises[1].prop() == *conj->rhs))
            return mismatch("AndIntro: second premise must match right conjunct");
        return make(conclusion);
    }

    // ── A from A ∧ B ──────────────────────────────────────────────────────────
    case Rule::AndElimL: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* conj = std::get_if<PropAnd>(&premises[0].prop().node);
        if (!conj)
            return mismatch("AndElimL: premise must be A ∧ B");
        if (!(conclusion == *conj->lhs))
            return mismatch("AndElimL: conclusion must be left conjunct A");
        return make(conclusion);
    }

    // ── B from A ∧ B ──────────────────────────────────────────────────────────
    case Rule::AndElimR: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* conj = std::get_if<PropAnd>(&premises[0].prop().node);
        if (!conj)
            return mismatch("AndElimR: premise must be A ∧ B");
        if (!(conclusion == *conj->rhs))
            return mismatch("AndElimR: conclusion must be right conjunct B");
        return make(conclusion);
    }

    // ── A → B given Γ,A ⊢ B  (ImplIntro requires assumption context) ──────────
    case Rule::ImplIntro: {
        // TODO: requires checker to pass the discharged assumption A separately.
        // For now, accept if conclusion is A → B and single premise is B.
        if (premises.size() != 1) return wrong_arity(1);
        const auto* impl = std::get_if<PropImpl>(&conclusion.node);
        if (!impl)
            return mismatch("ImplIntro: conclusion must be A → B");
        if (!(premises[0].prop() == *impl->rhs))
            return mismatch("ImplIntro: premise must be the consequent B");
        return make(conclusion);
    }

    // ── B from A → B and A  (modus ponens) ───────────────────────────────────
    case Rule::ImplElim: {
        if (premises.size() != 2) return wrong_arity(2);
        const auto* impl = std::get_if<PropImpl>(&premises[0].prop().node);
        if (!impl)
            return mismatch("ImplElim: first premise must be A → B");
        if (!(premises[1].prop() == *impl->lhs))
            return mismatch("ImplElim: second premise must be antecedent A");
        if (!(conclusion == *impl->rhs))
            return mismatch("ImplElim: conclusion must be consequent B");
        return make(conclusion);
    }

    // ── A ∨ B from A ─────────────────────────────────────────────────────────
    case Rule::OrIntroL: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* disj = std::get_if<PropOr>(&conclusion.node);
        if (!disj)
            return mismatch("OrIntroL: conclusion must be A ∨ B");
        if (!(premises[0].prop() == *disj->lhs))
            return mismatch("OrIntroL: premise must match left disjunct A");
        return make(conclusion);
    }

    // ── A ∨ B from B ─────────────────────────────────────────────────────────
    case Rule::OrIntroR: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* disj = std::get_if<PropOr>(&conclusion.node);
        if (!disj)
            return mismatch("OrIntroR: conclusion must be A ∨ B");
        if (!(premises[0].prop() == *disj->rhs))
            return mismatch("OrIntroR: premise must match right disjunct B");
        return make(conclusion);
    }

    // ── C from A ∨ B, A → C, B → C  (OrElim requires two sub-proofs) ─────────
    case Rule::OrElim: {
        // TODO: the two case sub-proofs require assumption context.
        // Minimal check: 3 premises; [0] is A∨B, [1] is A→C, [2] is B→C.
        if (premises.size() != 3) return wrong_arity(3);
        const auto* disj = std::get_if<PropOr>(&premises[0].prop().node);
        if (!disj)
            return mismatch("OrElim: first premise must be A ∨ B");
        const auto* lcase = std::get_if<PropImpl>(&premises[1].prop().node);
        const auto* rcase = std::get_if<PropImpl>(&premises[2].prop().node);
        if (!lcase || !rcase)
            return mismatch("OrElim: second and third premises must be A → C and B → C");
        if (!(*lcase->lhs == *disj->lhs) || !(*rcase->lhs == *disj->rhs))
            return mismatch("OrElim: case premises must match the disjuncts");
        if (!(conclusion == *lcase->rhs) || !(conclusion == *rcase->rhs))
            return mismatch("OrElim: both cases must conclude C");
        return make(conclusion);
    }

    // ── ¬A from Γ,A ⊢ ⊥  (NotIntro requires assumption context) ──────────────
    case Rule::NotIntro: {
        // TODO: requires checker to pass the discharged assumption A.
        if (premises.size() != 1) return wrong_arity(1);
        const auto* neg = std::get_if<PropNot>(&conclusion.node);
        if (!neg)
            return mismatch("NotIntro: conclusion must be ¬A");
        if (!std::get_if<PropFalse>(&premises[0].prop().node))
            return mismatch("NotIntro: premise must be ⊥");
        return make(conclusion);
    }

    // ── ⊥ from ¬A and A ──────────────────────────────────────────────────────
    case Rule::NotElim: {
        if (premises.size() != 2) return wrong_arity(2);
        const auto* neg = std::get_if<PropNot>(&premises[0].prop().node);
        if (!neg)
            return mismatch("NotElim: first premise must be ¬A");
        if (!(premises[1].prop() == *neg->inner))
            return mismatch("NotElim: second premise must be A");
        if (!std::get_if<PropFalse>(&conclusion.node))
            return mismatch("NotElim: conclusion must be ⊥");
        return make(conclusion);
    }

    // ── P from ⊥  (ex falso quodlibet) ───────────────────────────────────────
    case Rule::FalseElim: {
        if (premises.size() != 1) return wrong_arity(1);
        if (!std::get_if<PropFalse>(&premises[0].prop().node))
            return mismatch("FalseElim: premise must be ⊥");
        return make(conclusion); // conclusion can be anything
    }

    } // switch
    return std::unexpected(err(rule, "unhandled rule"));
}

} // namespace forall::kernel
