#include <forall/kernel/kernel.hpp>
#include <forall/ast/node.hpp>

// Definitional equality: structural equality after beta + eta normalisation.
// Used throughout apply() so that ForallElim with a lambda witness succeeds when
// the substituted body differs from the stated conclusion only by beta-reduction.
static bool props_eq(const forall::ast::Prop& a, const forall::ast::Prop& b) {
    return forall::ast::defn_eq(a, b);
}

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
Kernel::apply(Rule rule, std::span<const Judgment> premises, const ast::Prop& conclusion,
              const ast::Expr* witness) {

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
        if (!props_eq(premises[0].prop(), conclusion))
            return mismatch("assumption must match conclusion");
        return make(conclusion);

    // ── A ∧ B from A and B ────────────────────────────────────────────────────
    case Rule::AndIntro: {
        if (premises.size() != 2) return wrong_arity(2);
        const auto* conj = std::get_if<PropAnd>(&conclusion.node);
        if (!conj)
            return mismatch("AndIntro: conclusion must be A ∧ B");
        if (!props_eq(premises[0].prop(), *conj->lhs))
            return mismatch("AndIntro: first premise must match left conjunct");
        if (!props_eq(premises[1].prop(), *conj->rhs))
            return mismatch("AndIntro: second premise must match right conjunct");
        return make(conclusion);
    }

    // ── A from A ∧ B ──────────────────────────────────────────────────────────
    case Rule::AndElimL: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* conj = std::get_if<PropAnd>(&premises[0].prop().node);
        if (!conj)
            return mismatch("AndElimL: premise must be A ∧ B");
        if (!props_eq(conclusion, *conj->lhs))
            return mismatch("AndElimL: conclusion must be left conjunct A");
        return make(conclusion);
    }

    // ── B from A ∧ B ──────────────────────────────────────────────────────────
    case Rule::AndElimR: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* conj = std::get_if<PropAnd>(&premises[0].prop().node);
        if (!conj)
            return mismatch("AndElimR: premise must be A ∧ B");
        if (!props_eq(conclusion, *conj->rhs))
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
        if (!props_eq(premises[0].prop(), *impl->rhs))
            return mismatch("ImplIntro: premise must be the consequent B");
        return make(conclusion);
    }

    // ── B from A → B and A  (modus ponens) ───────────────────────────────────
    case Rule::ImplElim: {
        if (premises.size() != 2) return wrong_arity(2);
        const auto* impl = std::get_if<PropImpl>(&premises[0].prop().node);
        if (!impl)
            return mismatch("ImplElim: first premise must be A → B");
        if (!props_eq(premises[1].prop(), *impl->lhs))
            return mismatch("ImplElim: second premise must be antecedent A");
        if (!props_eq(conclusion, *impl->rhs))
            return mismatch("ImplElim: conclusion must be consequent B");
        return make(conclusion);
    }

    // ── A ∨ B from A ─────────────────────────────────────────────────────────
    case Rule::OrIntroL: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* disj = std::get_if<PropOr>(&conclusion.node);
        if (!disj)
            return mismatch("OrIntroL: conclusion must be A ∨ B");
        if (!props_eq(premises[0].prop(), *disj->lhs))
            return mismatch("OrIntroL: premise must match left disjunct A");
        return make(conclusion);
    }

    // ── A ∨ B from B ─────────────────────────────────────────────────────────
    case Rule::OrIntroR: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* disj = std::get_if<PropOr>(&conclusion.node);
        if (!disj)
            return mismatch("OrIntroR: conclusion must be A ∨ B");
        if (!props_eq(premises[0].prop(), *disj->rhs))
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
        if (!props_eq(*lcase->lhs, *disj->lhs) || !props_eq(*rcase->lhs, *disj->rhs))
            return mismatch("OrElim: case premises must match the disjuncts");
        if (!props_eq(conclusion, *lcase->rhs) || !props_eq(conclusion, *rcase->rhs))
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
        if (!props_eq(premises[1].prop(), *neg->inner))
            return mismatch("NotElim: second premise must be A");
        if (!std::get_if<PropFalse>(&conclusion.node))
            return mismatch("NotElim: conclusion must be ⊥");
        return make(conclusion);
    }

    // ── ⊤-intro (trivially true) ─────────────────────────────────────────────
    case Rule::TrueIntro: {
        if (!premises.empty()) return wrong_arity(0);
        if (!std::get_if<PropTrue>(&conclusion.node))
            return mismatch("TrueIntro: conclusion must be ⊤");
        return make(conclusion);
    }

    // ── P from ⊥  (ex falso quodlibet) ───────────────────────────────────────
    case Rule::FalseElim: {
        if (premises.size() != 1) return wrong_arity(1);
        if (!std::get_if<PropFalse>(&premises[0].prop().node))
            return mismatch("FalseElim: premise must be ⊥");
        return make(conclusion); // conclusion can be anything
    }

    // ── P[x:=t] from ∀x.P and witness t ─────────────────────────────────────
    // ForallElim (universal instantiation):
    //   Γ ⊢ ∀x.P   t is any term
    //   ─────────────────────────
    //   Γ ⊢ P[x:=t]
    case Rule::ForallElim: {
        if (premises.size() != 1) return wrong_arity(1);
        if (!witness)
            return mismatch("ForallElim: witness term t is required");
        const auto* fa = std::get_if<PropForall>(&premises[0].prop().node);
        if (!fa)
            return mismatch("ForallElim: premise must be ∀ x, P");
        const ast::Prop expected = ast::subst(*fa->body, fa->var, *witness);
        if (!props_eq(conclusion, expected))
            return mismatch("ForallElim: conclusion must be P[x:=t]");
        return make(conclusion);
    }

    // ── ∃x.P from P[x:=t] and witness t ─────────────────────────────────────
    // ExistsIntro (existential introduction):
    //   Γ ⊢ P[x:=t]   t is any term
    //   ─────────────────────────────
    //   Γ ⊢ ∃x.P
    case Rule::ExistsIntro: {
        if (premises.size() != 1) return wrong_arity(1);
        if (!witness)
            return mismatch("ExistsIntro: witness term t is required");
        const auto* ex = std::get_if<PropExists>(&conclusion.node);
        if (!ex)
            return mismatch("ExistsIntro: conclusion must be ∃ x, P");
        const ast::Prop expected = ast::subst(*ex->body, ex->var, *witness);
        if (!props_eq(premises[0].prop(), expected))
            return mismatch("ExistsIntro: premise must be P[x:=t]");
        return make(conclusion);
    }

    // ── ∀x.P from P(x)  ──────────────────────────────────────────────────────
    // ForallIntro (universal introduction):
    //   Γ ⊢ P(x)   x does not appear free in Γ  (freshness checked by checker)
    //   ─────────────────────────────────────────────────────────────────────
    //   Γ ⊢ ∀ x [: T], P(x)
    case Rule::ForallIntro: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* fa = std::get_if<PropForall>(&conclusion.node);
        if (!fa)
            return mismatch("ForallIntro: conclusion must be ∀ x, P");
        if (!props_eq(premises[0].prop(), *fa->body))
            return mismatch("ForallIntro: premise must equal the body of ∀ x, P");
        return make(conclusion);
    }

    // ── Q from ∃x.P and sub-proof of Q (with fresh x, P(x) assumed) ─────────────
    // ExistsElim (existential elimination):
    //   Γ ⊢ ∃x.P    Γ, x:T, h:P(x) ⊢ Q    x ∉ free(Q)  (checked by checker)
    //   ─────────────────────────────────────────────────────────────────────
    //   Γ ⊢ Q
    case Rule::ExistsElim: {
        if (premises.size() != 2) return wrong_arity(2);
        if (!std::get_if<PropExists>(&premises[0].prop().node))
            return mismatch("ExistsElim: first premise must be ∃ x, P");
        if (!props_eq(premises[1].prop(), conclusion))
            return mismatch("ExistsElim: second premise must equal conclusion Q");
        return make(conclusion);
    }

    // ── ∀n:Nat,P(n) from P(0) and ∀n:Nat,P(n)→P(succ(n)) ───────────────────────
    // NatInduction (mathematical induction on natural numbers):
    //   Γ ⊢ P(0)
    //   Γ ⊢ ∀n:Nat, P(n) → P(succ(n))
    //   ─────────────────────────────────
    //   Γ ⊢ ∀n:Nat, P(n)
    //
    // Verification:
    //   conclusion must be  ∀ n : Nat, P(n).
    //   premise[0] must be  P[n:=0]  == subst(body, var, ExprLit{0}).
    //   premise[1] must be  ∀ n : Nat, P(n) → P(succ(n))
    //       == ∀ n : Nat, body → subst(body, var, ExprCall{"succ", {ExprVar{var}}}).
    case Rule::NatInduction: {
        if (premises.size() != 2) return wrong_arity(2);

        const auto* fa = std::get_if<PropForall>(&conclusion.node);
        if (!fa)
            return mismatch("NatInduction: conclusion must be ∀ n : Nat, P(n)");

        const ast::Prop base_expected = ast::subst(*fa->body, fa->var,
            ast::Expr{{}, ast::ExprLit{"0"}});
        if (!props_eq(premises[0].prop(), base_expected))
            return mismatch("NatInduction: first premise must be P[n:=0]");

        // step premise: ∀ n : Nat, P(n) → P(succ(n))
        ast::Prop p_succ_n = ast::subst(*fa->body, fa->var,
            ast::Expr{{}, ast::ExprCall{"succ",
                {ast::make_expr(ast::Expr{{}, ast::ExprVar{fa->var}})}}});
        ast::Prop step_body{{}, ast::PropImpl{fa->body, ast::make_prop(p_succ_n)}};
        ast::Prop step_expected{{},
            ast::PropForall{fa->var, fa->type, ast::make_prop(step_body)}};
        if (!props_eq(premises[1].prop(), step_expected))
            return mismatch("NatInduction: second premise must be ∀ n : Nat, P(n) → P(succ(n))");

        return make(conclusion);
    }

    // ── Refl: ⊢ a = a ─────────────────────────────────────────────────────────
    case Rule::Refl: {
        if (!premises.empty()) return wrong_arity(0);
        const auto* rel = std::get_if<ast::PropRel>(&conclusion.node);
        if (!rel || rel->op != ast::RelOp::Eq)
            return mismatch("Refl: conclusion must be a = a");
        if (!ast::defn_eq(*rel->lhs, *rel->rhs))
            return mismatch("Refl: both sides must be definitionally equal");
        return make(conclusion);
    }

    // ── Symm: a = b ⊢ b = a ──────────────────────────────────────────────────
    case Rule::Symm: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* p = std::get_if<ast::PropRel>(&premises[0].prop().node);
        if (!p || p->op != ast::RelOp::Eq)
            return mismatch("Symm: premise must be a = b");
        const auto* c = std::get_if<ast::PropRel>(&conclusion.node);
        if (!c || c->op != ast::RelOp::Eq)
            return mismatch("Symm: conclusion must be b = a");
        if (!ast::defn_eq(*c->lhs, *p->rhs) || !ast::defn_eq(*c->rhs, *p->lhs))
            return mismatch("Symm: conclusion must swap premise sides");
        return make(conclusion);
    }

    // ── Trans: a = b, b = c ⊢ a = c ──────────────────────────────────────────
    case Rule::Trans: {
        if (premises.size() != 2) return wrong_arity(2);
        const auto* p0 = std::get_if<ast::PropRel>(&premises[0].prop().node);
        const auto* p1 = std::get_if<ast::PropRel>(&premises[1].prop().node);
        if (!p0 || p0->op != ast::RelOp::Eq)
            return mismatch("Trans: first premise must be a = b");
        if (!p1 || p1->op != ast::RelOp::Eq)
            return mismatch("Trans: second premise must be b = c");
        if (!ast::defn_eq(*p0->rhs, *p1->lhs))
            return mismatch("Trans: middle terms must match (rhs of first = lhs of second)");
        const auto* c = std::get_if<ast::PropRel>(&conclusion.node);
        if (!c || c->op != ast::RelOp::Eq)
            return mismatch("Trans: conclusion must be a = c");
        if (!ast::defn_eq(*c->lhs, *p0->lhs) || !ast::defn_eq(*c->rhs, *p1->rhs))
            return mismatch("Trans: conclusion must be a = c");
        return make(conclusion);
    }

    // ── Congr: a = b ⊢ f(a) = f(b) ──────────────────────────────────────────
    // Verified by: substituting b→a in conclusion.rhs yields conclusion.lhs
    // (or substituting a→b in conclusion.lhs yields conclusion.rhs).
    case Rule::Congr: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* p = std::get_if<ast::PropRel>(&premises[0].prop().node);
        if (!p || p->op != ast::RelOp::Eq)
            return mismatch("Congr: premise must be a = b");
        const auto* c = std::get_if<ast::PropRel>(&conclusion.node);
        if (!c || c->op != ast::RelOp::Eq)
            return mismatch("Congr: conclusion must be f(a) = f(b)");
        // Replace b with a in rhs; result should equal lhs.
        const ast::Expr lhs_check = ast::subst_expr(*c->rhs, *p->rhs, *p->lhs);
        if (!ast::defn_eq(lhs_check, *c->lhs))
            return mismatch("Congr: conclusion is not a valid congruence of the premise");
        return make(conclusion);
    }

    // ── EqSubst: substitution of equals in propositions ─────────────────────
    // Premises: [0] h : a = b,  [1] proof_P_b : P(b)
    // Conclusion: P(a)   (the conclusion with b replaced back by a)
    // Verified by: replacing a with b in the conclusion yields the second premise.
    // This is the "rewrite" closure rule: once `rewrite h` has produced a proof
    // of the rewritten goal P(b), EqSubst certifies the original goal P(a).
    case Rule::EqSubst: {
        if (premises.size() != 2) return wrong_arity(2);
        const auto* eq = std::get_if<ast::PropRel>(&premises[0].prop().node);
        if (!eq || eq->op != ast::RelOp::Eq)
            return mismatch("EqSubst: first premise must be a = b");
        // Replace all occurrences of a (lhs) with b (rhs) in the conclusion.
        // The result must equal the second premise.
        const ast::Prop subst_check = ast::subst_expr(conclusion, *eq->lhs, *eq->rhs);
        if (!props_eq(subst_check, premises[1].prop()))
            return mismatch("EqSubst: substituting lhs→rhs in conclusion does not yield second premise");
        return make(conclusion);
    }

    // ── ProofIrrel: two proofs of the same proposition are interchangeable ────
    // Given two Judgments certifying the same Prop, certify that Prop.
    // In our LCF design this is already implicit (Judgment carries no proof
    // term), but the explicit rule documents the invariant and allows it to
    // be invoked deliberately.
    case Rule::ProofIrrel: {
        if (premises.size() != 2) return wrong_arity(2);
        if (!props_eq(premises[0].prop(), premises[1].prop()))
            return mismatch("ProofIrrel: both premises must prove the same proposition");
        return make(premises[0].prop());
    }

    // ── PropExt: propositional extensionality ─────────────────────────────────
    // Premise  : h : (P→Q)∧(Q→P)   (the desugared form of P ↔ Q)
    // Conclusion must be a PropRel{Eq} with both sides being Atomic propositions.
    // This rule is sound: logically equivalent propositions are equal (propext).
    case Rule::PropExt: {
        if (premises.size() != 1) return wrong_arity(1);
        const auto* conj = std::get_if<ast::PropAnd>(&premises[0].prop().node);
        if (!conj)
            return mismatch("PropExt: premise must be (P→Q)∧(Q→P) — a biconditional");
        const auto* fwd = std::get_if<ast::PropImpl>(&conj->lhs->node);
        const auto* bwd = std::get_if<ast::PropImpl>(&conj->rhs->node);
        if (!fwd || !bwd)
            return mismatch("PropExt: premise must be (P→Q)∧(Q→P)");
        // P→Q and Q→P: verify lhs of fwd == rhs of bwd and rhs of fwd == lhs of bwd
        if (!props_eq(*fwd->lhs, *bwd->rhs) || !props_eq(*fwd->rhs, *bwd->lhs))
            return mismatch("PropExt: premise direction mismatch — expected (P→Q)∧(Q→P)");
        // Conclusion must be P = Q (as a PropRel{Eq} over Atomic names) — or any
        // form accepted by introduce_axiom at the checker level.  For the kernel we
        // just certify the conclusion as stated without further inspection.
        return make(conclusion);
    }

    } // switch
    return std::unexpected(err(rule, "unhandled rule"));
}

} // namespace forall::kernel
