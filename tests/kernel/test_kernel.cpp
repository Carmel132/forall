#include <gtest/gtest.h>
#include <forall/kernel/kernel.hpp>

using namespace forall;
using namespace forall::ast;

static Prop atom(std::string name) { return {diag::SourceLocation{}, Atomic{std::move(name)}}; }
static Prop prop_and(Prop l, Prop r) { return {diag::SourceLocation{}, PropAnd{make_prop(std::move(l)), make_prop(std::move(r))}}; }
static Prop prop_or (Prop l, Prop r) { return {diag::SourceLocation{}, PropOr {make_prop(std::move(l)), make_prop(std::move(r))}}; }
static Prop prop_impl(Prop l, Prop r){ return {diag::SourceLocation{}, PropImpl{make_prop(std::move(l)), make_prop(std::move(r))}}; }
static Prop prop_not(Prop p)         { return {diag::SourceLocation{}, PropNot{make_prop(std::move(p))}}; }
static Prop prop_false()             { return {diag::SourceLocation{}, PropFalse{}}; }

TEST(KernelTest, AxiomIntroduction) {
    kernel::Kernel k;
    auto result = k.introduce_axiom(atom("P"));
    ASSERT_TRUE(result.has_value());
    const auto* a = std::get_if<Atomic>(&result->prop().node);
    ASSERT_NE(a, nullptr);
    EXPECT_EQ(a->name, "P");
}

TEST(KernelTest, AndIntro) {
    kernel::Kernel k;
    auto ja = k.introduce_axiom(atom("A")); ASSERT_TRUE(ja);
    auto jb = k.introduce_axiom(atom("B")); ASSERT_TRUE(jb);

    std::vector<kernel::Judgment> premises{*ja, *jb};
    auto result = k.apply(kernel::Rule::AndIntro, premises, prop_and(atom("A"), atom("B")));
    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(std::get_if<PropAnd>(&result->prop().node));
}

TEST(KernelTest, AndIntroWrongConclusion) {
    kernel::Kernel k;
    auto ja = k.introduce_axiom(atom("A")); ASSERT_TRUE(ja);
    auto jb = k.introduce_axiom(atom("B")); ASSERT_TRUE(jb);

    std::vector<kernel::Judgment> premises{*ja, *jb};
    auto result = k.apply(kernel::Rule::AndIntro, premises, prop_and(atom("A"), atom("C")));
    EXPECT_FALSE(result.has_value());
}

TEST(KernelTest, AndElimL) {
    kernel::Kernel k;
    auto jab = k.introduce_axiom(prop_and(atom("A"), atom("B"))); ASSERT_TRUE(jab);

    std::vector<kernel::Judgment> premises{*jab};
    auto result = k.apply(kernel::Rule::AndElimL, premises, atom("A"));
    ASSERT_TRUE(result.has_value());
    const auto* a = std::get_if<Atomic>(&result->prop().node);
    ASSERT_NE(a, nullptr);
    EXPECT_EQ(a->name, "A");
}

TEST(KernelTest, AndElimR) {
    kernel::Kernel k;
    auto jab = k.introduce_axiom(prop_and(atom("A"), atom("B"))); ASSERT_TRUE(jab);

    std::vector<kernel::Judgment> premises{*jab};
    auto result = k.apply(kernel::Rule::AndElimR, premises, atom("B"));
    ASSERT_TRUE(result.has_value());
}

TEST(KernelTest, ImplElim) {
    kernel::Kernel k;
    auto jab = k.introduce_axiom(prop_impl(atom("A"), atom("B"))); ASSERT_TRUE(jab);
    auto ja  = k.introduce_axiom(atom("A"));                       ASSERT_TRUE(ja);

    std::vector<kernel::Judgment> premises{*jab, *ja};
    auto result = k.apply(kernel::Rule::ImplElim, premises, atom("B"));
    ASSERT_TRUE(result.has_value());
}

TEST(KernelTest, ImplElimWrongAntecedent) {
    kernel::Kernel k;
    auto jab = k.introduce_axiom(prop_impl(atom("A"), atom("B"))); ASSERT_TRUE(jab);
    auto jc  = k.introduce_axiom(atom("C"));                       ASSERT_TRUE(jc);

    std::vector<kernel::Judgment> premises{*jab, *jc};
    auto result = k.apply(kernel::Rule::ImplElim, premises, atom("B"));
    EXPECT_FALSE(result.has_value());
}

TEST(KernelTest, OrIntroL) {
    kernel::Kernel k;
    auto ja = k.introduce_axiom(atom("A")); ASSERT_TRUE(ja);

    std::vector<kernel::Judgment> premises{*ja};
    auto result = k.apply(kernel::Rule::OrIntroL, premises, prop_or(atom("A"), atom("B")));
    ASSERT_TRUE(result.has_value());
}

TEST(KernelTest, OrIntroR) {
    kernel::Kernel k;
    auto jb = k.introduce_axiom(atom("B")); ASSERT_TRUE(jb);

    std::vector<kernel::Judgment> premises{*jb};
    auto result = k.apply(kernel::Rule::OrIntroR, premises, prop_or(atom("A"), atom("B")));
    ASSERT_TRUE(result.has_value());
}

TEST(KernelTest, NotElim) {
    kernel::Kernel k;
    auto jnota = k.introduce_axiom(prop_not(atom("A"))); ASSERT_TRUE(jnota);
    auto ja    = k.introduce_axiom(atom("A"));            ASSERT_TRUE(ja);

    std::vector<kernel::Judgment> premises{*jnota, *ja};
    auto result = k.apply(kernel::Rule::NotElim, premises, prop_false());
    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(std::get_if<PropFalse>(&result->prop().node));
}

TEST(KernelTest, FalseElim) {
    kernel::Kernel k;
    auto jbot = k.introduce_axiom(prop_false()); ASSERT_TRUE(jbot);

    std::vector<kernel::Judgment> premises{*jbot};
    auto result = k.apply(kernel::Rule::FalseElim, premises, atom("AnythingAtAll"));
    ASSERT_TRUE(result.has_value());
}

TEST(KernelTest, PropEquality) {
    EXPECT_EQ(atom("P"), atom("P"));
    EXPECT_NE(atom("P"), atom("Q"));
    EXPECT_EQ(prop_and(atom("A"), atom("B")), prop_and(atom("A"), atom("B")));
    EXPECT_NE(prop_and(atom("A"), atom("B")), prop_and(atom("B"), atom("A")));
    EXPECT_EQ(prop_not(atom("P")), prop_not(atom("P")));
    EXPECT_NE(prop_not(atom("P")), prop_not(atom("Q")));
}

TEST(KernelTest, PropEqualityNested) {
    // (A → B) ∧ (C → D) == (A → B) ∧ (C → D)
    auto ab = prop_impl(atom("A"), atom("B"));
    auto cd = prop_impl(atom("C"), atom("D"));
    EXPECT_EQ(prop_and(ab, cd), prop_and(ab, cd));
    EXPECT_NE(prop_and(ab, cd), prop_and(ab, prop_impl(atom("C"), atom("E"))));
    // Nesting depth does not confuse equality
    EXPECT_EQ(prop_or(prop_and(ab, cd), prop_not(atom("P"))),
              prop_or(prop_and(ab, cd), prop_not(atom("P"))));
}

TEST(KernelTest, PropFalseEquality) {
    EXPECT_EQ(prop_false(), prop_false());
    EXPECT_NE(prop_false(), atom("P"));
    EXPECT_NE(atom("P"),    prop_false());
    EXPECT_NE(prop_false(), prop_not(atom("P")));
}

TEST(KernelTest, PropImplAssociativity) {
    // P → (Q → R) ≠ (P → Q) → R
    auto left  = prop_impl(atom("P"), prop_impl(atom("Q"), atom("R")));
    auto right = prop_impl(prop_impl(atom("P"), atom("Q")), atom("R"));
    EXPECT_NE(left, right);
}

// ── ForallElim ────────────────────────────────────────────────────────────────

static Prop prop_forall(std::string v, Prop body) {
    return {diag::SourceLocation{}, PropForall{std::move(v), std::nullopt,
                                               make_prop(std::move(body))}};
}
static Prop prop_exists(std::string v, Prop body) {
    return {diag::SourceLocation{}, PropExists{std::move(v), std::nullopt,
                                               make_prop(std::move(body))}};
}
static Prop prop_rel(Expr l, RelOp op, Expr r) {
    return {diag::SourceLocation{},
            PropRel{make_expr(std::move(l)), make_expr(std::move(r)), op}};
}
static Expr evar(std::string n) { return {diag::SourceLocation{}, ExprVar{std::move(n)}}; }
static Expr elit(std::string v) { return {diag::SourceLocation{}, ExprLit{std::move(v)}}; }

TEST(KernelTest, ForallElim_Basic) {
    // ∀ x, x = 0   →  conclude  5 = 0  with witness 5
    kernel::Kernel k;
    Prop forall_prop = prop_forall("x", prop_rel(evar("x"), RelOp::Eq, elit("0")));
    auto j = k.introduce_axiom(forall_prop); ASSERT_TRUE(j);

    Expr five = elit("5");
    Prop conclusion = subst(*std::get<PropForall>(forall_prop.node).body, "x", five);
    // conclusion == 5 = 0
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ForallElim, prem, conclusion, &five);
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->prop(), conclusion);
}

TEST(KernelTest, ForallElim_WrongConclusion) {
    kernel::Kernel k;
    Prop forall_prop = prop_forall("x", prop_rel(evar("x"), RelOp::Eq, elit("0")));
    auto j = k.introduce_axiom(forall_prop); ASSERT_TRUE(j);

    Expr five = elit("5");
    Prop wrong_conclusion = prop_rel(elit("5"), RelOp::Eq, elit("1")); // 5 = 1 ≠ 5 = 0
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ForallElim, prem, wrong_conclusion, &five);
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, ForallElim_MissingWitness) {
    kernel::Kernel k;
    Prop forall_prop = prop_forall("x", prop_rel(evar("x"), RelOp::Eq, elit("0")));
    auto j = k.introduce_axiom(forall_prop); ASSERT_TRUE(j);
    Prop conclusion = prop_rel(elit("5"), RelOp::Eq, elit("0"));
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ForallElim, prem, conclusion, nullptr);
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, ForallElim_PremiseMustBeForall) {
    kernel::Kernel k;
    Prop not_forall = atom("P");
    auto j = k.introduce_axiom(not_forall); ASSERT_TRUE(j);
    Expr five = elit("5");
    Prop conclusion = atom("P");
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ForallElim, prem, conclusion, &five);
    EXPECT_FALSE(r.has_value());
}

// ── ExistsIntro ───────────────────────────────────────────────────────────────

TEST(KernelTest, ExistsIntro_Basic) {
    // premise: 5 = 0  (i.e., P[x:=5] with P = x=0)
    // conclusion: ∃ x, x = 0   with witness 5
    kernel::Kernel k;
    Expr five = elit("5");
    Prop premise = prop_rel(elit("5"), RelOp::Eq, elit("0")); // 5 = 0
    auto j = k.introduce_axiom(premise); ASSERT_TRUE(j);

    Prop conclusion = prop_exists("x", prop_rel(evar("x"), RelOp::Eq, elit("0")));
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ExistsIntro, prem, conclusion, &five);
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->prop(), conclusion);
}

TEST(KernelTest, ExistsIntro_WrongWitness) {
    // witness is 7 but premise says 5 = 0 — subst(x=0, x, 7) = 7=0 ≠ 5=0
    kernel::Kernel k;
    Expr seven = elit("7");
    Prop premise = prop_rel(elit("5"), RelOp::Eq, elit("0"));
    auto j = k.introduce_axiom(premise); ASSERT_TRUE(j);
    Prop conclusion = prop_exists("x", prop_rel(evar("x"), RelOp::Eq, elit("0")));
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ExistsIntro, prem, conclusion, &seven);
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, ExistsIntro_MissingWitness) {
    kernel::Kernel k;
    Prop premise = prop_rel(elit("5"), RelOp::Eq, elit("0"));
    auto j = k.introduce_axiom(premise); ASSERT_TRUE(j);
    Prop conclusion = prop_exists("x", prop_rel(evar("x"), RelOp::Eq, elit("0")));
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ExistsIntro, prem, conclusion, nullptr);
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, ExistsIntro_ConclusionMustBeExists) {
    kernel::Kernel k;
    Expr five = elit("5");
    Prop premise = prop_rel(elit("5"), RelOp::Eq, elit("0"));
    auto j = k.introduce_axiom(premise); ASSERT_TRUE(j);
    Prop not_exists = atom("P");
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ExistsIntro, prem, not_exists, &five);
    EXPECT_FALSE(r.has_value());
}

// ── ForallIntro ────────────────────────────────────────────────────────────────

TEST(KernelTest, ForallIntro_Valid) {
    // premise: n > 0   conclusion: ∀ n, n > 0
    kernel::Kernel k;
    Prop body = prop_rel(evar("n"), RelOp::Gt, elit("0"));
    auto j = k.introduce_axiom(body); ASSERT_TRUE(j);
    Prop conclusion = prop_forall("n", body);
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ForallIntro, prem, conclusion);
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->prop(), conclusion);
}

TEST(KernelTest, ForallIntro_PremiseMustMatchBody) {
    // premise: n > 0   but conclusion body is n > 1 — mismatch
    kernel::Kernel k;
    Prop body_premise = prop_rel(evar("n"), RelOp::Gt, elit("0"));
    Prop body_conc    = prop_rel(evar("n"), RelOp::Gt, elit("1"));
    auto j = k.introduce_axiom(body_premise); ASSERT_TRUE(j);
    Prop conclusion = prop_forall("n", body_conc);
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ForallIntro, prem, conclusion);
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, ForallIntro_ConclusionMustBeForall) {
    // conclusion is not ∀ — should fail
    kernel::Kernel k;
    Prop body = prop_rel(evar("n"), RelOp::Gt, elit("0"));
    auto j = k.introduce_axiom(body); ASSERT_TRUE(j);
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::ForallIntro, prem, body); // body is not PropForall
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, ForallIntro_WrongArity) {
    // ForallIntro requires exactly 1 premise
    kernel::Kernel k;
    Prop body = prop_rel(evar("n"), RelOp::Gt, elit("0"));
    auto j1 = k.introduce_axiom(body); ASSERT_TRUE(j1);
    auto j2 = k.introduce_axiom(body); ASSERT_TRUE(j2);
    Prop conclusion = prop_forall("n", body);
    std::vector<kernel::Judgment> prem{*j1, *j2};
    auto r = k.apply(kernel::Rule::ForallIntro, prem, conclusion);
    EXPECT_FALSE(r.has_value());
}

// ── ExistsElim ─────────────────────────────────────────────────────────────────

TEST(KernelTest, ExistsElim_Valid) {
    // ∃ n, n > 0   and derived Q   ⊢  Q
    kernel::Kernel k;
    Prop ex_prop   = prop_exists("n", prop_rel(evar("n"), RelOp::Gt, elit("0")));
    Prop Q         = atom("R");
    auto j_ex = k.introduce_axiom(ex_prop); ASSERT_TRUE(j_ex);
    auto j_Q  = k.introduce_axiom(Q);       ASSERT_TRUE(j_Q);
    std::vector<kernel::Judgment> prem{*j_ex, *j_Q};
    auto r = k.apply(kernel::Rule::ExistsElim, prem, Q);
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->prop(), Q);
}

TEST(KernelTest, ExistsElim_FirstPremiseMustBeExists) {
    // First premise is not an existential — should fail
    kernel::Kernel k;
    Prop not_exists = atom("P");
    Prop Q          = atom("R");
    auto j1 = k.introduce_axiom(not_exists); ASSERT_TRUE(j1);
    auto j2 = k.introduce_axiom(Q);          ASSERT_TRUE(j2);
    std::vector<kernel::Judgment> prem{*j1, *j2};
    auto r = k.apply(kernel::Rule::ExistsElim, prem, Q);
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, ExistsElim_SecondPremiseMustMatchConclusion) {
    // Second premise is R but conclusion is S — should fail
    kernel::Kernel k;
    Prop ex_prop = prop_exists("n", prop_rel(evar("n"), RelOp::Gt, elit("0")));
    Prop Q       = atom("R");
    Prop S       = atom("S");
    auto j_ex = k.introduce_axiom(ex_prop); ASSERT_TRUE(j_ex);
    auto j_Q  = k.introduce_axiom(Q);       ASSERT_TRUE(j_Q);
    std::vector<kernel::Judgment> prem{*j_ex, *j_Q};
    auto r = k.apply(kernel::Rule::ExistsElim, prem, S); // conclusion S ≠ Q
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, ExistsElim_WrongArity) {
    // ExistsElim requires exactly 2 premises
    kernel::Kernel k;
    Prop ex_prop = prop_exists("n", atom("P"));
    auto j_ex = k.introduce_axiom(ex_prop); ASSERT_TRUE(j_ex);
    std::vector<kernel::Judgment> prem{*j_ex};
    auto r = k.apply(kernel::Rule::ExistsElim, prem, atom("Q"));
    EXPECT_FALSE(r.has_value());
}

// ── NatInduction ──────────────────────────────────────────────────────────────
// Helper: ExprCall for succ(var)
static Expr esucc(std::string var) {
    return {diag::SourceLocation{},
            ExprCall{"succ", {make_expr(evar(std::move(var)))}}};
}
// Helper: ∀ var : Nat, body
static Prop prop_forall_nat(std::string var, Prop body) {
    TypeNode nat{{TypeNat{}}};
    return {diag::SourceLocation{},
            PropForall{std::move(var), std::make_optional(nat),
                       make_prop(std::move(body))}};
}

TEST(KernelTest, NatInduction_Valid) {
    // Prove ∀ n : Nat, P(n)  given P(0) and ∀ n : Nat, P(n) → P(succ(n))
    // where P(n) = n = n  (a trivially true atomic relation for testing)
    kernel::Kernel k;

    // body: n = n
    Prop body        = prop_rel(evar("n"), RelOp::Eq, evar("n"));
    // base: 0 = 0
    Prop base        = subst(body, "n", elit("0"));
    // step: ∀ n : Nat, (n = n) → (succ(n) = succ(n))
    Prop step_body   = prop_impl(body, subst(body, "n", esucc("n")));
    Prop step_prop   = prop_forall_nat("n", step_body);
    // conclusion: ∀ n : Nat, n = n
    Prop conclusion  = prop_forall_nat("n", body);

    auto j_base = k.introduce_axiom(base); ASSERT_TRUE(j_base);
    auto j_step = k.introduce_axiom(step_prop); ASSERT_TRUE(j_step);
    std::vector<kernel::Judgment> prem{*j_base, *j_step};
    auto r = k.apply(kernel::Rule::NatInduction, prem, conclusion);
    ASSERT_TRUE(r.has_value());
    EXPECT_TRUE(std::get_if<PropForall>(&r->prop().node));
}

TEST(KernelTest, NatInduction_WrongBase) {
    // base case has wrong proposition — should fail
    kernel::Kernel k;
    Prop body       = prop_rel(evar("n"), RelOp::Eq, evar("n"));
    Prop wrong_base = atom("WrongBase");
    Prop step_body  = prop_impl(body, subst(body, "n", esucc("n")));
    Prop step_prop  = prop_forall_nat("n", step_body);
    Prop conclusion = prop_forall_nat("n", body);

    auto j_base = k.introduce_axiom(wrong_base); ASSERT_TRUE(j_base);
    auto j_step = k.introduce_axiom(step_prop);  ASSERT_TRUE(j_step);
    std::vector<kernel::Judgment> prem{*j_base, *j_step};
    auto r = k.apply(kernel::Rule::NatInduction, prem, conclusion);
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, NatInduction_WrongStep) {
    // step proposition doesn't match ∀ n, P(n) → P(succ(n)) — should fail
    kernel::Kernel k;
    Prop body       = prop_rel(evar("n"), RelOp::Eq, evar("n"));
    Prop base       = subst(body, "n", elit("0"));
    Prop wrong_step = atom("WrongStep");
    Prop conclusion = prop_forall_nat("n", body);

    auto j_base = k.introduce_axiom(base);       ASSERT_TRUE(j_base);
    auto j_step = k.introduce_axiom(wrong_step); ASSERT_TRUE(j_step);
    std::vector<kernel::Judgment> prem{*j_base, *j_step};
    auto r = k.apply(kernel::Rule::NatInduction, prem, conclusion);
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, NatInduction_ConclusionMustBeForall) {
    // conclusion is not ∀ — should fail
    kernel::Kernel k;
    Prop body       = prop_rel(evar("n"), RelOp::Eq, evar("n"));
    Prop base       = subst(body, "n", elit("0"));
    Prop step_body  = prop_impl(body, subst(body, "n", esucc("n")));
    Prop step_prop  = prop_forall_nat("n", step_body);

    auto j_base = k.introduce_axiom(base);      ASSERT_TRUE(j_base);
    auto j_step = k.introduce_axiom(step_prop); ASSERT_TRUE(j_step);
    std::vector<kernel::Judgment> prem{*j_base, *j_step};
    auto r = k.apply(kernel::Rule::NatInduction, prem, body); // body, not ∀
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, NatInduction_WrongArity) {
    kernel::Kernel k;
    Prop body = prop_rel(evar("n"), RelOp::Eq, evar("n"));
    auto j    = k.introduce_axiom(body); ASSERT_TRUE(j);
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::NatInduction, prem, prop_forall_nat("n", body));
    EXPECT_FALSE(r.has_value());
}

static Prop prop_true() { return {diag::SourceLocation{}, PropTrue{}}; }

TEST(KernelTest, TrueIntro_Valid) {
    kernel::Kernel k;
    std::vector<kernel::Judgment> no_prem;
    auto r = k.apply(kernel::Rule::TrueIntro, no_prem, prop_true());
    ASSERT_TRUE(r.has_value());
    EXPECT_TRUE(std::get_if<PropTrue>(&r->prop().node));
}

TEST(KernelTest, TrueIntro_WrongConclusion) {
    kernel::Kernel k;
    Prop p{diag::SourceLocation{}, Atomic{"P"}};
    std::vector<kernel::Judgment> no_prem;
    auto r = k.apply(kernel::Rule::TrueIntro, no_prem, p);
    EXPECT_FALSE(r.has_value());
}

TEST(KernelTest, TrueIntro_WrongArity) {
    kernel::Kernel k;
    auto j = k.introduce_axiom(prop_true()); ASSERT_TRUE(j);
    std::vector<kernel::Judgment> prem{*j};
    auto r = k.apply(kernel::Rule::TrueIntro, prem, prop_true());
    EXPECT_FALSE(r.has_value());
}

// ── ForallElim with lambda witness (TR1/TR4 integration) ─────────────────────
//
// This test verifies that definitional equality (beta-reduction) allows
// ForallElim to succeed when the witness is a lambda expression.
//
// Proof structure:
//   axiom:       ∀ f : Nat→Nat, f(0) = 0
//   witness:     fun x => x    (identity function)
//   conclusion:  (fun x => x)(0) = 0
//
// After subst(f(0) = 0, f, fun x => x), the expected proposition is:
//   ExprApp{fun x => x, [0]} = 0
// which is definitionally equal (via beta) to:
//   0 = 0
//
// The conclusion stated is 0 = 0, so defn_eq must accept it.

TEST(KernelTest, ForallElim_LambdaWitness_BetaReduces) {
    kernel::Kernel k;

    // Axiom: ∀ f, f(0) = 0
    // The body is: f(0) = 0, i.e. PropRel{ExprCall{"f",[0]}, Eq, ExprLit{"0"}}
    Prop body = prop_rel(
        Expr{{}, ExprCall{"f", {make_expr(elit("0"))}}},
        RelOp::Eq,
        elit("0"));
    Prop forall_prop = prop_forall("f", body);
    auto j_forall = k.introduce_axiom(forall_prop);
    ASSERT_TRUE(j_forall.has_value());

    // Witness: fun x => x  (identity lambda)
    Expr identity = Expr{{}, ExprLambda{"x", std::nullopt, make_expr(evar("x"))}};

    // Conclusion: 0 = 0
    // This is beta_reduce(subst(f(0)=0, f, fun x => x))
    //   = beta_reduce(ExprApp{fun x=>x,[0]} = 0)
    //   = (0 = 0)
    Prop conclusion = prop_rel(elit("0"), RelOp::Eq, elit("0"));

    std::vector<kernel::Judgment> prem{*j_forall};
    auto result = k.apply(kernel::Rule::ForallElim, prem, conclusion, &identity);
    ASSERT_TRUE(result.has_value()) << (result.has_value() ? "" : result.error().message);
    EXPECT_EQ(result->prop(), conclusion);
}

TEST(KernelTest, ForallElim_LambdaWitness_WrongConclusion) {
    // Same axiom but stating wrong conclusion 1 = 0 — must fail.
    kernel::Kernel k;

    Prop body = prop_rel(
        Expr{{}, ExprCall{"f", {make_expr(elit("0"))}}},
        RelOp::Eq,
        elit("0"));
    Prop forall_prop = prop_forall("f", body);
    auto j_forall = k.introduce_axiom(forall_prop);
    ASSERT_TRUE(j_forall.has_value());

    Expr identity = Expr{{}, ExprLambda{"x", std::nullopt, make_expr(evar("x"))}};

    // Wrong conclusion: 1 = 0 instead of 0 = 0
    Prop wrong_conclusion = prop_rel(elit("1"), RelOp::Eq, elit("0"));

    std::vector<kernel::Judgment> prem{*j_forall};
    auto result = k.apply(kernel::Rule::ForallElim, prem, wrong_conclusion, &identity);
    EXPECT_FALSE(result.has_value());
}
