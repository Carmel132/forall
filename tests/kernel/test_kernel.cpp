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
