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
