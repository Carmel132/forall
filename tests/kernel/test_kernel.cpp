#include <gtest/gtest.h>
#include <forall/kernel/kernel.hpp>

using namespace forall;

TEST(KernelTest, AxiomIntroductionProducesJudgment) {
    kernel::Kernel k;
    ast::Prop p{diag::SourceLocation{}, "P"};

    auto result = k.introduce_axiom(p);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->prop().raw, "P");
}

TEST(KernelTest, ApplyingRuleYieldsJudgmentForConclusion) {
    kernel::Kernel k;
    ast::Prop a{diag::SourceLocation{}, "A"};
    ast::Prop b{diag::SourceLocation{}, "B"};

    auto ja = k.introduce_axiom(a);
    ASSERT_TRUE(ja.has_value());

    std::array premises{*ja};
    auto result = k.apply(kernel::Rule::AndElimL, premises, b);

    ASSERT_TRUE(result.has_value());
}
