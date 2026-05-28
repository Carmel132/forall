#include <gtest/gtest.h>
#include <forall/ast/node.hpp>
#include <forall/diagnostics/diagnostic.hpp>
#include <forall/lexer/lexer.hpp>
#include <forall/parser/parser.hpp>

using namespace forall;
using namespace forall::ast;

// ── Test helpers ───────────────────────────────────────────────────────────────

struct ParseResult {
    diag::DiagnosticEngine diag;
    ast::Module            mod;
};

static ParseResult parse_str(const std::string& src) {
    ParseResult r;
    lexer::Lexer lex{src, "<test>", r.diag};
    auto toks = lex.tokenize();
    parser::Parser p{toks, r.diag};
    r.mod = p.parse();
    return r;
}

// Get the Nth step from a proof block as a specific StepNode type, or nullptr.
template<typename T>
static const T* get_step(const ProofBlock& block, std::size_t i) {
    if (i >= block.steps.size()) return nullptr;
    return std::get_if<T>(&block.steps[i].node);
}

// ── Declarations ───────────────────────────────────────────────────────────────

TEST(ParserTest, Axiom) {
    auto r = parse_str("axiom p_holds : P");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, DeclKind::Axiom);
    EXPECT_EQ(d.name, "p_holds");
    const auto* a = std::get_if<Atomic>(&d.statement.node);
    ASSERT_NE(a, nullptr);
    EXPECT_EQ(a->name, "P");
    EXPECT_FALSE(d.proof.has_value());
}

TEST(ParserTest, TheoremWithProofBlock) {
    auto r = parse_str("theorem t : P\nproof\n  suppose h : P\n  then P by h\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, DeclKind::Theorem);
    EXPECT_EQ(d.name, "t");
    ASSERT_TRUE(d.proof.has_value());
    EXPECT_EQ(d.proof->steps.size(), 2u);
}

TEST(ParserTest, LemmaKind) {
    auto r = parse_str("lemma foo : Q\nproof\n  suppose h : Q\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->kind, DeclKind::Lemma);
}

TEST(ParserTest, MultipleDeclarations) {
    auto r = parse_str("axiom a1 : P\naxiom a2 : Q");
    ASSERT_FALSE(r.diag.hasErrors());
    EXPECT_EQ(r.mod.decls.size(), 2u);
}

// ── Proof steps ────────────────────────────────────────────────────────────────

TEST(ParserTest, SupposeStep) {
    auto r = parse_str("theorem t : P\nproof\n  suppose h : P\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<SupposeStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    ASSERT_TRUE(s->name.has_value());
    EXPECT_EQ(*s->name, "h");
    EXPECT_FALSE(s->for_contradiction);
    EXPECT_NE(std::get_if<Atomic>(&s->prop.node), nullptr);
}

TEST(ParserTest, SupposeStepForContradiction) {
    auto r = parse_str("theorem t : P\nproof\n  suppose for contradiction: h : P\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<SupposeStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    EXPECT_TRUE(s->for_contradiction);
    ASSERT_TRUE(s->name.has_value());
    EXPECT_EQ(*s->name, "h");
}

TEST(ParserTest, HaveStep) {
    auto r = parse_str("theorem t : P\nproof\n  have h : P by h1 and h2\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<HaveStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    EXPECT_EQ(s->name, "h");
    ASSERT_EQ(s->justification.size(), 2u);
    EXPECT_EQ(s->justification[0], "h1");
    EXPECT_EQ(s->justification[1], "h2");
}

TEST(ParserTest, ThenStep) {
    auto r = parse_str("theorem t : P\nproof\n  then P by h1\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<ThenStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    ASSERT_EQ(s->justification.size(), 1u);
    EXPECT_EQ(s->justification[0], "h1");
}

TEST(ParserTest, ThenStepNoBy) {
    auto r = parse_str("theorem t : P\nproof\n  then P\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<ThenStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    EXPECT_TRUE(s->justification.empty());
}

TEST(ParserTest, ContradictionStep) {
    auto r = parse_str("theorem t : P\nproof\n  contradiction : h1 and h2\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<ContradictionStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    ASSERT_EQ(s->justification.size(), 2u);
    EXPECT_EQ(s->justification[0], "h1");
    EXPECT_EQ(s->justification[1], "h2");
}

TEST(ParserTest, LetStep) {
    auto r = parse_str("theorem t : P\nproof\n  let x be a Nat\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<LetStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    EXPECT_EQ(s->var, "x");
    ASSERT_TRUE(s->type.has_value());
    EXPECT_EQ(*s->type, "Nat");
}

// ── Propositions ───────────────────────────────────────────────────────────────

TEST(ParserTest, PropAtomic) {
    auto r = parse_str("axiom a : MyProp");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* a = std::get_if<Atomic>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(a, nullptr);
    EXPECT_EQ(a->name, "MyProp");
}

TEST(ParserTest, PropAnd) {
    auto r = parse_str("axiom a : P and Q");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* c = std::get_if<PropAnd>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(c, nullptr);
    EXPECT_EQ(std::get_if<Atomic>(&c->lhs->node)->name, "P");
    EXPECT_EQ(std::get_if<Atomic>(&c->rhs->node)->name, "Q");
}

TEST(ParserTest, PropOr) {
    auto r = parse_str("axiom a : P or Q");
    ASSERT_FALSE(r.diag.hasErrors());
    EXPECT_NE(std::get_if<PropOr>(&r.mod.decls[0]->statement.node), nullptr);
}

TEST(ParserTest, PropNot) {
    auto r = parse_str("axiom a : not P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* neg = std::get_if<PropNot>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(neg, nullptr);
    EXPECT_NE(std::get_if<Atomic>(&neg->inner->node), nullptr);
}

TEST(ParserTest, PropImplArrow) {
    auto r = parse_str("axiom a : P -> Q");
    ASSERT_FALSE(r.diag.hasErrors());
    EXPECT_NE(std::get_if<PropImpl>(&r.mod.decls[0]->statement.node), nullptr);
}

TEST(ParserTest, PropImplImplies) {
    auto r = parse_str("axiom a : P implies Q");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* im = std::get_if<PropImpl>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(im, nullptr);
    EXPECT_EQ(std::get_if<Atomic>(&im->lhs->node)->name, "P");
    EXPECT_EQ(std::get_if<Atomic>(&im->rhs->node)->name, "Q");
}

TEST(ParserTest, PropIfThen) {
    auto r = parse_str("axiom a : if P then Q");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* im = std::get_if<PropImpl>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(im, nullptr);
    EXPECT_EQ(std::get_if<Atomic>(&im->lhs->node)->name, "P");
    EXPECT_EQ(std::get_if<Atomic>(&im->rhs->node)->name, "Q");
}

TEST(ParserTest, PropFalseKeyword) {
    auto r = parse_str("axiom a : false");
    ASSERT_FALSE(r.diag.hasErrors());
    EXPECT_NE(std::get_if<PropFalse>(&r.mod.decls[0]->statement.node), nullptr);
}

TEST(ParserTest, PropParenthesized) {
    auto r = parse_str("axiom a : (P and Q) -> R");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* im = std::get_if<PropImpl>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(im, nullptr);
    EXPECT_NE(std::get_if<PropAnd>(&im->lhs->node), nullptr);
    EXPECT_NE(std::get_if<Atomic>(&im->rhs->node), nullptr);
}

TEST(ParserTest, PropImplRightAssociative) {
    // P -> Q -> R  must parse as  P -> (Q -> R)
    auto r = parse_str("axiom a : P -> Q -> R");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* outer = std::get_if<PropImpl>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(outer, nullptr);
    EXPECT_NE(std::get_if<Atomic>(&outer->lhs->node), nullptr);   // lhs is P
    EXPECT_NE(std::get_if<PropImpl>(&outer->rhs->node), nullptr);  // rhs is Q -> R
}

TEST(ParserTest, PropImplAndImpliesAreEquivalent) {
    // "P -> Q" and "P implies Q" should produce structurally equal ASTs.
    auto r1 = parse_str("axiom a : P -> Q");
    auto r2 = parse_str("axiom a : P implies Q");
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

// ── Error recovery ─────────────────────────────────────────────────────────────

TEST(ParserTest, MissingColonAfterAxiomName) {
    auto r = parse_str("axiom foo P");
    EXPECT_TRUE(r.diag.hasErrors());
}

TEST(ParserTest, MissingEndKeyword) {
    auto r = parse_str("theorem t : P\nproof\n  suppose h : P");
    EXPECT_TRUE(r.diag.hasErrors());
}

TEST(ParserTest, UnknownTopLevelToken) {
    auto r = parse_str("garbage");
    EXPECT_TRUE(r.diag.hasErrors());
}
