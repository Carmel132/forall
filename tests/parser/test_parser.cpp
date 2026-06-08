#include <gtest/gtest.h>
#include <forall/ast/node.hpp>
#include <forall/diagnostics/diagnostic.hpp>
#include <forall/lexer/lexer.hpp>
#include <forall/parser/parser.hpp>
#include <forall/pretty/to_string.hpp>

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

TEST(ParserTest, LetBeForm_StillWorks) {
    auto r = parse_str("theorem t : P\nproof\n  let x be a Nat\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<LetStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    EXPECT_EQ(s->var, "x");
    ASSERT_TRUE(s->type.has_value());
    EXPECT_FALSE(s->definition.has_value());
    EXPECT_EQ(forall::pretty::to_string(*s->type), "Nat");
}

TEST(ParserTest, LetExprForm) {
    auto r = parse_str("theorem t : P\nproof\n  let x = 42\nend");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<LetStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    EXPECT_EQ(s->var, "x");
    EXPECT_FALSE(s->type.has_value());
    ASSERT_TRUE(s->definition.has_value());
    // Check the definition is ExprLit{42}
    const auto* lit = std::get_if<ExprLit>(&(*s->definition)->node);
    ASSERT_NE(lit, nullptr);
    EXPECT_EQ(lit->value, "42");
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

// ── Quantifiers ────────────────────────────────────────────────────────────────

TEST(ParserTest, QuantifierForAll) {
    auto r = parse_str("axiom a : for all x, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    EXPECT_EQ(fa->var, "x");
    EXPECT_FALSE(fa->type.has_value());
    EXPECT_NE(std::get_if<Atomic>(&fa->body->node), nullptr);
}

TEST(ParserTest, QuantifierForAllTyped) {
    auto r = parse_str("axiom a : for all x : Nat, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    EXPECT_EQ(fa->var, "x");
    ASSERT_TRUE(fa->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*fa->type), "Nat");
    EXPECT_NE(std::get_if<Atomic>(&fa->body->node), nullptr);
}

TEST(ParserTest, QuantifierExists) {
    auto r = parse_str("axiom a : there exists x, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ex = std::get_if<PropExists>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(ex, nullptr);
    EXPECT_EQ(ex->var, "x");
    EXPECT_FALSE(ex->type.has_value());
}

TEST(ParserTest, QuantifierUnicodeForall) {
    // ∀ U+2200 → UTF-8 E2 88 80
    auto r = parse_str("axiom a : \xE2\x88\x80 x, P");
    ASSERT_FALSE(r.diag.hasErrors());
    EXPECT_NE(std::get_if<PropForall>(&r.mod.decls[0]->statement.node), nullptr);
}

TEST(ParserTest, QuantifierUnicodeExists) {
    // ∃ U+2203 → UTF-8 E2 88 83
    auto r = parse_str("axiom a : \xE2\x88\x83 x, P");
    ASSERT_FALSE(r.diag.hasErrors());
    EXPECT_NE(std::get_if<PropExists>(&r.mod.decls[0]->statement.node), nullptr);
}

TEST(ParserTest, QuantifierInImplication) {
    // "P -> for all x, Q"  parses as  P -> (for all x, Q)
    auto r = parse_str("axiom a : P -> for all x, Q");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* im = std::get_if<PropImpl>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(im, nullptr);
    EXPECT_NE(std::get_if<Atomic>(&im->lhs->node), nullptr);
    EXPECT_NE(std::get_if<PropForall>(&im->rhs->node), nullptr);
}

TEST(ParserTest, QuantifierNestedForall) {
    // "for all x, for all y, P"  parses as  ∀ x, (∀ y, P)
    auto r = parse_str("axiom a : for all x, for all y, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* outer = std::get_if<PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(outer, nullptr);
    EXPECT_EQ(outer->var, "x");
    EXPECT_NE(std::get_if<PropForall>(&outer->body->node), nullptr);
}

TEST(ParserTest, ErrorRecoveryUnknownStep) {
    // Unknown step token: parser emits an error and produces a silent sentinel.
    // Subsequent valid steps are still parsed correctly.
    auto r = parse_str("theorem t : P\nproof\n  bad_token\n  then P by h\nend");
    EXPECT_TRUE(r.diag.hasErrors());
    ASSERT_TRUE(r.mod.decls[0]->proof.has_value());
    EXPECT_EQ(r.mod.decls[0]->proof->steps.size(), 2u);
    // Second step (the 'then') is parsed despite the earlier error
    EXPECT_NE(std::get_if<ThenStep>(&r.mod.decls[0]->proof->steps[1].node), nullptr);
}

// ── Core arithmetic — expressions and relational propositions ──────────────────
//
// Coverage map:
//   Item 1  Numeric literals         → ExprNumericLiteral
//   Item 2  Basic arithmetic         → ExprArithmetic*, PropRelSimple
//   Item 3  Absolute value           → ExprAbsoluteValue, PropRelAbsValue
//   Item 4  Function application     → ExprFunctionCall, PropPredicate
//   Item 5  Relational propositions  → PropRelSimple, PropRelInConjunction, PropRelNested
//   Item 6  Exponentiation           → ExprExponentiation
//   Item 7  Integer div / mod        → ExprDivMod

// ── Item 1: Numeric literals ───────────────────────────────────────────────────

TEST(ParserTest, ExprNumericLiteralInt) {
    // Integer literal appears as lhs of a relational prop
    auto r = parse_str("axiom a : 42 >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::GtEq);
    const auto* lit = std::get_if<ExprLit>(&rel->lhs->node);
    ASSERT_NE(lit, nullptr);
    EXPECT_EQ(lit->value, "42");
}

TEST(ParserTest, ExprNumericLiteralDecimal) {
    auto r = parse_str("axiom a : 3.14 > 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* lit = std::get_if<ExprLit>(&rel->lhs->node);
    ASSERT_NE(lit, nullptr);
    EXPECT_EQ(lit->value, "3.14");
}

// ── Item 2: Basic arithmetic ───────────────────────────────────────────────────

TEST(ParserTest, ExprArithmeticAddSub) {
    // n + 1 > n  parses as PropRel{ ExprBinary{Add,n,1}, Gt, ExprVar{n} }
    auto r = parse_str("axiom a : n + 1 > n");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::Gt);
    const auto* add = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(add, nullptr);
    EXPECT_EQ(add->op, BinOp::Add);
}

TEST(ParserTest, ExprArithmeticMulDiv) {
    // 2 * x = x + x
    auto r = parse_str("axiom a : 2 * x = x + x");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::Eq);
    const auto* mul = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(mul, nullptr);
    EXPECT_EQ(mul->op, BinOp::Mul);
}

TEST(ParserTest, ExprArithmeticPrecedence) {
    // 1 + 2 * 3 = 7  — multiplication binds tighter than addition
    auto r = parse_str("axiom a : 1 + 2 * 3 = 7");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* add = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(add, nullptr);
    EXPECT_EQ(add->op, BinOp::Add);
    // rhs of add should be the 2*3 multiplication
    const auto* mul = std::get_if<ExprBinary>(&add->rhs->node);
    ASSERT_NE(mul, nullptr);
    EXPECT_EQ(mul->op, BinOp::Mul);
}

TEST(ParserTest, ExprUnaryNegation) {
    auto r = parse_str("axiom a : -x < 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* neg = std::get_if<ExprUnary>(&rel->lhs->node);
    ASSERT_NE(neg, nullptr);
    EXPECT_EQ(neg->op, UnaryOp::Neg);
}

// ── Item 3: Absolute value ─────────────────────────────────────────────────────

TEST(ParserTest, ExprAbsoluteValue) {
    // |x| >= 0  parses as PropRel{ ExprAbs{x}, GtEq, ExprLit{0} }
    auto r = parse_str("axiom a : |x| >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::GtEq);
    EXPECT_NE(std::get_if<ExprAbs>(&rel->lhs->node), nullptr);
}

TEST(ParserTest, PropRelAbsValue) {
    // |a - b| < eps
    auto r = parse_str("axiom a : |a - b| < eps");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::Lt);
    const auto* abs = std::get_if<ExprAbs>(&rel->lhs->node);
    ASSERT_NE(abs, nullptr);
    // inner of |...| is a subtraction
    const auto* sub = std::get_if<ExprBinary>(&abs->operand->node);
    ASSERT_NE(sub, nullptr);
    EXPECT_EQ(sub->op, BinOp::Sub);
}

// ── Item 4: Function application ───────────────────────────────────────────────

TEST(ParserTest, ExprFunctionCallInRelProp) {
    // f(x) > 0  —  ExprCall as lhs of a relational prop
    auto r = parse_str("axiom a : f(x) > 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "f");
    ASSERT_EQ(call->args.size(), 1u);
}

TEST(ParserTest, ExprFunctionCallMultiArg) {
    // g(x, y, z) = 0
    auto r = parse_str("axiom a : g(x, y, z) = 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "g");
    EXPECT_EQ(call->args.size(), 3u);
}

TEST(ParserTest, PropPredicate) {
    // isPrime(n)  alone as a proposition → PropPred
    auto r = parse_str("axiom a : isPrime(n)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* pred = std::get_if<PropPred>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(pred, nullptr);
    EXPECT_EQ(pred->name, "isPrime");
    EXPECT_EQ(pred->args.size(), 1u);
}

// ── Item 5: Relational propositions ───────────────────────────────────────────

TEST(ParserTest, PropRelAllSixOperators) {
    // Each relational operator parses correctly
    struct Case { const char* src; RelOp expected; };
    const Case cases[] = {
        {"axiom a : x <  y", RelOp::Lt   },
        {"axiom a : x >  y", RelOp::Gt   },
        {"axiom a : x <= y", RelOp::LtEq },
        {"axiom a : x >= y", RelOp::GtEq },
        {"axiom a : x =  y", RelOp::Eq   },
        {"axiom a : x /= y", RelOp::NotEq},
    };
    for (const auto& c : cases) {
        auto r = parse_str(c.src);
        ASSERT_FALSE(r.diag.hasErrors()) << "failed for: " << c.src;
        const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
        ASSERT_NE(rel, nullptr) << "not PropRel for: " << c.src;
        EXPECT_EQ(rel->op, c.expected) << "wrong op for: " << c.src;
    }
}

TEST(ParserTest, PropRelUnicodeOperators) {
    // Unicode ≤ / ≥ / ≠ produce the same tokens as <= / >= / /=
    auto r1 = parse_str("axiom a : x <= y");
    auto r2 = parse_str("axiom a : x \xE2\x89\xA4 y"); // ≤ U+2264
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, PropRelInConjunction) {
    // P and n >= 0  — relational atom inside a propositional connective
    auto r = parse_str("axiom a : P and n >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* conj = std::get_if<PropAnd>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(conj, nullptr);
    EXPECT_NE(std::get_if<Atomic>(&conj->lhs->node), nullptr);
    EXPECT_NE(std::get_if<PropRel>(&conj->rhs->node), nullptr);
}

TEST(ParserTest, PropRelParenthesized) {
    // (x + 1 < n) as a parenthesized prop
    auto r = parse_str("axiom a : (x + 1 < n) and P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* conj = std::get_if<PropAnd>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(conj, nullptr);
    EXPECT_NE(std::get_if<PropRel>(&conj->lhs->node), nullptr);
}

// ── Item 6: Exponentiation ─────────────────────────────────────────────────────

TEST(ParserTest, ExprExponentiation) {
    // x ^ 2 >= 0
    auto r = parse_str("axiom a : x ^ 2 >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* pow = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(pow, nullptr);
    EXPECT_EQ(pow->op, BinOp::Pow);
}

TEST(ParserTest, ExprExponentiationRightAssoc) {
    // x ^ y ^ z  parses as  x ^ (y ^ z)
    auto r = parse_str("axiom a : x ^ y ^ z = 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* outer = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(outer, nullptr);
    EXPECT_EQ(outer->op, BinOp::Pow);
    // rhs of outer ^ is also a ^
    EXPECT_NE(std::get_if<ExprBinary>(&outer->rhs->node), nullptr);
}

TEST(ParserTest, ExprExponentiationBindsTighterThanMul) {
    // 2 * x ^ 3  parses as  2 * (x ^ 3), not  (2 * x) ^ 3
    auto r = parse_str("axiom a : 2 * x ^ 3 = 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* mul = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(mul, nullptr);
    EXPECT_EQ(mul->op, BinOp::Mul);
    EXPECT_NE(std::get_if<ExprBinary>(&mul->rhs->node), nullptr); // x^3 on rhs
}

// ── Item 7: Integer division and modulo ────────────────────────────────────────

TEST(ParserTest, ExprIntegerDiv) {
    // n div 2 >= 0
    auto r = parse_str("axiom a : n div 2 >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* idiv = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(idiv, nullptr);
    EXPECT_EQ(idiv->op, BinOp::IDiv);
}

TEST(ParserTest, ExprModulo) {
    // n mod 2 = 0
    auto r = parse_str("axiom a : n mod 2 = 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* mod = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(mod, nullptr);
    EXPECT_EQ(mod->op, BinOp::Mod);
    // rhs of mod is literal 2; lhs is var n
    EXPECT_NE(std::get_if<ExprVar>(&mod->lhs->node), nullptr);
    EXPECT_NE(std::get_if<ExprLit>(&mod->rhs->node), nullptr);
}

TEST(ParserTest, ExprDivBindsTighterThanAdd) {
    // n div 2 + 1  parses as  (n div 2) + 1
    auto r = parse_str("axiom a : n div 2 + 1 = 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* add = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(add, nullptr);
    EXPECT_EQ(add->op, BinOp::Add);
    EXPECT_NE(std::get_if<ExprBinary>(&add->lhs->node), nullptr); // n div 2 on lhs
}

// ── Item 8: Subscript indexing ─────────────────────────────────────────────────

TEST(ParserTest, ExprSubscriptSimple) {
    // a[n] >= 0  —  ExprIndex{ExprVar{a}, ExprVar{n}} as lhs of relational prop
    auto r = parse_str("axiom a : a[n] >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* idx = std::get_if<ExprIndex>(&rel->lhs->node);
    ASSERT_NE(idx, nullptr);
    EXPECT_NE(std::get_if<ExprVar>(&idx->array->node), nullptr);
    EXPECT_NE(std::get_if<ExprVar>(&idx->index->node), nullptr);
}

TEST(ParserTest, ExprSubscriptLiteralIndex) {
    // a[0] = 1  —  literal index
    auto r = parse_str("axiom a : a[0] = 1");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* idx = std::get_if<ExprIndex>(&rel->lhs->node);
    ASSERT_NE(idx, nullptr);
    const auto* lit = std::get_if<ExprLit>(&idx->index->node);
    ASSERT_NE(lit, nullptr);
    EXPECT_EQ(lit->value, "0");
}

TEST(ParserTest, ExprSubscriptExpressionIndex) {
    // a[n + 1] = 0  —  full expression as index
    auto r = parse_str("axiom a : a[n + 1] = 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* idx = std::get_if<ExprIndex>(&rel->lhs->node);
    ASSERT_NE(idx, nullptr);
    const auto* add = std::get_if<ExprBinary>(&idx->index->node);
    ASSERT_NE(add, nullptr);
    EXPECT_EQ(add->op, BinOp::Add);
}

TEST(ParserTest, ExprSubscriptChained) {
    // a[i][j] = 0  —  left-associative: (a[i])[j]
    auto r = parse_str("axiom a : a[i][j] = 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* outer = std::get_if<ExprIndex>(&rel->lhs->node);
    ASSERT_NE(outer, nullptr);
    // outer index is j
    const auto* jvar = std::get_if<ExprVar>(&outer->index->node);
    ASSERT_NE(jvar, nullptr);
    EXPECT_EQ(jvar->name, "j");
    // array of outer is itself an index a[i]
    const auto* inner = std::get_if<ExprIndex>(&outer->array->node);
    ASSERT_NE(inner, nullptr);
    EXPECT_NE(std::get_if<ExprVar>(&inner->array->node), nullptr);
    EXPECT_NE(std::get_if<ExprVar>(&inner->index->node), nullptr);
}

TEST(ParserTest, ExprSubscriptBindsTighterThanPow) {
    // a[n] ^ 2  parses as  (a[n]) ^ 2,  not  a[n^2]
    auto r = parse_str("axiom a : a[n] ^ 2 = 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* pw = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(pw, nullptr);
    EXPECT_EQ(pw->op, BinOp::Pow);
    // base of ^ is a[n]
    EXPECT_NE(std::get_if<ExprIndex>(&pw->lhs->node), nullptr);
    // exponent of ^ is literal 2
    EXPECT_NE(std::get_if<ExprLit>(&pw->rhs->node), nullptr);
}

// ── Item 9: Tuple / pair construction ─────────────────────────────────────────

TEST(ParserTest, ExprTuplePair) {
    // pair = (1, 2)  —  ExprTuple as rhs of a relational prop
    auto r = parse_str("axiom a : pair = (1, 2)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* tup = std::get_if<ExprTuple>(&rel->rhs->node);
    ASSERT_NE(tup, nullptr);
    ASSERT_EQ(tup->elements.size(), 2u);
    EXPECT_NE(std::get_if<ExprLit>(&tup->elements[0]->node), nullptr);
    EXPECT_NE(std::get_if<ExprLit>(&tup->elements[1]->node), nullptr);
}

TEST(ParserTest, ExprTupleTriple) {
    // triple = (a, b, c)  —  three-element tuple
    auto r = parse_str("axiom a : triple = (x, y, z)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* tup = std::get_if<ExprTuple>(&rel->rhs->node);
    ASSERT_NE(tup, nullptr);
    EXPECT_EQ(tup->elements.size(), 3u);
}

TEST(ParserTest, ExprTupleVsGrouping) {
    // a[(n + 1)] > 0  —  a single parenthesised expression inside a subscript is
    // grouping (transparent), NOT a single-element tuple.
    auto r = parse_str("axiom a : a[(n + 1)] > 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* idx = std::get_if<ExprIndex>(&rel->lhs->node);
    ASSERT_NE(idx, nullptr);
    // index is the addition, not a tuple
    EXPECT_EQ(std::get_if<ExprTuple>(&idx->index->node), nullptr);
    const auto* add = std::get_if<ExprBinary>(&idx->index->node);
    ASSERT_NE(add, nullptr);
    EXPECT_EQ(add->op, BinOp::Add);
}

TEST(ParserTest, ExprTupleVsFunctionCall) {
    // f(a, b) = 0  —  function call with two args, NOT a function call with a tuple
    auto r = parse_str("axiom a : f(x, y) = 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "f");
    EXPECT_EQ(call->args.size(), 2u);              // two separate args, not one tuple
    EXPECT_EQ(std::get_if<ExprTuple>(&call->args[0]->node), nullptr);
}

TEST(ParserTest, ExprTupleAsFunctionArg) {
    // f((1, 2)) = 0  —  function call with one argument that is a tuple
    auto r = parse_str("axiom a : f((1, 2)) = 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    ASSERT_EQ(call->args.size(), 1u);              // one argument: the tuple
    const auto* tup = std::get_if<ExprTuple>(&call->args[0]->node);
    ASSERT_NE(tup, nullptr);
    EXPECT_EQ(tup->elements.size(), 2u);
}

// ── Item 10: Lambda abstraction ───────────────────────────────────────────────

TEST(ParserTest, LambdaBasic) {
    // f = fun x => x  —  bare lambda, no type annotation
    auto r = parse_str("axiom a : f = fun x => x");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* lam = std::get_if<ExprLambda>(&rel->rhs->node);
    ASSERT_NE(lam, nullptr);
    EXPECT_EQ(lam->var, "x");
    EXPECT_FALSE(lam->type.has_value());
    EXPECT_NE(std::get_if<ExprVar>(&lam->body->node), nullptr);
}

TEST(ParserTest, LambdaTyped) {
    // f = fun x : Nat => x + 1
    auto r = parse_str("axiom a : f = fun x : Nat => x + 1");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* lam = std::get_if<ExprLambda>(&rel->rhs->node);
    ASSERT_NE(lam, nullptr);
    EXPECT_EQ(lam->var, "x");
    ASSERT_TRUE(lam->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*lam->type), "Nat");
    const auto* add = std::get_if<ExprBinary>(&lam->body->node);
    ASSERT_NE(add, nullptr);
    EXPECT_EQ(add->op, BinOp::Add);
}

TEST(ParserTest, LambdaUnicode) {
    // f = λ x, x  — Unicode λ with comma separator
    auto r = parse_str("axiom a : f = \xCE\xBB x, x");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* lam = std::get_if<ExprLambda>(&rel->rhs->node);
    ASSERT_NE(lam, nullptr);
    EXPECT_EQ(lam->var, "x");
    EXPECT_NE(std::get_if<ExprVar>(&lam->body->node), nullptr);
}

TEST(ParserTest, LambdaUnicodeTyped) {
    // f = λ x : Real, x * x — Unicode λ with type
    auto r = parse_str("axiom a : f = \xCE\xBB x : Real, x * x");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* lam = std::get_if<ExprLambda>(&rel->rhs->node);
    ASSERT_NE(lam, nullptr);
    EXPECT_EQ(lam->var, "x");
    ASSERT_TRUE(lam->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*lam->type), "Real");
    EXPECT_NE(std::get_if<ExprBinary>(&lam->body->node), nullptr);
}

TEST(ParserTest, LambdaNested) {
    // f = fun x => fun y => x + y  — nested lambdas; outer body is a lambda
    auto r = parse_str("axiom a : f = fun x => fun y => x + y");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* outer = std::get_if<ExprLambda>(&rel->rhs->node);
    ASSERT_NE(outer, nullptr);
    EXPECT_EQ(outer->var, "x");
    const auto* inner = std::get_if<ExprLambda>(&outer->body->node);
    ASSERT_NE(inner, nullptr);
    EXPECT_EQ(inner->var, "y");
    EXPECT_NE(std::get_if<ExprBinary>(&inner->body->node), nullptr);
}

TEST(ParserTest, LambdaBodyExtendsRight) {
    // f = fun x => x + 1 — body is x+1, not just x
    auto r = parse_str("axiom a : f = fun x => x + 1");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* lam = std::get_if<ExprLambda>(&rel->rhs->node);
    ASSERT_NE(lam, nullptr);
    // Body is the full addition, not just x
    const auto* add = std::get_if<ExprBinary>(&lam->body->node);
    ASSERT_NE(add, nullptr);
    EXPECT_EQ(add->op, BinOp::Add);
}

TEST(ParserTest, LambdaAsArg) {
    // apply(fun x => x, 3) = 3 — lambda as function argument
    auto r = parse_str("axiom a : apply(fun x => x, 3) = 3");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "apply");
    ASSERT_EQ(call->args.size(), 2u);
    EXPECT_NE(std::get_if<ExprLambda>(&call->args[0]->node), nullptr);
    EXPECT_NE(std::get_if<ExprLit>(&call->args[1]->node), nullptr);
}

// ── Item 11: Conditional term ─────────────────────────────────────────────────

TEST(ParserTest, CondExprBasic) {
    // n and (if x > 0 then x else 0) >= 0 — conditional in relational prop via "and"
    // (Reached through parseConjunction -> parseAtomicProp -> parseExpr -> parseCondExpr)
    auto r = parse_str("axiom a : P and if x > 0 then x else 0 >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* conj = std::get_if<PropAnd>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(conj, nullptr);
    // RHS of "and" is the relational: (if x>0 then x else 0) >= 0
    const auto* rel = std::get_if<PropRel>(&conj->rhs->node);
    ASSERT_NE(rel, nullptr);
    const auto* cond = std::get_if<ExprIf>(&rel->lhs->node);
    ASSERT_NE(cond, nullptr);
}

TEST(ParserTest, CondExprCondition) {
    // Verify the condition, then-branch, and else-branch are stored correctly
    auto r = parse_str("axiom a : P and if x > 0 then x else 0 = x");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* conj = std::get_if<PropAnd>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(conj, nullptr);
    const auto* rel = std::get_if<PropRel>(&conj->rhs->node);
    ASSERT_NE(rel, nullptr);
    const auto* cond = std::get_if<ExprIf>(&rel->lhs->node);
    ASSERT_NE(cond, nullptr);
    // condition is PropRel{x, 0, Gt}
    EXPECT_NE(std::get_if<PropRel>(&cond->cond->node), nullptr);
    // then-branch is ExprVar{x}
    EXPECT_NE(std::get_if<ExprVar>(&cond->then_->node), nullptr);
    // else-branch is ExprLit{0}
    EXPECT_NE(std::get_if<ExprLit>(&cond->else_->node), nullptr);
}

TEST(ParserTest, CondExprNested) {
    // if P then (if Q then a else b) else c — outer is conditional, inner is conditional
    auto r = parse_str("axiom a : P and if P then if Q then x else y else z = w");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* conj = std::get_if<PropAnd>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(conj, nullptr);
    const auto* rel = std::get_if<PropRel>(&conj->rhs->node);
    ASSERT_NE(rel, nullptr);
    const auto* outer = std::get_if<ExprIf>(&rel->lhs->node);
    ASSERT_NE(outer, nullptr);
    // then-branch of outer is another ExprIf
    EXPECT_NE(std::get_if<ExprIf>(&outer->then_->node), nullptr);
    // else-branch of outer is ExprVar{z}
    EXPECT_NE(std::get_if<ExprVar>(&outer->else_->node), nullptr);
}

TEST(ParserTest, CondExprElseBranchExtendsRight) {
    // if P then a else b + 1  —  else-branch is b+1, not just b
    auto r = parse_str("axiom a : P and if P then a else b + 1 = c");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* conj = std::get_if<PropAnd>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(conj, nullptr);
    const auto* rel = std::get_if<PropRel>(&conj->rhs->node);
    ASSERT_NE(rel, nullptr);
    const auto* cond = std::get_if<ExprIf>(&rel->lhs->node);
    ASSERT_NE(cond, nullptr);
    // else-branch is b + 1
    const auto* add = std::get_if<ExprBinary>(&cond->else_->node);
    ASSERT_NE(add, nullptr);
    EXPECT_EQ(add->op, BinOp::Add);
}

TEST(ParserTest, CondExprInLambda) {
    // f = fun x => if x > 0 then x else 0 — conditional inside lambda body
    auto r = parse_str("axiom a : f = fun x => if x > 0 then x else 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* lam = std::get_if<ExprLambda>(&rel->rhs->node);
    ASSERT_NE(lam, nullptr);
    EXPECT_NE(std::get_if<ExprIf>(&lam->body->node), nullptr);
}

TEST(ParserTest, CondExprWithRelationalCondition) {
    // Condition is a relational prop: if a >= b then a else b
    auto r = parse_str("axiom a : P and if a >= b then a else b = max_val");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* conj = std::get_if<PropAnd>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(conj, nullptr);
    const auto* rel = std::get_if<PropRel>(&conj->rhs->node);
    ASSERT_NE(rel, nullptr);
    const auto* cond = std::get_if<ExprIf>(&rel->lhs->node);
    ASSERT_NE(cond, nullptr);
    // condition is a >= b (PropRel with GtEq)
    const auto* cond_rel = std::get_if<PropRel>(&cond->cond->node);
    ASSERT_NE(cond_rel, nullptr);
    EXPECT_EQ(cond_rel->op, RelOp::GtEq);
}

// ── Item 12: Aggregate operators (sum, prod, floor/ceil, factorial) ──────────────

TEST(ParserTest, SumTypedBinder) {
    // sum i : Nat, i >= 0  — typed binder form
    auto r = parse_str("axiom s : sum i : Nat, i >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* agg = std::get_if<ExprAgg>(&rel->lhs->node);
    ASSERT_NE(agg, nullptr);
    EXPECT_EQ(agg->op, AggOp::Sum);
    EXPECT_EQ(agg->var, "i");
    ASSERT_TRUE(agg->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*agg->type), "Nat");
    EXPECT_FALSE(agg->rel.has_value());
    EXPECT_FALSE(agg->bound.has_value());
    EXPECT_NE(std::get_if<ExprVar>(&agg->body->node), nullptr);
}

TEST(ParserTest, SumBoundedBinder) {
    // sum i < n, i >= 0  — bounded binder form
    auto r = parse_str("axiom s : sum i < n, i >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* agg = std::get_if<ExprAgg>(&rel->lhs->node);
    ASSERT_NE(agg, nullptr);
    EXPECT_EQ(agg->op, AggOp::Sum);
    EXPECT_EQ(agg->var, "i");
    EXPECT_FALSE(agg->type.has_value());
    ASSERT_TRUE(agg->rel.has_value());
    EXPECT_EQ(*agg->rel, RelOp::Lt);
    ASSERT_TRUE(agg->bound.has_value());
    EXPECT_NE(std::get_if<ExprVar>(&(*agg->bound)->node), nullptr);
    EXPECT_NE(std::get_if<ExprVar>(&agg->body->node), nullptr);
}

TEST(ParserTest, ProdTypedBinder) {
    // prod i : Nat, i >= 0
    auto r = parse_str("axiom p : prod i : Nat, i >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* agg = std::get_if<ExprAgg>(&rel->lhs->node);
    ASSERT_NE(agg, nullptr);
    EXPECT_EQ(agg->op, AggOp::Prod);
    ASSERT_TRUE(agg->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*agg->type), "Nat");
    EXPECT_FALSE(agg->rel.has_value());
}

TEST(ParserTest, ProdBoundedBinder) {
    // prod i <= n, i >= 0  — bounded with <=
    auto r = parse_str("axiom p : prod i <= n, i >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* agg = std::get_if<ExprAgg>(&rel->lhs->node);
    ASSERT_NE(agg, nullptr);
    EXPECT_EQ(agg->op, AggOp::Prod);
    ASSERT_TRUE(agg->rel.has_value());
    EXPECT_EQ(*agg->rel, RelOp::LtEq);
    ASSERT_TRUE(agg->bound.has_value());
}

TEST(ParserTest, SumUnicode) {
    // ∑ i : Nat, i >= 0  — Unicode ∑ (U+2211 = E2 88 91) produces identical AST to "sum"
    auto r1 = parse_str("axiom s : sum i : Nat, i >= 0");
    auto r2 = parse_str("axiom s : \xE2\x88\x91 i : Nat, i >= 0");
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, ProdUnicode) {
    // ∏ i : Nat, i >= 0  — Unicode ∏ (U+220F = E2 88 8F) produces identical AST to "prod"
    auto r1 = parse_str("axiom p : prod i : Nat, i >= 0");
    auto r2 = parse_str("axiom p : \xE2\x88\x8F i : Nat, i >= 0");
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, SumNested) {
    // sum i : Nat, sum j : Nat, i + j >= 0 — outer body is another sum
    auto r = parse_str("axiom s : sum i : Nat, sum j : Nat, i + j >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* outer = std::get_if<ExprAgg>(&rel->lhs->node);
    ASSERT_NE(outer, nullptr);
    EXPECT_EQ(outer->op, AggOp::Sum);
    EXPECT_EQ(outer->var, "i");
    const auto* inner = std::get_if<ExprAgg>(&outer->body->node);
    ASSERT_NE(inner, nullptr);
    EXPECT_EQ(inner->op, AggOp::Sum);
    EXPECT_EQ(inner->var, "j");
}

TEST(ParserTest, SumBodyExtendsRight) {
    // sum i : Nat, i * i = n  —  body grabs "i*i"; equality is at the outer level
    auto r = parse_str("axiom s : sum i : Nat, i * i = n");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::Eq);
    const auto* agg = std::get_if<ExprAgg>(&rel->lhs->node);
    ASSERT_NE(agg, nullptr);
    const auto* mul = std::get_if<ExprBinary>(&agg->body->node);
    ASSERT_NE(mul, nullptr);
    EXPECT_EQ(mul->op, BinOp::Mul);
    EXPECT_NE(std::get_if<ExprVar>(&rel->rhs->node), nullptr); // rhs of whole prop is n
}

TEST(ParserTest, FloorUnicode) {
    // ⌊x⌋ desugars to ExprCall{"floor", [x]}  (U+230A/230B = E2 8C 8A/8B)
    auto r = parse_str("axiom f : \xE2\x8C\x8A x \xE2\x8C\x8B >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "floor");
    ASSERT_EQ(call->args.size(), 1u);
    EXPECT_NE(std::get_if<ExprVar>(&call->args[0]->node), nullptr);
}

TEST(ParserTest, CeilUnicode) {
    // ⌈x⌉ desugars to ExprCall{"ceil", [x]}  (U+2308/2309 = E2 8C 88/89)
    auto r = parse_str("axiom c : \xE2\x8C\x88 x \xE2\x8C\x89 >= 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "ceil");
    ASSERT_EQ(call->args.size(), 1u);
}

TEST(ParserTest, FloorUnicodeSameAsKeyword) {
    // ⌊x⌋ produces the same AST as floor(x)
    auto r1 = parse_str("axiom f : floor(x) >= 0");
    auto r2 = parse_str("axiom f : \xE2\x8C\x8A x \xE2\x8C\x8B >= 0");
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, FactorialBasic) {
    // n! > 0  — postfix !, desugars to ExprCall{"factorial", [n]}
    auto r = parse_str("axiom f : n! > 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "factorial");
    ASSERT_EQ(call->args.size(), 1u);
    EXPECT_NE(std::get_if<ExprVar>(&call->args[0]->node), nullptr);
}

TEST(ParserTest, FactorialBindsTighterThanPow) {
    // n!^2 parses as (n!)^2  — factorial is tighter than exponentiation
    auto r = parse_str("axiom f : n! ^ 2 = m");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* pw = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(pw, nullptr);
    EXPECT_EQ(pw->op, BinOp::Pow);
    const auto* call = std::get_if<ExprCall>(&pw->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "factorial");
    EXPECT_NE(std::get_if<ExprLit>(&pw->rhs->node), nullptr);
}

TEST(ParserTest, FactorialOnSubscript) {
    // a[n]! parses as factorial(a[n])  — postfix chain: subscript then factorial
    auto r = parse_str("axiom f : a[n]! = m");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "factorial");
    ASSERT_EQ(call->args.size(), 1u);
    EXPECT_NE(std::get_if<ExprIndex>(&call->args[0]->node), nullptr);
}

// ── Item 13: Algebraic operators (compose / ∘, inv) ──────────────────────────

TEST(ParserTest, ComposeKeyword) {
    // f compose g = h  —  infix compose → ExprBinary{Compose, f, g}
    auto r = parse_str("axiom a : f compose g = h");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* comp = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(comp, nullptr);
    EXPECT_EQ(comp->op, BinOp::Compose);
    EXPECT_NE(std::get_if<ExprVar>(&comp->lhs->node), nullptr);
    EXPECT_NE(std::get_if<ExprVar>(&comp->rhs->node), nullptr);
}

TEST(ParserTest, CircKeyword) {
    // f circ g = h  —  "circ" is an alias for "compose"; identical AST
    auto r1 = parse_str("axiom a : f compose g = h");
    auto r2 = parse_str("axiom a : f circ g = h");
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, ComposeUnicode) {
    // f ∘ g = h  —  Unicode ∘ (U+2218 = E2 88 98) produces identical AST to keyword
    auto r1 = parse_str("axiom a : f compose g = h");
    auto r2 = parse_str("axiom a : f \xE2\x88\x98 g = h");
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, ComposeLeftAssoc) {
    // f compose g compose h  =  (f ∘ g) ∘ h  (left-associative, like *)
    auto r = parse_str("axiom a : f compose g compose h = k");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* outer = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(outer, nullptr);
    EXPECT_EQ(outer->op, BinOp::Compose);
    // lhs of outer is also a compose (f ∘ g)
    const auto* inner = std::get_if<ExprBinary>(&outer->lhs->node);
    ASSERT_NE(inner, nullptr);
    EXPECT_EQ(inner->op, BinOp::Compose);
    // rhs of outer is h (a bare variable)
    EXPECT_NE(std::get_if<ExprVar>(&outer->rhs->node), nullptr);
}

TEST(ParserTest, ComposeBindsTighterThanAdd) {
    // f compose g + h = k  →  (f ∘ g) + h = k  (compose at mul-level, tighter than +)
    auto r = parse_str("axiom a : f compose g + h = k");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* add = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(add, nullptr);
    EXPECT_EQ(add->op, BinOp::Add);
    // lhs of + is the compose
    const auto* comp = std::get_if<ExprBinary>(&add->lhs->node);
    ASSERT_NE(comp, nullptr);
    EXPECT_EQ(comp->op, BinOp::Compose);
    // rhs of + is h
    EXPECT_NE(std::get_if<ExprVar>(&add->rhs->node), nullptr);
}

TEST(ParserTest, InvBasic) {
    // inv f = g  —  prefix inv desugars to ExprCall{"inv", [f]}
    auto r = parse_str("axiom a : inv f = g");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "inv");
    ASSERT_EQ(call->args.size(), 1u);
    EXPECT_NE(std::get_if<ExprVar>(&call->args[0]->node), nullptr);
}

TEST(ParserTest, InvFunctionCall) {
    // inv f(x) = g  —  inv applies to the function call f(x), not just the identifier f
    auto r = parse_str("axiom a : inv f(x) = g");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* inv_call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(inv_call, nullptr);
    EXPECT_EQ(inv_call->name, "inv");
    ASSERT_EQ(inv_call->args.size(), 1u);
    // argument is f(x), itself a call
    const auto* inner = std::get_if<ExprCall>(&inv_call->args[0]->node);
    ASSERT_NE(inner, nullptr);
    EXPECT_EQ(inner->name, "f");
    EXPECT_EQ(inner->args.size(), 1u);
}

TEST(ParserTest, InvBindsTighterThanCompose) {
    // inv f compose g = h  →  (inv f) ∘ g = h  (inv at unary level, tighter than compose)
    auto r = parse_str("axiom a : inv f compose g = h");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* comp = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(comp, nullptr);
    EXPECT_EQ(comp->op, BinOp::Compose);
    // lhs of compose is inv(f)
    const auto* inv_call = std::get_if<ExprCall>(&comp->lhs->node);
    ASSERT_NE(inv_call, nullptr);
    EXPECT_EQ(inv_call->name, "inv");
    // rhs of compose is g
    EXPECT_NE(std::get_if<ExprVar>(&comp->rhs->node), nullptr);
}

// ── Item 14: Set terms ─────────────────────────────────────────────────────────

TEST(ParserTest, SetMembershipKeyword) {
    // x in S  →  PropRel{x, S, RelOp::In}
    auto r = parse_str("axiom a : x in S");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::In);
    EXPECT_NE(std::get_if<ExprVar>(&rel->lhs->node), nullptr);
    EXPECT_NE(std::get_if<ExprVar>(&rel->rhs->node), nullptr);
}

TEST(ParserTest, SetMembershipUnicode) {
    // x ∈ S  — identical AST to keyword form
    auto r1 = parse_str("axiom a : x in S");
    auto r2 = parse_str("axiom a : x \xe2\x88\x88 S"); // ∈ U+2208
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, SetNonMembershipKeyword) {
    // x not in S  →  PropRel{x, S, RelOp::NotIn}
    auto r = parse_str("axiom a : x not in S");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::NotIn);
}

TEST(ParserTest, SetNonMembershipUnicode) {
    // x ∉ S  — identical AST to "x not in S"
    auto r1 = parse_str("axiom a : x not in S");
    auto r2 = parse_str("axiom a : x \xe2\x88\x89 S"); // ∉ U+2209
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, SubsetEqKeyword) {
    // A subseteq B  →  PropRel{A, B, RelOp::SubsetEq}
    auto r = parse_str("axiom a : A subseteq B");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::SubsetEq);
}

TEST(ParserTest, SubsetEqUnicode) {
    // A ⊆ B  — identical AST to "A subseteq B"
    auto r1 = parse_str("axiom a : A subseteq B");
    auto r2 = parse_str("axiom a : A \xe2\x8a\x86 B"); // ⊆ U+2286
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, StrictSubsetKeyword) {
    // A subset B  →  PropRel{A, B, RelOp::Subset}
    auto r = parse_str("axiom a : A subset B");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::Subset);
}

TEST(ParserTest, SupersetEqKeyword) {
    // A supseteq B  →  PropRel{A, B, RelOp::SupersetEq}
    auto r = parse_str("axiom a : A supseteq B");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::SupersetEq);
}

TEST(ParserTest, SetLiteralEmpty) {
    // {} as lhs of relational prop — empty ExprSetLit
    auto r = parse_str("axiom a : {} = empty");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* sl = std::get_if<ExprSetLit>(&rel->lhs->node);
    ASSERT_NE(sl, nullptr);
    EXPECT_TRUE(sl->elements.empty());
}

TEST(ParserTest, SetLiteralThreeElements) {
    // {1, 2, 3} — set literal with three numeric elements
    auto r = parse_str("axiom a : {1, 2, 3} = S");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* sl = std::get_if<ExprSetLit>(&rel->lhs->node);
    ASSERT_NE(sl, nullptr);
    ASSERT_EQ(sl->elements.size(), 3u);
    for (const auto& e : sl->elements)
        EXPECT_NE(std::get_if<ExprLit>(&e->node), nullptr);
}

TEST(ParserTest, SetComprehensionWithType) {
    // {x : Nat | x > 0}  — set comprehension with type annotation
    auto r = parse_str("axiom a : {x : Nat | x > 0} = S");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* sc = std::get_if<ExprSetCompr>(&rel->lhs->node);
    ASSERT_NE(sc, nullptr);
    EXPECT_EQ(sc->var, "x");
    ASSERT_TRUE(sc->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*sc->type), "Nat");
    // predicate is x > 0
    const auto* pred = std::get_if<PropRel>(&sc->pred->node);
    ASSERT_NE(pred, nullptr);
    EXPECT_EQ(pred->op, RelOp::Gt);
}

TEST(ParserTest, SetComprehensionWithoutType) {
    // {x | P}  — set comprehension without type, predicate is Atomic{P}
    auto r = parse_str("axiom a : {x | P} = S");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* sc = std::get_if<ExprSetCompr>(&rel->lhs->node);
    ASSERT_NE(sc, nullptr);
    EXPECT_EQ(sc->var, "x");
    EXPECT_FALSE(sc->type.has_value());
    EXPECT_NE(std::get_if<Atomic>(&sc->pred->node), nullptr);
}

TEST(ParserTest, SetUnionKeyword) {
    // A union B  →  ExprBinary{Union, A, B}
    auto r = parse_str("axiom a : A union B = C");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* un = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(un, nullptr);
    EXPECT_EQ(un->op, BinOp::Union);
    EXPECT_NE(std::get_if<ExprVar>(&un->lhs->node), nullptr);
    EXPECT_NE(std::get_if<ExprVar>(&un->rhs->node), nullptr);
}

TEST(ParserTest, SetUnionUnicode) {
    // A ∪ B  — identical AST to keyword form
    auto r1 = parse_str("axiom a : A union B = C");
    auto r2 = parse_str("axiom a : A \xe2\x88\xaa B = C"); // ∪ U+222A
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, SetIntersectionKeyword) {
    // A inter B  →  ExprBinary{Inter, A, B}
    auto r = parse_str("axiom a : A inter B = C");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* it = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(it, nullptr);
    EXPECT_EQ(it->op, BinOp::Inter);
}

TEST(ParserTest, SetIntersectionUnicode) {
    // A ∩ B  — identical AST to keyword form
    auto r1 = parse_str("axiom a : A inter B = C");
    auto r2 = parse_str("axiom a : A \xe2\x88\xa9 B = C"); // ∩ U+2229
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, SetDifferenceKeyword) {
    // A setminus B  →  ExprBinary{SetMinus, A, B}
    auto r = parse_str("axiom a : A setminus B = C");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* sm = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(sm, nullptr);
    EXPECT_EQ(sm->op, BinOp::SetMinus);
}

TEST(ParserTest, SetDifferenceBackslash) {
    // A \ B  — identical AST to "A setminus B"
    auto r1 = parse_str("axiom a : A setminus B = C");
    auto r2 = parse_str("axiom a : A \\ B = C");
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    EXPECT_EQ(r1.mod.decls[0]->statement, r2.mod.decls[0]->statement);
}

TEST(ParserTest, SetComplementKeyword) {
    // compl A  →  ExprCall{"compl", [A]}
    auto r = parse_str("axiom a : compl A = B");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* call = std::get_if<ExprCall>(&rel->lhs->node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "compl");
    ASSERT_EQ(call->args.size(), 1u);
    EXPECT_NE(std::get_if<ExprVar>(&call->args[0]->node), nullptr);
}

TEST(ParserTest, SetInterBindsTighterThanUnion) {
    // A inter B union C  =  (A ∩ B) ∪ C  (inter is mul-level, union is add-level)
    auto r = parse_str("axiom a : A inter B union C = D");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* un = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(un, nullptr);
    EXPECT_EQ(un->op, BinOp::Union);
    // lhs of union is the intersection
    const auto* it = std::get_if<ExprBinary>(&un->lhs->node);
    ASSERT_NE(it, nullptr);
    EXPECT_EQ(it->op, BinOp::Inter);
    // rhs of union is C
    EXPECT_NE(std::get_if<ExprVar>(&un->rhs->node), nullptr);
}

TEST(ParserTest, SetMembershipInConjunction) {
    // x in S and y in T  —  membership inside conjunction
    auto r = parse_str("axiom a : x in S and y in T");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* conj = std::get_if<PropAnd>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(conj, nullptr);
    EXPECT_EQ(std::get_if<PropRel>(&conj->lhs->node)->op, RelOp::In);
    EXPECT_EQ(std::get_if<PropRel>(&conj->rhs->node)->op, RelOp::In);
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

// ── Error recovery: declaration-level sync ─────────────────────────────────────

TEST(ParserTest, ErrorRecovery_StrayTokenThenValidDecl) {
    // One stray token before a valid axiom: exactly one error; axiom still parsed.
    auto r = parse_str("garbage\naxiom p : P");
    EXPECT_TRUE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->name, "p");
}

TEST(ParserTest, ErrorRecovery_MultipleStrayTokensThenValidDecl) {
    // Several stray tokens before a valid axiom: one error (sync skips them all).
    auto r = parse_str("foo bar baz\naxiom p : P");
    EXPECT_TRUE(r.diag.hasErrors());
    EXPECT_EQ(r.diag.diagnostics().size(), 1u);
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->name, "p");
}

TEST(ParserTest, ErrorRecovery_BrokenAxiomNameThenValidDecl) {
    // "axiom" keyword but no identifier name, followed by a valid axiom.
    auto r = parse_str("axiom : P\naxiom q : Q");
    EXPECT_TRUE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->name, "q");
}

TEST(ParserTest, ErrorRecovery_TwoBadDeclsThenGood) {
    // Two bad declarations then a good theorem: the good one is always parsed.
    auto r = parse_str("garbage1\ngarbage2\naxiom z : Z");
    EXPECT_TRUE(r.diag.hasErrors());
    ASSERT_GE(r.mod.decls.size(), 1u);
    EXPECT_EQ(r.mod.decls.back()->name, "z");
}

// ── Source ranges (end_loc) ────────────────────────────────────────────────────

TEST(ParserTest, EndLocSetOnStatement) {
    // Every parsed Prop should have end_loc set (not nullopt).
    auto r = parse_str("axiom a : P");
    ASSERT_FALSE(r.diag.hasErrors());
    EXPECT_TRUE(r.mod.decls[0]->statement.end_loc.has_value());
}

TEST(ParserTest, EndLocSetOnRelProp) {
    // PropRel statement has end_loc set and it is after loc.
    auto r = parse_str("axiom a : n > 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto& stmt = r.mod.decls[0]->statement;
    ASSERT_TRUE(stmt.end_loc.has_value());
    // end_loc is at or after loc (same line, later column, or later line)
    EXPECT_TRUE(stmt.end_loc->line > stmt.loc.line
                || stmt.end_loc->col  > stmt.loc.col);
}

TEST(ParserTest, EndLocAtNextDeclStart) {
    // In a two-declaration file the first statement's end_loc lands at the start
    // of the second declaration (the token right after the first proposition).
    auto r = parse_str("axiom a : n > 0\naxiom b : Q");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 2u);
    const auto& stmt_a = r.mod.decls[0]->statement;
    const auto& decl_b = *r.mod.decls[1];
    ASSERT_TRUE(stmt_a.end_loc.has_value());
    // end_loc of first statement should equal loc of second declaration's keyword
    // (the 'axiom' token starts at line 2, col 1)
    EXPECT_EQ(stmt_a.end_loc->line, decl_b.loc.line);
    EXPECT_EQ(stmt_a.end_loc->col,  decl_b.loc.col);
}

TEST(ParserTest, EndLocOnInnerExpr) {
    // The lhs expression of a PropRel has its own end_loc pointing at the
    // relational operator — confirming inner expressions also carry ranges.
    // Source: "axiom a : n + 1 > 0"
    //         col:  1...... 11  15  17 19
    auto r = parse_str("axiom a : n + 1 > 0");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto& stmt = r.mod.decls[0]->statement;
    const auto* rel = std::get_if<PropRel>(&stmt.node);
    ASSERT_NE(rel, nullptr);
    ASSERT_TRUE(rel->lhs->end_loc.has_value()); // lhs is "n + 1"
    // end_loc of "n + 1" must be after its start loc
    EXPECT_TRUE(rel->lhs->end_loc->line > rel->lhs->loc.line
                || rel->lhs->end_loc->col  > rel->lhs->loc.col);
}

TEST(ParserTest, EndLocOnQuantifier) {
    // Quantifier proposition has end_loc set.
    auto r = parse_str("axiom a : for all x, P(x)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto& stmt = r.mod.decls[0]->statement;
    EXPECT_TRUE(stmt.end_loc.has_value());
    // end_loc at or after loc
    EXPECT_TRUE(stmt.end_loc->line > stmt.loc.line
                || stmt.end_loc->col  > stmt.loc.col);
}

// ── Quantifier witness syntax: "by h at t" ─────────────────────────────────────

TEST(ParserTest, HaveStepWithWitness) {
    // "have q : P(n) by forall_h at n" — HaveStep with witness ExprVar{n}
    auto r = parse_str(R"(
theorem t : P(n)
proof
  suppose forall_h : for all x, P(x)
  have q : P(n) by forall_h at n
  then P(n) by q
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* h = get_step<HaveStep>(*r.mod.decls[0]->proof, 1);
    ASSERT_NE(h, nullptr);
    EXPECT_EQ(h->name, "q");
    ASSERT_EQ(h->justification.size(), 1u);
    EXPECT_EQ(h->justification[0], "forall_h");
    ASSERT_TRUE(h->witness.has_value());
    const auto* var = std::get_if<ExprVar>(&(*h->witness)->node);
    ASSERT_NE(var, nullptr);
    EXPECT_EQ(var->name, "n");
}

TEST(ParserTest, HaveStepWithoutWitnessNoChange) {
    // A regular "have" step without "at" still has witness == nullopt.
    auto r = parse_str(R"(
theorem t : P and Q
proof
  suppose hp : P
  suppose hq : Q
  have hpq : P and Q by hp and hq
  then P and Q by hpq
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* h = get_step<HaveStep>(*r.mod.decls[0]->proof, 2);
    ASSERT_NE(h, nullptr);
    EXPECT_FALSE(h->witness.has_value());
}

TEST(ParserTest, ThenStepWithWitness) {
    // "then there exists x, P(x) by fact at n" — ThenStep with witness ExprVar{n}
    auto r = parse_str(R"(
theorem t : there exists x, P(x)
proof
  suppose fact : P(n)
  then there exists x, P(x) by fact at n
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ts = get_step<ThenStep>(*r.mod.decls[0]->proof, 1);
    ASSERT_NE(ts, nullptr);
    ASSERT_EQ(ts->justification.size(), 1u);
    EXPECT_EQ(ts->justification[0], "fact");
    ASSERT_TRUE(ts->witness.has_value());
    const auto* var = std::get_if<ExprVar>(&(*ts->witness)->node);
    ASSERT_NE(var, nullptr);
    EXPECT_EQ(var->name, "n");
}

TEST(ParserTest, WitnessExprIsArithmetic) {
    // "by h at n + 1" — witness is a full expression, not just a variable
    auto r = parse_str(R"(
theorem t : P(n + 1)
proof
  suppose forall_h : for all x, P(x)
  have q : P(n + 1) by forall_h at n + 1
  then P(n + 1) by q
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* h = get_step<HaveStep>(*r.mod.decls[0]->proof, 1);
    ASSERT_NE(h, nullptr);
    ASSERT_TRUE(h->witness.has_value());
    const auto* add = std::get_if<ExprBinary>(&(*h->witness)->node);
    ASSERT_NE(add, nullptr);
    EXPECT_EQ(add->op, BinOp::Add);
}

// ── Cases step: "done" arm terminator ─────────────────────────────────────────

TEST(ParserTest, CasesWithDoneAllowsFollowingStep) {
    // "done" terminates each arm; the trailing "then" is NOT consumed by the last arm.
    auto r = parse_str(R"(
theorem t : S
proof
  suppose h : P or Q
  cases result : h
    case hp : P => then R by pr and hp done
    case hq : Q => then R by qr and hq done
  then S by result
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    // 3 steps: suppose, cases, then
    ASSERT_EQ(r.mod.decls[0]->proof->steps.size(), 3u);
    EXPECT_NE(std::get_if<SupposeStep>(&r.mod.decls[0]->proof->steps[0].node), nullptr);
    EXPECT_NE(std::get_if<CasesStep> (&r.mod.decls[0]->proof->steps[1].node), nullptr);
    EXPECT_NE(std::get_if<ThenStep>  (&r.mod.decls[0]->proof->steps[2].node), nullptr);
}

TEST(ParserTest, CasesWithDoneMultiStepArms) {
    // Arms with multiple steps work with "done": each arm has have+then before done.
    auto r = parse_str(R"(
theorem t : S
proof
  suppose h : P or Q
  cases result : h
    case hp : P =>
      have hr : R by pr and hp
      then R by hr
    done
    case hq : Q =>
      then R by qr and hq
    done
  then S by result
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls[0]->proof->steps.size(), 3u);
    const auto* cs = std::get_if<CasesStep>(&r.mod.decls[0]->proof->steps[1].node);
    ASSERT_NE(cs, nullptr);
    EXPECT_EQ(cs->arms.size(), 2u);
    EXPECT_EQ(cs->arms[0].steps.size(), 2u); // have + then
    EXPECT_EQ(cs->arms[1].steps.size(), 1u); // then only
}

TEST(ParserTest, CasesWithoutDoneBackwardCompat) {
    // Without "done", existing behavior is preserved: arms stop at "case"/"end".
    auto r = parse_str(R"(
theorem t : R
proof
  suppose h : P or Q
  cases result : h
    case hp : P => then R by pr and hp
    case hq : Q => then R by qr and hq
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    // 2 steps: suppose, cases (no trailing then — arms consumed everything up to end)
    ASSERT_EQ(r.mod.decls[0]->proof->steps.size(), 2u);
}

// ── TakeStep (∀-intro variable introduction) ──────────────────────────────────

TEST(ParserTest, TakeStep_NoType) {
    auto r = parse_str(R"(
theorem t : P
proof
  take x
  then P by ax
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<TakeStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    EXPECT_EQ(s->var, "x");
    EXPECT_FALSE(s->type.has_value());
}

TEST(ParserTest, TakeStep_WithType) {
    auto r = parse_str(R"(
theorem t : P
proof
  take n : Nat
  then P by ax
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<TakeStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s, nullptr);
    EXPECT_EQ(s->var, "n");
    ASSERT_TRUE(s->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*s->type), "Nat");
}

TEST(ParserTest, TakeStep_InFullForallProof) {
    // take + have + then ∀ — parse succeeds and produces 3 steps
    auto r = parse_str(R"(
theorem all_p : for all n : Nat, P(n)
proof
  take n : Nat
  have h : P(n) by ax
  then for all n : Nat, P(n) by h
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls[0]->proof->steps.size(), 3u);
    EXPECT_NE(std::get_if<TakeStep>  (&r.mod.decls[0]->proof->steps[0].node), nullptr);
    EXPECT_NE(std::get_if<HaveStep>  (&r.mod.decls[0]->proof->steps[1].node), nullptr);
    EXPECT_NE(std::get_if<ThenStep>  (&r.mod.decls[0]->proof->steps[2].node), nullptr);
    // verify the ThenStep conclusion is a PropForall
    const auto* ts = std::get_if<ThenStep>(&r.mod.decls[0]->proof->steps[2].node);
    ASSERT_NE(ts, nullptr);
    EXPECT_NE(std::get_if<PropForall>(&ts->prop.node), nullptr);
}

// ── ObtainStep (∃-elim) ───────────────────────────────────────────────────────

TEST(ParserTest, ObtainStep_Basic) {
    // Without "done", the arm runs until "end" — obtain is the last step.
    auto r = parse_str(R"(
theorem t : Q
proof
  suppose he : there exists n, P(n)
  obtain result from he
    case n , hn : P(n) =>
      then Q by ax
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    // 2 steps: suppose, obtain (arm runs to end of proof)
    ASSERT_EQ(r.mod.decls[0]->proof->steps.size(), 2u);
    const auto* os = std::get_if<ObtainStep>(&r.mod.decls[0]->proof->steps[1].node);
    ASSERT_NE(os, nullptr);
    EXPECT_EQ(os->name, "result");
    EXPECT_EQ(os->exists_ref, "he");
    EXPECT_EQ(os->var, "n");
    EXPECT_FALSE(os->type.has_value());
    EXPECT_EQ(os->hyp_name, "hn");
    EXPECT_EQ(os->steps.size(), 1u); // just the one then step
}

TEST(ParserTest, ObtainStep_WithType) {
    // Typed variable annotation; arm runs to end.
    auto r = parse_str(R"(
theorem t : Q
proof
  suppose he : there exists n : Nat, P(n)
  obtain result from he
    case n : Nat , hn : P(n) =>
      then Q by ax
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls[0]->proof->steps.size(), 2u);
    const auto* os = std::get_if<ObtainStep>(&r.mod.decls[0]->proof->steps[1].node);
    ASSERT_NE(os, nullptr);
    EXPECT_EQ(os->var, "n");
    ASSERT_TRUE(os->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*os->type), "Nat");
    EXPECT_EQ(os->hyp_name, "hn");
    EXPECT_EQ(os->steps.size(), 1u);
}

TEST(ParserTest, ObtainStep_WithDone) {
    // "done" terminates the arm; subsequent then is NOT consumed by the arm
    auto r = parse_str(R"(
theorem t : Q
proof
  suppose he : there exists n, P(n)
  obtain result from he
    case n , hn : P(n) =>
      then Q by ax
  done
  then Q by result
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    // 3 outer steps: suppose, obtain (with done), then
    ASSERT_EQ(r.mod.decls[0]->proof->steps.size(), 3u);
    EXPECT_NE(std::get_if<ObtainStep>(&r.mod.decls[0]->proof->steps[1].node), nullptr);
    EXPECT_NE(std::get_if<ThenStep>  (&r.mod.decls[0]->proof->steps[2].node), nullptr);
    const auto* os = std::get_if<ObtainStep>(&r.mod.decls[0]->proof->steps[1].node);
    ASSERT_NE(os, nullptr);
    // arm has 1 step (the then); done was consumed
    EXPECT_EQ(os->steps.size(), 1u);
}

// ── Function type annotations (Nat -> Real) ───────────────────────────────────

TEST(ParserTest, FunctionType_InForallBinder) {
    // ∀ f : Nat -> Real, P  — binder with function type annotation
    auto r = parse_str("axiom a : for all f : Nat -> Real, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    ASSERT_TRUE(fa->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*fa->type), "Nat -> Real");
}

TEST(ParserTest, FunctionType_RightAssocInBinder) {
    // ∀ f : Nat -> Real -> Prop, P  — right-associative
    auto r = parse_str("axiom a : for all f : Nat -> Real -> Prop, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    ASSERT_TRUE(fa->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*fa->type), "Nat -> Real -> Prop");
}

TEST(ParserTest, FunctionType_InExistsBinder) {
    // there exists f : Nat -> Real, P  — existential binder with function type
    auto r = parse_str("axiom a : there exists f : Nat -> Real, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ex = std::get_if<PropExists>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(ex, nullptr);
    ASSERT_TRUE(ex->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*ex->type), "Nat -> Real");
}

// ── Definition params stored in AST ──────────────────────────────────────────

TEST(ParserTest, DefinitionParams_OneParam) {
    auto r = parse_str("definition f (x : Nat) : P");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->params.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->params[0].name, "x");
    EXPECT_EQ(forall::pretty::to_string(r.mod.decls[0]->params[0].type), "Nat");
}

TEST(ParserTest, DefinitionParams_TwoParams) {
    auto r = parse_str("definition add (x : Nat) (y : Nat) : P");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls[0]->params.size(), 2u);
    EXPECT_EQ(r.mod.decls[0]->params[0].name, "x");
    EXPECT_EQ(r.mod.decls[0]->params[1].name, "y");
    EXPECT_EQ(forall::pretty::to_string(r.mod.decls[0]->params[0].type), "Nat");
    EXPECT_EQ(forall::pretty::to_string(r.mod.decls[0]->params[1].type), "Nat");
}

TEST(ParserTest, DefinitionParams_FunctionTypeParam) {
    auto r = parse_str("definition apply (f : Nat -> Real) : P");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls[0]->params.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->params[0].name, "f");
    EXPECT_EQ(forall::pretty::to_string(r.mod.decls[0]->params[0].type), "Nat -> Real");
}

TEST(ParserTest, DefinitionParams_NoParams) {
    // definitions with no params still parse correctly; params list empty
    auto r = parse_str("definition c : P");
    ASSERT_FALSE(r.diag.hasErrors());
    EXPECT_EQ(r.mod.decls[0]->params.size(), 0u);
}

TEST(ParserTest, AxiomHasNoParams) {
    // axioms never have params; params list empty
    auto r = parse_str("axiom a : P");
    ASSERT_FALSE(r.diag.hasErrors());
    EXPECT_EQ(r.mod.decls[0]->params.size(), 0u);
}

// ── Set type annotations ──────────────────────────────────────────────────────

TEST(ParserTest, TypeAnnotation_SetNat_InForallBinder) {
    // ∀ S : Set Nat, P  — ForallBinder with TypeSet{Nat}
    auto r = parse_str("axiom a : for all S : Set Nat, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    ASSERT_TRUE(fa->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*fa->type), "Set Nat");
}

TEST(ParserTest, TypeAnnotation_SetReal_InExistsBinder) {
    // ∃ S : Set Real, P  — ExistsBinder with TypeSet{Real}
    auto r = parse_str("axiom a : there exists S : Set Real, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ex = std::get_if<PropExists>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(ex, nullptr);
    ASSERT_TRUE(ex->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*ex->type), "Set Real");
}

TEST(ParserTest, TypeAnnotation_SetNat_AsDefinitionParam) {
    // definition f (S : Set Nat) : P  — param with TypeSet{Nat}
    auto r = parse_str("definition f (S : Set Nat) : P");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls[0]->params.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->params[0].name, "S");
    EXPECT_EQ(forall::pretty::to_string(r.mod.decls[0]->params[0].type), "Set Nat");
}

TEST(ParserTest, TypeAnnotation_NestedSet) {
    // ∀ S : Set Set Nat, P  — nested set type annotation
    auto r = parse_str("axiom a : for all S : Set Set Nat, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    ASSERT_TRUE(fa->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*fa->type), "Set Set Nat");
}

// ── Grouped-expression as PropRel LHS ─────────────────────────────────────────
// Previously "(x + y) + z = ..." failed because '(' was parsed as a proposition
// grouping context; the inner "x + y" had no relational operator and errored.

TEST(ParserTest, GroupedExprLHS_SimpleEquality) {
    // (x + y) = z
    auto r = parse_str("axiom a : (x + y) = z");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::Eq);
    const auto* lhs = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(lhs, nullptr);
    EXPECT_EQ(lhs->op, BinOp::Add);
}

TEST(ParserTest, GroupedExprLHS_AssociativityAxiom) {
    // (x + y) + z = x + (y + z)  — the shape used in real.forall / nat.forall
    auto r = parse_str("axiom assoc : (x + y) + z = x + (y + z)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::Eq);
    // LHS: (x + y) + z  → ExprBinary{Add, ExprBinary{Add, x, y}, z}
    const auto* outer = std::get_if<ExprBinary>(&rel->lhs->node);
    ASSERT_NE(outer, nullptr);
    EXPECT_EQ(outer->op, BinOp::Add);
    const auto* inner = std::get_if<ExprBinary>(&outer->lhs->node);
    ASSERT_NE(inner, nullptr);
    EXPECT_EQ(inner->op, BinOp::Add);
}

TEST(ParserTest, GroupedExprLHS_MulAssoc) {
    // (x * y) * z = x * (y * z)
    auto r = parse_str("axiom assoc : (x * y) * z = x * (y * z)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::Eq);
}

TEST(ParserTest, GroupedExprLHS_InequalityLt) {
    // (a + b) < c
    auto r = parse_str("axiom a : (a + b) < c");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::Lt);
}

TEST(ParserTest, GroupedPropStillWorks) {
    // (P and Q) — should still parse as a conjunction, not error
    auto r = parse_str("axiom a : (P and Q)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* conj = std::get_if<PropAnd>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(conj, nullptr);
}

TEST(ParserTest, GroupedPropInImplication) {
    // (P and Q) implies R — grouped prop as antecedent
    auto r = parse_str("axiom a : (P and Q) implies R");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* impl = std::get_if<PropImpl>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(impl, nullptr);
    const auto* conj = std::get_if<PropAnd>(&impl->lhs->node);
    ASSERT_NE(conj, nullptr);
}

// ── InductionStep parser tests ────────────────────────────────────────────────

TEST(ParserTest, InductionStep_Basic) {
    auto r = parse_str(R"(
theorem t : for all n : Nat, n = n
proof
  induction result on n : n = n
    base:
      then 0 = 0 by ax
    inductive:
      then succ(n) = succ(n) by ih
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls[0]->proof->steps.size(), 1u);
    const auto* ind = get_step<InductionStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(ind, nullptr);
    EXPECT_EQ(ind->name, "result");
    EXPECT_EQ(ind->var, "n");
    // body should be the prop "n = n" (a PropRel)
    EXPECT_NE(std::get_if<PropRel>(&ind->body.node), nullptr);
    EXPECT_EQ(ind->base_steps.size(), 1u);
    EXPECT_EQ(ind->inductive_steps.size(), 1u);
    EXPECT_NE(std::get_if<ThenStep>(&ind->base_steps[0]->node), nullptr);
    EXPECT_NE(std::get_if<ThenStep>(&ind->inductive_steps[0]->node), nullptr);
}

TEST(ParserTest, InductionStep_MultipleStepsPerBlock) {
    auto r = parse_str(R"(
theorem t : for all n : Nat, P
proof
  induction result on n : P
    base:
      suppose h : P
      then P by h
    inductive:
      suppose h : P
      then P by h
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ind = get_step<InductionStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(ind, nullptr);
    EXPECT_EQ(ind->base_steps.size(), 2u);
    EXPECT_EQ(ind->inductive_steps.size(), 2u);
}

TEST(ParserTest, InductionStep_InductionKeywordLexed) {
    // Verify 'induction' is lexed as a keyword; 'base' and 'inductive' as identifiers
    auto r = parse_str(R"(
theorem t : P
proof
  induction result on n : P
    base:
      then P by ax
    inductive:
      then P by ih
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    EXPECT_NE(get_step<InductionStep>(*r.mod.decls[0]->proof, 0), nullptr);
}

TEST(ParserTest, InductionStep_BodyIsForallProp) {
    // body can be a complex proposition — quantified
    auto r = parse_str(R"(
theorem t : for all n : Nat, for all m : Nat, n = m implies m = n
proof
  induction result on n : for all m : Nat, n = m implies m = n
    base:
      then for all m : Nat, 0 = m implies m = 0 by ax
    inductive:
      then for all m : Nat, succ(n) = m implies m = succ(n) by ih
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ind = get_step<InductionStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(ind, nullptr);
    EXPECT_NE(std::get_if<PropForall>(&ind->body.node), nullptr);
}

// ── Instance declarations ──────────────────────────────────────────────────────

TEST(ParserTest, InstanceDecl_Basic) {
    // instance Real : Field  — parses to DeclKind::Instance
    auto r = parse_str("instance Real : Field");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, DeclKind::Instance);
    EXPECT_EQ(d.name, "Real");
    EXPECT_EQ(d.instance_class, "Field");
}

TEST(ParserTest, InstanceDecl_MultipleWithAxioms) {
    // axiom then instance — both are parsed as separate declarations
    auto r = parse_str("axiom T_add_comm : P\ninstance T : Ring");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 2u);
    EXPECT_EQ(r.mod.decls[0]->kind, DeclKind::Axiom);
    EXPECT_EQ(r.mod.decls[1]->kind, DeclKind::Instance);
    EXPECT_EQ(r.mod.decls[1]->name, "T");
    EXPECT_EQ(r.mod.decls[1]->instance_class, "Ring");
}

TEST(ParserTest, InstanceDecl_MissingColon) {
    // instance Real Field  — missing ':' is a parse error
    auto r = parse_str("instance Real Field");
    EXPECT_TRUE(r.diag.hasErrors());
}

TEST(ParserTest, InstanceDecl_MissingClassName) {
    // instance Real :  — missing class name is a parse error
    auto r = parse_str("instance Real :");
    EXPECT_TRUE(r.diag.hasErrors());
}

TEST(ParserTest, InstanceDecl_MissingTypeName) {
    // instance : Ring  — missing type name is a parse error
    auto r = parse_str("instance : Ring");
    EXPECT_TRUE(r.diag.hasErrors());
}

// ── contradiction from / suppose for contradiction that ─────────────

TEST(ParserTest, ContradictionFrom) {
    // "contradiction from nh and h" — "from" is an alias for ":"
    auto r = parse_str(R"(theorem t : false
proof
  suppose h : P
  suppose nh : not P
  contradiction from nh and h
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto& steps = r.mod.decls[0]->proof->steps;
    ASSERT_EQ(steps.size(), 3u);
    const auto* cs = std::get_if<ContradictionStep>(&steps[2].node);
    ASSERT_NE(cs, nullptr);
    EXPECT_EQ(cs->justification.size(), 2u);
    EXPECT_EQ(cs->justification[0], "nh");
    EXPECT_EQ(cs->justification[1], "h");
}

TEST(ParserTest, SupposeForContradictionThat) {
    // "suppose for contradiction that P" — "that" replaces ":"
    auto r = parse_str(R"(theorem t : false
proof
  suppose for contradiction that P
  have bot : false by ax and h
  then false by bot
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ss = get_step<SupposeStep>(r.mod.decls[0]->proof.value(), 0);
    ASSERT_NE(ss, nullptr);
    EXPECT_TRUE(ss->for_contradiction);
}

// ── "from" as alias for "by" in have steps ───────────────────────────────

TEST(ParserTest, HaveStepFrom) {
    // "have h : P from ax" — "from" is an alias for "by"
    auto r = parse_str(R"(axiom ax : P
theorem t : P
proof
  have h : P from ax
  then P by h
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* hs = get_step<HaveStep>(r.mod.decls[1]->proof.value(), 0);
    ASSERT_NE(hs, nullptr);
    EXPECT_EQ(hs->justification.size(), 1u);
    EXPECT_EQ(hs->justification[0], "ax");
}

TEST(ParserTest, MultiVarBinder_TwoVarsSpaceSep) {
    // "for all x y : Nat, P" must parse as PropForall{x, PropForall{y, P}}
    auto r = parse_str("axiom a : for all x y : Nat, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* outer = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(outer, nullptr);
    EXPECT_EQ(outer->var, "x");
    const auto* inner = std::get_if<ast::PropForall>(&outer->body->node);
    ASSERT_NE(inner, nullptr);
    EXPECT_EQ(inner->var, "y");
    const auto* atom = std::get_if<ast::Atomic>(&inner->body->node);
    ASSERT_NE(atom, nullptr);
    EXPECT_EQ(atom->name, "P");
}

TEST(ParserTest, MultiVarBinder_ThreeVarsNoType) {
    // "for all x y z, P" nests three foralls
    auto r = parse_str("axiom a : for all x y z, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* f1 = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(f1, nullptr); EXPECT_EQ(f1->var, "x");
    const auto* f2 = std::get_if<ast::PropForall>(&f1->body->node);
    ASSERT_NE(f2, nullptr); EXPECT_EQ(f2->var, "y");
    const auto* f3 = std::get_if<ast::PropForall>(&f2->body->node);
    ASSERT_NE(f3, nullptr); EXPECT_EQ(f3->var, "z");
}

TEST(ParserTest, MultiVarBinder_AndSeparated) {
    // "for all x and y : Nat, P" — "and" as separator
    auto r = parse_str("axiom a : for all x and y : Nat, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* outer = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(outer, nullptr);
    EXPECT_EQ(outer->var, "x");
    const auto* inner = std::get_if<ast::PropForall>(&outer->body->node);
    ASSERT_NE(inner, nullptr);
    EXPECT_EQ(inner->var, "y");
}

TEST(ParserTest, MultiVarBinder_ExistsTwo) {
    // "there exists x y : Nat, P" — ∃ also supports multi-var
    auto r = parse_str("axiom a : there exists x y : Nat, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* outer = std::get_if<ast::PropExists>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(outer, nullptr); EXPECT_EQ(outer->var, "x");
    const auto* inner = std::get_if<ast::PropExists>(&outer->body->node);
    ASSERT_NE(inner, nullptr); EXPECT_EQ(inner->var, "y");
}

TEST(ParserTest, MultiVarBinder_SingleVarStillWorks) {
    // single-variable form unchanged
    auto r = parse_str("axiom a : for all x : Nat, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* f = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(f, nullptr); EXPECT_EQ(f->var, "x");
    const auto* body = std::get_if<ast::Atomic>(&f->body->node);
    ASSERT_NE(body, nullptr); EXPECT_EQ(body->name, "P");
}

TEST(ParserTest, BoundedBinder_ForallLt) {
    // "for all i < n, P(i)" desugars to "∀ i : Nat, i < n → P(i)"
    auto r = parse_str("axiom a : for all i < n, P(i)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    EXPECT_EQ(fa->var, "i");
    ASSERT_TRUE(fa->type.has_value());
    EXPECT_TRUE(std::holds_alternative<ast::TypeNat>(fa->type->node));
    // body is (i < n) → P(i)
    const auto* impl = std::get_if<ast::PropImpl>(&fa->body->node);
    ASSERT_NE(impl, nullptr);
    const auto* guard = std::get_if<ast::PropRel>(&impl->lhs->node);
    ASSERT_NE(guard, nullptr);
    EXPECT_EQ(guard->op, ast::RelOp::Lt);
}

TEST(ParserTest, BoundedBinder_ForallGt) {
    // "for all i > 0, P(i)" desugars to "∀ i : Nat, i > 0 → P(i)"
    auto r = parse_str("axiom a : for all i > 0, P(i)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr); EXPECT_EQ(fa->var, "i");
    const auto* impl = std::get_if<ast::PropImpl>(&fa->body->node);
    ASSERT_NE(impl, nullptr);
    const auto* guard = std::get_if<ast::PropRel>(&impl->lhs->node);
    ASSERT_NE(guard, nullptr);
    EXPECT_EQ(guard->op, ast::RelOp::Gt);
}

TEST(ParserTest, BoundedBinder_ExistsLeq) {
    // "there exists i <= n, P(i)"
    auto r = parse_str("axiom a : there exists i <= n, P(i)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ex = std::get_if<ast::PropExists>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(ex, nullptr); EXPECT_EQ(ex->var, "i");
    const auto* impl = std::get_if<ast::PropImpl>(&ex->body->node);
    ASSERT_NE(impl, nullptr);
    const auto* guard = std::get_if<ast::PropRel>(&impl->lhs->node);
    ASSERT_NE(guard, nullptr);
    EXPECT_EQ(guard->op, ast::RelOp::LtEq);
}

TEST(ParserTest, TupleType_Pair_InForallBinder) {
    // "for all p : (Nat, Nat), P" uses TypeTuple
    auto r = parse_str("axiom a : for all p : (Nat, Nat), P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    ASSERT_TRUE(fa->type.has_value());
    const auto* tt = std::get_if<ast::TypeTuple>(&fa->type->node);
    ASSERT_NE(tt, nullptr);
    ASSERT_EQ(tt->elements.size(), 2u);
    EXPECT_TRUE(std::holds_alternative<ast::TypeNat>(tt->elements[0]->node));
    EXPECT_TRUE(std::holds_alternative<ast::TypeNat>(tt->elements[1]->node));
}

TEST(ParserTest, TupleType_Triple) {
    // three-element tuple type in a binder
    auto r = parse_str("axiom a : for all t : (Nat, Int, Real), P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    const auto* tt = std::get_if<ast::TypeTuple>(&fa->type.value().node);
    ASSERT_NE(tt, nullptr);
    ASSERT_EQ(tt->elements.size(), 3u);
    EXPECT_TRUE(std::holds_alternative<ast::TypeNat>(tt->elements[0]->node));
    EXPECT_TRUE(std::holds_alternative<ast::TypeInt>(tt->elements[1]->node));
    EXPECT_TRUE(std::holds_alternative<ast::TypeReal>(tt->elements[2]->node));
}

TEST(ParserTest, TupleType_SingleParenIsNotTuple) {
    // "(Nat)" should reduce to just Nat (not TypeTuple{Nat})
    auto r = parse_str("axiom a : for all x : (Nat), P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    ASSERT_TRUE(fa->type.has_value());
    EXPECT_TRUE(std::holds_alternative<ast::TypeNat>(fa->type->node));
}

TEST(ParserTest, TruePropKeyword) {
    // "true" parses as PropTrue{}
    auto r = parse_str("axiom a : true");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* pt = std::get_if<ast::PropTrue>(&r.mod.decls[0]->statement.node);
    EXPECT_NE(pt, nullptr);
}

TEST(ParserTest, TruePropUnicode) {
    // ⊤ (E2 88 A4) parses as PropTrue{}
    auto r = parse_str("axiom a : \xe2\x88\xa4");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* pt = std::get_if<ast::PropTrue>(&r.mod.decls[0]->statement.node);
    EXPECT_NE(pt, nullptr);
}

TEST(ParserTest, DoubleNegation_Axiom) {
    // "not (not P)" must parse as PropNot{PropNot{Atomic{"P"}}}, not an error
    auto r = parse_str("axiom dne : not (not P) -> P");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    // statement should be (¬¬P) → P
    const auto* impl = std::get_if<ast::PropImpl>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(impl, nullptr);
    const auto* outer_not = std::get_if<ast::PropNot>(&impl->lhs->node);
    ASSERT_NE(outer_not, nullptr);
    const auto* inner_not = std::get_if<ast::PropNot>(&outer_not->inner->node);
    ASSERT_NE(inner_not, nullptr);
    const auto* atom = std::get_if<ast::Atomic>(&inner_not->inner->node);
    ASSERT_NE(atom, nullptr);
    EXPECT_EQ(atom->name, "P");
}

TEST(ParserTest, DoubleNegation_Parenthesized) {
    // axiom about "¬(¬P)" using Unicode symbols
    auto r = parse_str("axiom dne2 : ¬(¬P)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* outer_not = std::get_if<ast::PropNot>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(outer_not, nullptr);
    const auto* inner_not = std::get_if<ast::PropNot>(&outer_not->inner->node);
    ASSERT_NE(inner_not, nullptr);
}

TEST(ParserTest, ShowStep_Basic) {
    // "show P" parses as ShowStep
    auto r = parse_str(R"(
axiom ax : P
theorem t : P
proof
  show P
  then P by ax
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ss = get_step<ast::ShowStep>(*r.mod.decls[1]->proof, 0);
    ASSERT_NE(ss, nullptr);
    const auto* atom = std::get_if<ast::Atomic>(&ss->prop.node);
    ASSERT_NE(atom, nullptr);
    EXPECT_EQ(atom->name, "P");
}

TEST(ParserTest, ExactStep_Basic) {
    // "exact ax" parses as ExactStep with hyp_ref = "ax"
    auto r = parse_str(R"(
axiom ax : P
theorem t : P
proof
  exact ax
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* es = get_step<ast::ExactStep>(*r.mod.decls[1]->proof, 0);
    ASSERT_NE(es, nullptr);
    EXPECT_EQ(es->hyp_ref, "ax");
}

TEST(ParserTest, RewriteStep_Forward) {
    // "rewrite h" parses as a single-item RewriteStep with reverse=false
    auto r = parse_str(R"(
axiom eq : x = y
theorem t : P(x)
proof
  rewrite eq
  then P(y)
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rw = get_step<ast::RewriteStep>(*r.mod.decls[1]->proof, 0);
    ASSERT_NE(rw, nullptr);
    ASSERT_EQ(rw->rewrites.size(), 1u);
    EXPECT_EQ(rw->rewrites[0].hyp_ref, "eq");
    EXPECT_FALSE(rw->rewrites[0].reverse);
}

TEST(ParserTest, RewriteStep_List) {
    // "rewrite h1, ← h2, h3" parses as a three-item RewriteStep.
    auto r = parse_str("axiom eq1 : a = b\n"
                       "axiom eq2 : c = d\n"
                       "axiom eq3 : e = f\n"
                       "theorem t : P\n"
                       "proof\n"
                       "  rewrite eq1, \xe2\x86\x90 eq2, eq3\n"
                       "  then P\n"
                       "end");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rw = get_step<ast::RewriteStep>(*r.mod.decls[3]->proof, 0);
    ASSERT_NE(rw, nullptr);
    ASSERT_EQ(rw->rewrites.size(), 3u);
    EXPECT_EQ(rw->rewrites[0].hyp_ref, "eq1");  EXPECT_FALSE(rw->rewrites[0].reverse);
    EXPECT_EQ(rw->rewrites[1].hyp_ref, "eq2");  EXPECT_TRUE(rw->rewrites[1].reverse);
    EXPECT_EQ(rw->rewrites[2].hyp_ref, "eq3");  EXPECT_FALSE(rw->rewrites[2].reverse);
}

// ── Structure declarations ─────────────────────────────────────────────────────

TEST(ParserTest, StructureBasic) {
    auto r = parse_str(R"(
structure Point :=
  x : Real
  y : Real
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, DeclKind::Structure);
    EXPECT_EQ(d.name, "Point");
    ASSERT_EQ(d.fields.size(), 2u);
    // Both fields should be FieldTerm
    const auto* f0 = std::get_if<ast::FieldTerm>(&d.fields[0]);
    ASSERT_NE(f0, nullptr);
    EXPECT_EQ(f0->name, "x");
    EXPECT_EQ(f0->type, ast::type_real());
    const auto* f1 = std::get_if<ast::FieldTerm>(&d.fields[1]);
    ASSERT_NE(f1, nullptr);
    EXPECT_EQ(f1->name, "y");
    EXPECT_EQ(f1->type, ast::type_real());
}

TEST(ParserTest, StructureWithAxioms) {
    // Group-like structure: 4 term fields + 4 axiom fields
    auto r = parse_str(R"(
structure Group :=
  carrier : Type
  mul : carrier -> carrier -> carrier
  one : carrier
  inv : carrier -> carrier
  axiom mul_assoc : for all a b c : carrier, mul(mul(a, b), c) = mul(a, mul(b, c))
  axiom one_mul : for all a : carrier, mul(one, a) = a
  axiom mul_one : for all a : carrier, mul(a, one) = a
  axiom mul_inv : for all a : carrier, mul(inv(a), a) = one
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, DeclKind::Structure);
    EXPECT_EQ(d.name, "Group");
    ASSERT_EQ(d.fields.size(), 8u);
    // First 4 are FieldTerm
    EXPECT_NE(std::get_if<ast::FieldTerm>(&d.fields[0]), nullptr);
    EXPECT_NE(std::get_if<ast::FieldTerm>(&d.fields[1]), nullptr);
    EXPECT_NE(std::get_if<ast::FieldTerm>(&d.fields[2]), nullptr);
    EXPECT_NE(std::get_if<ast::FieldTerm>(&d.fields[3]), nullptr);
    // Last 4 are FieldAxiom
    const auto* a0 = std::get_if<ast::FieldAxiom>(&d.fields[4]);
    ASSERT_NE(a0, nullptr);
    EXPECT_EQ(a0->name, "mul_assoc");
    const auto* a1 = std::get_if<ast::FieldAxiom>(&d.fields[5]);
    ASSERT_NE(a1, nullptr);
    EXPECT_EQ(a1->name, "one_mul");
    const auto* a2 = std::get_if<ast::FieldAxiom>(&d.fields[6]);
    ASSERT_NE(a2, nullptr);
    EXPECT_EQ(a2->name, "mul_one");
    const auto* a3 = std::get_if<ast::FieldAxiom>(&d.fields[7]);
    ASSERT_NE(a3, nullptr);
    EXPECT_EQ(a3->name, "mul_inv");
}

TEST(ParserTest, StructureMalformed) {
    // Missing name — should emit a parse error
    auto r = parse_str("structure :=");
    EXPECT_TRUE(r.diag.hasErrors());
}

// ── Field projection (ExprField) ─────────────────────────────────────────

TEST(ParserTest, FieldProjectionBasic) {
    // g.mul should parse to ExprField{ExprVar{"g"}, "mul"}
    auto r = parse_str("axiom a : g.mul = g.mul");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* field = std::get_if<ExprField>(&rel->lhs->node);
    ASSERT_NE(field, nullptr);
    EXPECT_EQ(field->field_name, "mul");
    const auto* base_var = std::get_if<ExprVar>(&field->base->node);
    ASSERT_NE(base_var, nullptr);
    EXPECT_EQ(base_var->name, "g");
}

TEST(ParserTest, FieldProjectionChained) {
    // g.mul.name should parse as ExprField{ExprField{ExprVar{"g"}, "mul"}, "name"}
    auto r = parse_str("axiom a : g.mul.name = g.mul.name");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    const auto* outer = std::get_if<ExprField>(&rel->lhs->node);
    ASSERT_NE(outer, nullptr);
    EXPECT_EQ(outer->field_name, "name");
    const auto* inner = std::get_if<ExprField>(&outer->base->node);
    ASSERT_NE(inner, nullptr);
    EXPECT_EQ(inner->field_name, "mul");
    const auto* base_var = std::get_if<ExprVar>(&inner->base->node);
    ASSERT_NE(base_var, nullptr);
    EXPECT_EQ(base_var->name, "g");
}

TEST(ParserTest, FieldProjectionInProp) {
    // g.one = g.one parses as PropRel{ExprField{...}, ExprField{...}, Eq}
    auto r = parse_str("axiom a : g.one = g.one");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* rel = std::get_if<PropRel>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(rel, nullptr);
    EXPECT_EQ(rel->op, RelOp::Eq);
    EXPECT_NE(std::get_if<ExprField>(&rel->lhs->node), nullptr);
    EXPECT_NE(std::get_if<ExprField>(&rel->rhs->node), nullptr);
}

// ── Structure instantiation ──────────────────────────────────────────────

TEST(ParserTest, StructureInstantiation) {
    // definition NatAdd : Monoid :=
    //   carrier := Nat
    //   mul := fun a => a
    //   one := 0
    auto r = parse_str(
        "definition NatAdd : Monoid :=\n"
        "  carrier := 0\n"
        "  one := 1\n"
    );
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, DeclKind::Definition);
    EXPECT_EQ(d.name, "NatAdd");
    EXPECT_EQ(d.struct_type, "Monoid");
    EXPECT_EQ(d.struct_bindings.size(), 2u);
    EXPECT_NE(d.struct_bindings.find("carrier"), d.struct_bindings.end());
    EXPECT_NE(d.struct_bindings.find("one"), d.struct_bindings.end());
}

TEST(ParserTest, StructureInstantiationWithLambda) {
    // mul binding uses a lambda expression
    auto r = parse_str(
        "definition M : Monoid :=\n"
        "  mul := fun a => a\n"
        "  one := 0\n"
    );
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.struct_type, "Monoid");
    auto it = d.struct_bindings.find("mul");
    ASSERT_NE(it, d.struct_bindings.end());
    EXPECT_NE(std::get_if<ExprLambda>(&it->second->node), nullptr);
}

// ── Pi types ─────────────────────────────────────────────────────────────

TEST(ParserTest, TypePiBasic) {
    // "(G : Group) -> Prop" as a binder type parses to TypePi
    auto r = parse_str("axiom a : for all f : (G : Group) -> Prop, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    ASSERT_TRUE(fa->type.has_value());
    const auto* pi = std::get_if<ast::TypePi>(&fa->type->node);
    ASSERT_NE(pi, nullptr);
    EXPECT_EQ(pi->var, "G");
    ASSERT_NE(pi->domain, nullptr);
    EXPECT_EQ(*pi->domain, ast::type_user("Group"));
    ASSERT_NE(pi->codomain, nullptr);
    EXPECT_EQ(*pi->codomain, ast::TypeNode{ast::TypeProp{}});
}

TEST(ParserTest, TypePiVsTypeFun) {
    // "Nat -> Real" still parses as TypeFun (no bound variable)
    auto r = parse_str("axiom a : for all f : Nat -> Real, P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    ASSERT_TRUE(fa->type.has_value());
    const auto* fun = std::get_if<ast::TypeFun>(&fa->type->node);
    ASSERT_NE(fun, nullptr);
    EXPECT_EQ(*fun->domain, ast::type_nat());
    EXPECT_EQ(*fun->codomain, ast::type_real());
}

TEST(ParserTest, TypePiVsTypeTuple) {
    // "(Nat, Real)" without "->" still parses as TypeTuple
    auto r = parse_str("axiom a : for all p : (Nat, Real), P");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* fa = std::get_if<ast::PropForall>(&r.mod.decls[0]->statement.node);
    ASSERT_NE(fa, nullptr);
    ASSERT_TRUE(fa->type.has_value());
    const auto* tt = std::get_if<ast::TypeTuple>(&fa->type->node);
    ASSERT_NE(tt, nullptr);
    ASSERT_EQ(tt->elements.size(), 2u);
    EXPECT_EQ(*tt->elements[0], ast::type_nat());
    EXPECT_EQ(*tt->elements[1], ast::type_real());
}

// ── Quotient type declarations ───────────────────────────────────────────

TEST(ParserTest, QuotientBasic) {
    // quotient Z2 := Int over eq2
    // No axiom fields — minimal form.
    auto r = parse_str(R"(
quotient Z2 := Int over eq2
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, DeclKind::Quotient);
    EXPECT_EQ(d.name, "Z2");
    EXPECT_EQ(d.quot_carrier, "Int");
    EXPECT_EQ(d.quot_rel, "eq2");
    EXPECT_EQ(d.fields.size(), 0u);
}

TEST(ParserTest, QuotientWithAxioms) {
    // quotient type with three equivalence axioms
    auto r = parse_str(R"(
quotient IntMod2 := Int over mod2_eq
  axiom mod2_refl  : for all a : Int, mod2_eq(a, a)
  axiom mod2_symm  : for all a b : Int, mod2_eq(a, b) -> mod2_eq(b, a)
  axiom mod2_trans : for all a b c : Int, mod2_eq(a, b) -> mod2_eq(b, c) -> mod2_eq(a, c)
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, DeclKind::Quotient);
    EXPECT_EQ(d.name, "IntMod2");
    EXPECT_EQ(d.quot_carrier, "Int");
    EXPECT_EQ(d.quot_rel, "mod2_eq");
    ASSERT_EQ(d.fields.size(), 3u);
    const auto* a0 = std::get_if<ast::FieldAxiom>(&d.fields[0]);
    ASSERT_NE(a0, nullptr);
    EXPECT_EQ(a0->name, "mod2_refl");
    const auto* a1 = std::get_if<ast::FieldAxiom>(&d.fields[1]);
    ASSERT_NE(a1, nullptr);
    EXPECT_EQ(a1->name, "mod2_symm");
    const auto* a2 = std::get_if<ast::FieldAxiom>(&d.fields[2]);
    ASSERT_NE(a2, nullptr);
    EXPECT_EQ(a2->name, "mod2_trans");
}

TEST(ParserTest, QuotientMalformed) {
    // Missing name after 'quotient' should produce a parse error
    auto r = parse_str("quotient :=");
    EXPECT_TRUE(r.diag.hasErrors());
}

// ── NL natural-language step aliases ─────────────────────────────────────────

// "note that P by refs" and "observe that P by refs" → HaveStep{"_", P, refs}
TEST(ParserTest, NL4_NoteThatHaveStep) {
    auto r = parse_str(R"(theorem t : P
proof
  suppose h : P
  note that P by h
  observe that P by h
  then P by h
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_TRUE(r.mod.decls[0]->proof.has_value());
    const auto& steps = r.mod.decls[0]->proof->steps;
    ASSERT_GE(steps.size(), 3u);
    // step[1] = note that P by h
    const auto* have1 = get_step<HaveStep>(*r.mod.decls[0]->proof, 1);
    ASSERT_NE(have1, nullptr);
    EXPECT_EQ(have1->name, "_");
    ASSERT_EQ(have1->justification.size(), 1u);
    EXPECT_EQ(have1->justification[0], "h");
    // step[2] = observe that P by h
    const auto* have2 = get_step<HaveStep>(*r.mod.decls[0]->proof, 2);
    ASSERT_NE(have2, nullptr);
    EXPECT_EQ(have2->name, "_");
}

// "since h1 and h2, have h : P"
TEST(ParserTest, NL5_SinceHaveStep) {
    auto r = parse_str(R"(theorem t : P and Q
proof
  suppose hp : P
  suppose hq : Q
  since hp and hq, have hpq : P and Q
  then P and Q by hpq
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* have = get_step<HaveStep>(*r.mod.decls[0]->proof, 2);
    ASSERT_NE(have, nullptr);
    EXPECT_EQ(have->name, "hpq");
    ASSERT_EQ(have->justification.size(), 2u);
    EXPECT_EQ(have->justification[0], "hp");
    EXPECT_EQ(have->justification[1], "hq");
}

// "by definition of X", "by axiom of X", "by lemma X", "by theorem X"
TEST(ParserTest, NL6_QualifiedJustification) {
    // All four forms: qualifiers discarded, only the ref name kept
    auto r = parse_str(R"(theorem t : P
proof
  suppose h1 : P
  suppose h2 : P
  suppose h3 : P
  suppose h4 : P
  have a1 : P by definition of h1
  have a2 : P by axiom of h2
  have a3 : P by lemma h3
  have a4 : P by theorem h4
  then P by h1
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    // step[4] = have a1 : P by definition of h1
    const auto* s1 = get_step<HaveStep>(*r.mod.decls[0]->proof, 4);
    ASSERT_NE(s1, nullptr);
    ASSERT_EQ(s1->justification.size(), 1u);
    EXPECT_EQ(s1->justification[0], "h1");
    // step[5] = have a2 : P by axiom of h2
    const auto* s2 = get_step<HaveStep>(*r.mod.decls[0]->proof, 5);
    ASSERT_NE(s2, nullptr);
    EXPECT_EQ(s2->justification[0], "h2");
    // step[6] = have a3 : P by lemma h3
    const auto* s3 = get_step<HaveStep>(*r.mod.decls[0]->proof, 6);
    ASSERT_NE(s3, nullptr);
    EXPECT_EQ(s3->justification[0], "h3");
    // step[7] = have a4 : P by theorem h4
    const auto* s4 = get_step<HaveStep>(*r.mod.decls[0]->proof, 7);
    ASSERT_NE(s4, nullptr);
    EXPECT_EQ(s4->justification[0], "h4");
}

// "fix x : T" same as "take x : T" (lexer alias, produces TakeStep)
TEST(ParserTest, NL7_FixAliasTake) {
    auto r1 = parse_str(R"(theorem t : P proof take x : Nat end)");
    auto r2 = parse_str(R"(theorem t : P proof fix x : Nat end)");
    ASSERT_FALSE(r1.diag.hasErrors());
    ASSERT_FALSE(r2.diag.hasErrors());
    const auto* s1 = get_step<TakeStep>(*r1.mod.decls[0]->proof, 0);
    const auto* s2 = get_step<TakeStep>(*r2.mod.decls[0]->proof, 0);
    ASSERT_NE(s1, nullptr);
    ASSERT_NE(s2, nullptr);
    EXPECT_EQ(s1->var, s2->var);
}

// "let n be arbitrary [in T]" → TakeStep
TEST(ParserTest, NL8_LetBeArbitrary) {
    auto r1 = parse_str(R"(theorem t : P proof let n be arbitrary end)");
    auto r2 = parse_str(R"(theorem t : P proof let n be arbitrary in Nat end)");
    ASSERT_FALSE(r1.diag.hasErrors()) << "let n be arbitrary failed";
    ASSERT_FALSE(r2.diag.hasErrors()) << "let n be arbitrary in Nat failed";
    const auto* s1 = get_step<TakeStep>(*r1.mod.decls[0]->proof, 0);
    const auto* s2 = get_step<TakeStep>(*r2.mod.decls[0]->proof, 0);
    ASSERT_NE(s1, nullptr);
    ASSERT_NE(s2, nullptr);
    EXPECT_EQ(s1->var, "n");
    EXPECT_FALSE(s1->type.has_value());
    EXPECT_EQ(s2->var, "n");
    ASSERT_TRUE(s2->type.has_value());
    EXPECT_EQ(forall::pretty::to_string(*s2->type), "Nat");
}

// "we need to show P" and "it suffices to show P" → ShowStep
TEST(ParserTest, NL9_WeNeedToShow) {
    auto r = parse_str(R"(theorem t : P
proof
  suppose h : P
  we need to show P
  it suffices to show P
  then P by h
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s1 = get_step<ShowStep>(*r.mod.decls[0]->proof, 1);
    ASSERT_NE(s1, nullptr);
    EXPECT_NE(std::get_if<Atomic>(&s1->prop.node), nullptr);
    const auto* s2 = get_step<ShowStep>(*r.mod.decls[0]->proof, 2);
    ASSERT_NE(s2, nullptr);
}

// "so P [by refs]", "which gives P", "which shows P" → ThenStep
TEST(ParserTest, NL10_SoWhichGives) {
    auto r1 = parse_str(R"(theorem t : P proof suppose h : P so P by h end)");
    ASSERT_FALSE(r1.diag.hasErrors());
    const auto* s1 = get_step<ThenStep>(*r1.mod.decls[0]->proof, 1);
    ASSERT_NE(s1, nullptr);
    ASSERT_EQ(s1->justification.size(), 1u);
    EXPECT_EQ(s1->justification[0], "h");

    auto r2 = parse_str(R"(theorem t : P proof suppose h : P which gives P by h end)");
    ASSERT_FALSE(r2.diag.hasErrors());
    const auto* s2 = get_step<ThenStep>(*r2.mod.decls[0]->proof, 1);
    ASSERT_NE(s2, nullptr);

    auto r3 = parse_str(R"(theorem t : P proof suppose h : P which shows P by h end)");
    ASSERT_FALSE(r3.diag.hasErrors());
    const auto* s3 = get_step<ThenStep>(*r3.mod.decls[0]->proof, 1);
    ASSERT_NE(s3, nullptr);
}

// "we know X" → HaveStep{"_", Atomic{X}, [X]}
TEST(ParserTest, NL13_WeKnow) {
    auto r = parse_str(R"(theorem t : P
proof
  suppose h : P
  we know h
  then P by h
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<HaveStep>(*r.mod.decls[0]->proof, 1);
    ASSERT_NE(s, nullptr);
    EXPECT_EQ(s->name, "_");
    ASSERT_EQ(s->justification.size(), 1u);
    EXPECT_EQ(s->justification[0], "h");
    // prop should be Atomic{"h"}
    const auto* a = std::get_if<Atomic>(&s->prop.node);
    ASSERT_NE(a, nullptr);
    EXPECT_EQ(a->name, "h");
}

// "hence P [by refs]" maps to ThenStep (lexer alias)
//        "it follows that P [by refs]" → ThenStep
TEST(ParserTest, NL15_HenceAndItFollowsThat) {
    auto r1 = parse_str(R"(theorem t : P proof suppose h : P hence P by h end)");
    ASSERT_FALSE(r1.diag.hasErrors());
    const auto* s1 = get_step<ThenStep>(*r1.mod.decls[0]->proof, 1);
    ASSERT_NE(s1, nullptr);
    ASSERT_EQ(s1->justification.size(), 1u);
    EXPECT_EQ(s1->justification[0], "h");

    auto r2 = parse_str(R"(theorem t : P proof suppose h : P it follows that P by h end)");
    ASSERT_FALSE(r2.diag.hasErrors());
    const auto* s2 = get_step<ThenStep>(*r2.mod.decls[0]->proof, 1);
    ASSERT_NE(s2, nullptr);
    ASSERT_EQ(s2->justification.size(), 1u);
    EXPECT_EQ(s2->justification[0], "h");
}

// "by hypothesis" / "by assumption" → __hypothesis__ / __assumption__ sentinels
TEST(ParserTest, NL16_ByHypothesis) {
    auto r = parse_str(R"(theorem t : P
proof
  suppose h : P
  have a : P by hypothesis
  have b : P by assumption
  then P by h
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s1 = get_step<HaveStep>(*r.mod.decls[0]->proof, 1);
    ASSERT_NE(s1, nullptr);
    ASSERT_EQ(s1->justification.size(), 1u);
    EXPECT_EQ(s1->justification[0], "__hypothesis__");
    const auto* s2 = get_step<HaveStep>(*r.mod.decls[0]->proof, 2);
    ASSERT_NE(s2, nullptr);
    EXPECT_EQ(s2->justification[0], "__assumption__");
}

// "we prove that P" → ShowStep{P}
TEST(ParserTest, NL18_WeProveThat) {
    auto r = parse_str(R"(theorem t : P
proof
  suppose h : P
  we prove that P
  then P by h
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* s = get_step<ShowStep>(*r.mod.decls[0]->proof, 1);
    ASSERT_NE(s, nullptr);
    EXPECT_NE(std::get_if<Atomic>(&s->prop.node), nullptr);
}

// "suppose h1 : P and h2 : Q" → two SupposeSteps
TEST(ParserTest, NL19_SupposeMultiple) {
    auto r = parse_str(R"(theorem t : P and Q
proof
  suppose hp : P and hq : Q
  then P and Q by hp and hq
end)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto& steps = r.mod.decls[0]->proof->steps;
    ASSERT_GE(steps.size(), 3u);
    // steps[0] = suppose hp : P
    const auto* s1 = get_step<SupposeStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(s1, nullptr);
    ASSERT_TRUE(s1->name.has_value());
    EXPECT_EQ(*s1->name, "hp");
    // steps[1] = suppose hq : Q (from deferred queue)
    const auto* s2 = get_step<SupposeStep>(*r.mod.decls[0]->proof, 1);
    ASSERT_NE(s2, nullptr);
    ASSERT_TRUE(s2->name.has_value());
    EXPECT_EQ(*s2->name, "hq");
}

// ── calc step tests ──────────────────────────────────────────────────────

// basic equality chain  a = b by h1  = c by h2
TEST(ParserTest, CalcStep_BasicEqualityChain) {
    auto r = parse_str(R"(
theorem t : a = a
proof
  calc a = b by h1 = c by h2
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* cs = get_step<CalcStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(cs, nullptr);
    EXPECT_TRUE(cs->name.empty());
    // lhs is ExprVar "a"
    const auto* lhs_var = std::get_if<ExprVar>(&cs->lhs->node);
    ASSERT_NE(lhs_var, nullptr);
    EXPECT_EQ(lhs_var->name, "a");
    // Two links
    ASSERT_EQ(cs->links.size(), 2u);
    EXPECT_EQ(cs->links[0].op, RelOp::Eq);
    EXPECT_EQ(cs->links[0].justification.size(), 1u);
    EXPECT_EQ(cs->links[0].justification[0], "h1");
    EXPECT_EQ(cs->links[1].op, RelOp::Eq);
    EXPECT_EQ(cs->links[1].justification[0], "h2");
}

// mixed ≤ = < chain
TEST(ParserTest, CalcStep_MixedOps) {
    auto r = parse_str(R"(
theorem t : a < a
proof
  calc a <= b by h1 = c by h2 < d by h3
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* cs = get_step<CalcStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(cs, nullptr);
    ASSERT_EQ(cs->links.size(), 3u);
    EXPECT_EQ(cs->links[0].op, RelOp::LtEq);
    EXPECT_EQ(cs->links[1].op, RelOp::Eq);
    EXPECT_EQ(cs->links[2].op, RelOp::Lt);
}

// named calc result
TEST(ParserTest, CalcStep_NamedResult) {
    auto r = parse_str(R"(
theorem t : a <= a
proof
  calc result : a <= b by h1 = c by h2
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* cs = get_step<CalcStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(cs, nullptr);
    EXPECT_EQ(cs->name, "result");
    ASSERT_EQ(cs->links.size(), 2u);
}

// single-link calc (trivial)
TEST(ParserTest, CalcStep_SingleLink) {
    auto r = parse_str(R"(
theorem t : a = a
proof
  calc a = b by h1
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* cs = get_step<CalcStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(cs, nullptr);
    ASSERT_EQ(cs->links.size(), 1u);
    EXPECT_EQ(cs->links[0].op, RelOp::Eq);
}

// calc inside a full theorem with other steps
TEST(ParserTest, CalcStep_InFullTheorem) {
    auto r = parse_str(R"(
theorem t : x < z
proof
  suppose h1 : x < y
  suppose h2 : y = z
  calc res : x < y by h1 = z by h2
  then x < z by res
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto& steps = r.mod.decls[0]->proof->steps;
    ASSERT_EQ(steps.size(), 4u);
    // Step 2 (index 2) is the calc
    const auto* cs = std::get_if<CalcStep>(&steps[2].node);
    ASSERT_NE(cs, nullptr);
    EXPECT_EQ(cs->name, "res");
    ASSERT_EQ(cs->links.size(), 2u);
    // Step 3 is the then
    const auto* ts = std::get_if<ThenStep>(&steps[3].node);
    ASSERT_NE(ts, nullptr);
}

// ── split step tests ─────────────────────────────────────────────────────

// conjunction split — left/right arms parse correctly
TEST(ParserTest, SplitStep_ConjunctionLeftRight) {
    auto r = parse_str(R"(
theorem t : P and Q
proof
  split
    case left =>
      then P by hp
    case right =>
      then Q by hq
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls[0]->proof->steps.size(), 1u);
    const auto* ss = std::get_if<SplitStep>(&r.mod.decls[0]->proof->steps[0].node);
    ASSERT_NE(ss, nullptr);
    EXPECT_TRUE(ss->name.empty());
    ASSERT_EQ(ss->arms.size(), 2u);
    EXPECT_EQ(ss->arms[0].label, "left");
    EXPECT_EQ(ss->arms[1].label, "right");
    ASSERT_EQ(ss->arms[0].steps.size(), 1u);
    ASSERT_EQ(ss->arms[1].steps.size(), 1u);
}

// biconditional split — (->) and (<-) labels
TEST(ParserTest, SplitStep_BiconditionalArrows) {
    auto r = parse_str(R"(
theorem t : P iff Q
proof
  split
    case (->) =>
      suppose hp : P
      then Q by hpq and hp
    case (<-) =>
      suppose hq : Q
      then P by hqp and hq
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ss = std::get_if<SplitStep>(&r.mod.decls[0]->proof->steps[0].node);
    ASSERT_NE(ss, nullptr);
    ASSERT_EQ(ss->arms.size(), 2u);
    // Labels include both enclosing parens: (->) and (<-)
    EXPECT_EQ(ss->arms[0].label[0], '(');
    EXPECT_NE(ss->arms[0].label.find('>'), std::string::npos);
    EXPECT_EQ(ss->arms[1].label[0], '(');
    EXPECT_NE(ss->arms[1].label.find('-'), std::string::npos);
    // Both arms have steps
    ASSERT_GE(ss->arms[0].steps.size(), 2u);
    ASSERT_GE(ss->arms[1].steps.size(), 2u);
}

// named split result
TEST(ParserTest, SplitStep_NamedResult) {
    auto r = parse_str(R"(
theorem t : P and Q
proof
  split conj :
    case left =>
      then P by hp
    case right =>
      then Q by hq
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ss = std::get_if<SplitStep>(&r.mod.decls[0]->proof->steps[0].node);
    ASSERT_NE(ss, nullptr);
    EXPECT_EQ(ss->name, "conj");
    ASSERT_EQ(ss->arms.size(), 2u);
}

// ── inline have sub-proofs ───────────────────────────────────────────────

TEST(ParserTest, NL11_HaveSubProofBasic) {
    auto r = parse_str(R"(
theorem t : P and Q
proof
  have h : P
  proof
    suppose hp : P
    then P by hp
  end
  suppose hq : Q
  then P and Q by h and hq
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_TRUE(r.mod.decls[0]->proof.has_value());
    const auto* hs = get_step<HaveStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(hs, nullptr);
    EXPECT_EQ(hs->name, "h");
    ASSERT_NE(hs->sub_proof, nullptr);
    EXPECT_EQ(hs->sub_proof->steps.size(), 2u);
    EXPECT_TRUE(hs->justification.empty());
}

TEST(ParserTest, NL11_HaveSubProofNested) {
    // Inner sub-proof itself contains a have step with a sub-proof.
    auto r = parse_str(R"(
theorem t : P
proof
  have outer : P
  proof
    have inner : P
    proof
      suppose hp : P
      then P by hp
    end
    then P by inner
  end
  then P by outer
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_TRUE(r.mod.decls[0]->proof.has_value());
    const auto* hs_outer = get_step<HaveStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(hs_outer, nullptr);
    ASSERT_NE(hs_outer->sub_proof, nullptr);
    // First step of the outer sub-proof should be another HaveStep with its own sub-proof.
    ASSERT_FALSE(hs_outer->sub_proof->steps.empty());
    const auto* hs_inner = std::get_if<HaveStep>(&hs_outer->sub_proof->steps[0].node);
    ASSERT_NE(hs_inner, nullptr);
    ASSERT_NE(hs_inner->sub_proof, nullptr);
}

// ── wlog step ────────────────────────────────────────────────────────────

TEST(ParserTest, NL14_WlogBasic) {
    auto r = parse_str(R"(
theorem t : P
proof
  wlog hw : P
  then P by hw
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_TRUE(r.mod.decls[0]->proof.has_value());
    const auto* ws = get_step<WlogStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(ws, nullptr);
    EXPECT_EQ(ws->name, "hw");
    const auto* atom = std::get_if<Atomic>(&ws->prop.node);
    ASSERT_NE(atom, nullptr);
    EXPECT_EQ(atom->name, "P");
}

// ── direction-marker biconditional proofs ────────────────────────────────

TEST(ParserTest, NL20_DirectionMarkersProduceSplitStep) {
    // A proof block starting with (→) / (←) should be parsed as a SplitStep.
    auto r = parse_str(R"(
theorem t : P iff Q
proof
  (->)
    suppose hp : P
    then Q by hp
  (<-)
    suppose hq : Q
    then P by hq
end
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_TRUE(r.mod.decls[0]->proof.has_value());
    // The proof block should have a single SplitStep.
    ASSERT_EQ(r.mod.decls[0]->proof->steps.size(), 1u);
    const auto* ss = get_step<SplitStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(ss, nullptr);
    ASSERT_EQ(ss->arms.size(), 2u);
    EXPECT_EQ(ss->arms[0].label, "(->)");
    EXPECT_EQ(ss->arms[1].label, "(<-)");
}

TEST(ParserTest, NL20_DirectionMarkersBackwardFromKeyword) {
    // (<-) using ASCII "<-" tokens should produce the same structure.
    auto r = parse_str(R"(
theorem t : P iff Q
proof
  (->)
    suppose hp : P
    then Q by hp
  (->)
    suppose hq : Q
    then P by hq
end
)");
    // Two (→) markers: both arms get "->" label, which is fine structurally.
    ASSERT_FALSE(r.diag.hasErrors());
    const auto* ss = get_step<SplitStep>(*r.mod.decls[0]->proof, 0);
    ASSERT_NE(ss, nullptr);
    ASSERT_EQ(ss->arms.size(), 2u);
}

// ── namespace blocks ─────────────────────────────────────────────────────

TEST(ParserTest, Namespace_ParsesInnerDecls) {
    auto r = parse_str(R"(
namespace Foo
  axiom bar : P
  axiom baz : Q
end Foo
)");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& ns = *r.mod.decls[0];
    EXPECT_EQ(ns.kind, DeclKind::Namespace);
    EXPECT_EQ(ns.name, "Foo");
    EXPECT_EQ(ns.ns_decls.size(), 2u);
}

TEST(ParserTest, Open_ParsesNamespaceName) {
    auto r = parse_str("open MyNs");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->kind, DeclKind::Open);
    EXPECT_EQ(r.mod.decls[0]->name, "MyNs");
}

// ── private/protected visibility ────────────────────────────────────────

TEST(ParserTest, Private_AxiomVisibility) {
    auto r = parse_str("private axiom secret : P");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->visibility, Visibility::Private);
    EXPECT_EQ(r.mod.decls[0]->kind, DeclKind::Axiom);
}

TEST(ParserTest, Protected_DefinitionVisibility) {
    auto r = parse_str("protected definition shared : P");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_EQ(r.mod.decls[0]->visibility, Visibility::Protected);
    EXPECT_EQ(r.mod.decls[0]->kind, DeclKind::Definition);
}

// ── abstract definitions ────────────────────────────────────────────────

TEST(ParserTest, AbstractDefinition_SetsFlag) {
    auto r = parse_str("abstract definition f : P -> Q");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_TRUE(r.mod.decls[0]->is_abstract);
    EXPECT_EQ(r.mod.decls[0]->kind, DeclKind::Definition);
}

TEST(ParserTest, NonAbstractDefinition_FlagIsFalse) {
    auto r = parse_str("definition f : P -> Q");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_FALSE(r.mod.decls[0]->is_abstract);
}

// Predicate definition with body: definition P(x : T) : Prop := body
// Parser should produce def_body pointing to the parsed proposition.
TEST(ParserTest, DefinitionWithBody_SingleParam) {
    auto r = parse_str("definition IsEven (n : Nat) : Prop := there exists k : Nat, n = k + k");
    ASSERT_FALSE(r.diag.hasErrors()) << [&]{
        std::string m; for (auto& d : r.diag.diagnostics()) m += d.message + "\n"; return m; }();
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, DeclKind::Definition);
    EXPECT_EQ(d.name, "IsEven");
    ASSERT_EQ(d.params.size(), 1u);
    EXPECT_EQ(d.params[0].name, "n");
    ASSERT_TRUE(d.def_body.has_value());
    // Body should be an existential: ∃ k : Nat, n = k + k
    const auto* ex = std::get_if<PropExists>(&(*d.def_body)->node);
    ASSERT_NE(ex, nullptr);
    EXPECT_EQ(ex->var, "k");
}

// Predicate definition with two params and a relational body.
TEST(ParserTest, DefinitionWithBody_TwoParams) {
    auto r = parse_str("definition Divides (a : Nat) (b : Nat) : Prop := there exists k : Nat, b = a * k");
    ASSERT_FALSE(r.diag.hasErrors()) << [&]{
        std::string m; for (auto& d : r.diag.diagnostics()) m += d.message + "\n"; return m; }();
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, DeclKind::Definition);
    ASSERT_EQ(d.params.size(), 2u);
    EXPECT_EQ(d.params[0].name, "a");
    EXPECT_EQ(d.params[1].name, "b");
    ASSERT_TRUE(d.def_body.has_value());
}

// Definition without body: no def_body present.
TEST(ParserTest, DefinitionWithoutBody_NoDefBody) {
    auto r = parse_str("definition P (x : Nat) : Prop");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    EXPECT_FALSE(r.mod.decls[0]->def_body.has_value());
}

// ── Type alias declarations ────────────────────────────────────────────────────

TEST(ParserTest, TypeAlias_Simple) {
    // "type Sequence = Nat -> Real" parses as DeclKind::TypeAlias with TypeFun body.
    auto r = parse_str("type Sequence = Nat -> Real");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, ast::DeclKind::TypeAlias);
    EXPECT_EQ(d.name, "Sequence");
    ASSERT_TRUE(d.type_alias_body.has_value());
    const auto* tf = std::get_if<ast::TypeFun>(&d.type_alias_body->node);
    ASSERT_NE(tf, nullptr);
    EXPECT_TRUE(std::get_if<ast::TypeNat>(&tf->domain->node) != nullptr);
    EXPECT_TRUE(std::get_if<ast::TypeReal>(&tf->codomain->node) != nullptr);
}

TEST(ParserTest, TypeAlias_NestedFun) {
    // "type Matrix = Nat -> Nat -> Real" parses as a right-nested TypeFun.
    auto r = parse_str("type Matrix = Nat -> Nat -> Real");
    ASSERT_FALSE(r.diag.hasErrors());
    ASSERT_EQ(r.mod.decls.size(), 1u);
    const auto& d = *r.mod.decls[0];
    EXPECT_EQ(d.kind, ast::DeclKind::TypeAlias);
    ASSERT_TRUE(d.type_alias_body.has_value());
    const auto* tf = std::get_if<ast::TypeFun>(&d.type_alias_body->node);
    ASSERT_NE(tf, nullptr);
    EXPECT_TRUE(std::get_if<ast::TypeNat>(&tf->domain->node) != nullptr);
    // codomain is Nat -> Real
    const auto* tf2 = std::get_if<ast::TypeFun>(&tf->codomain->node);
    ASSERT_NE(tf2, nullptr);
    EXPECT_TRUE(std::get_if<ast::TypeNat>(&tf2->domain->node) != nullptr);
    EXPECT_TRUE(std::get_if<ast::TypeReal>(&tf2->codomain->node) != nullptr);
}
