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
    EXPECT_EQ(*fa->type, "Nat");
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
    EXPECT_EQ(*lam->type, "Nat");
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
    EXPECT_EQ(*lam->type, "Real");
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
    EXPECT_EQ(*agg->type, "Nat");
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
    EXPECT_EQ(*agg->type, "Nat");
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
    EXPECT_EQ(*sc->type, "Nat");
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
