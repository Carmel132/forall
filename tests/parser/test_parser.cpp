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
