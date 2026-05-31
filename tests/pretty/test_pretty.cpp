#include <gtest/gtest.h>
#include <forall/pretty/to_string.hpp>
#include <forall/ast/node.hpp>
#include <forall/diagnostics/source_location.hpp>

using namespace forall;
using namespace forall::ast;

// ── Test helpers ───────────────────────────────────────────────────────────────

static diag::SourceLocation loc{};

static Expr E(ExprNode n) { return {loc, std::move(n)}; }
static Prop P(PropNode n) { return {loc, std::move(n)}; }

static ExprPtr EP(ExprNode n) { return make_expr(E(std::move(n))); }
static PropPtr PP(PropNode n) { return make_prop(P(std::move(n))); }

static std::string ts(ExprNode n) { return pretty::to_string(E(std::move(n))); }
static std::string ts(PropNode n) { return pretty::to_string(P(std::move(n))); }

// ── Expression tests ───────────────────────────────────────────────────────────

TEST(PrettyExpr, Lit) {
    EXPECT_EQ(ts(ExprLit{"42"}), "42");
    EXPECT_EQ(ts(ExprLit{"3.14"}), "3.14");
}

TEST(PrettyExpr, Var) {
    EXPECT_EQ(ts(ExprVar{"x"}), "x");
    EXPECT_EQ(ts(ExprVar{"epsilon"}), "epsilon");
}

TEST(PrettyExpr, AddSub) {
    EXPECT_EQ(ts(ExprBinary{BinOp::Add, EP(ExprVar{"a"}), EP(ExprVar{"b"})}), "a + b");
    EXPECT_EQ(ts(ExprBinary{BinOp::Sub, EP(ExprVar{"a"}), EP(ExprVar{"b"})}), "a - b");
}

TEST(PrettyExpr, MulDiv) {
    EXPECT_EQ(ts(ExprBinary{BinOp::Mul, EP(ExprVar{"a"}), EP(ExprVar{"b"})}), "a * b");
    EXPECT_EQ(ts(ExprBinary{BinOp::Div, EP(ExprVar{"a"}), EP(ExprVar{"b"})}), "a / b");
    EXPECT_EQ(ts(ExprBinary{BinOp::IDiv, EP(ExprVar{"a"}), EP(ExprVar{"b"})}), "a div b");
    EXPECT_EQ(ts(ExprBinary{BinOp::Mod, EP(ExprVar{"a"}), EP(ExprVar{"b"})}), "a mod b");
}

TEST(PrettyExpr, Compose) {
    EXPECT_EQ(ts(ExprBinary{BinOp::Compose, EP(ExprVar{"f"}), EP(ExprVar{"g"})}), "f \xe2\x88\x98 g");
}

TEST(PrettyExpr, Pow) {
    EXPECT_EQ(ts(ExprBinary{BinOp::Pow, EP(ExprVar{"a"}), EP(ExprVar{"b"})}), "a^b");
}

// ── Precedence / parenthesization ─────────────────────────────────────────────

TEST(PrettyExpr, AddBindsLooserThanMul) {
    // (a + b) * c  — lhs of * is Add (prec 1 < 2), needs parens
    auto e = ExprBinary{BinOp::Mul,
        EP(ExprBinary{BinOp::Add, EP(ExprVar{"a"}), EP(ExprVar{"b"})}),
        EP(ExprVar{"c"})};
    EXPECT_EQ(ts(std::move(e)), "(a + b) * c");
}

TEST(PrettyExpr, RhsOfMulNeedsParens) {
    // a * (b + c)  — rhs of * is Add (prec 1 ≤ 2), needs parens
    auto e = ExprBinary{BinOp::Mul,
        EP(ExprVar{"a"}),
        EP(ExprBinary{BinOp::Add, EP(ExprVar{"b"}), EP(ExprVar{"c"})})};
    EXPECT_EQ(ts(std::move(e)), "a * (b + c)");
}

TEST(PrettyExpr, RhsOfDivAtSamePrecNeedsParens) {
    // a / (b * c)  — rhs of / is Mul (prec 2 ≤ 2), needs parens
    auto e = ExprBinary{BinOp::Div,
        EP(ExprVar{"a"}),
        EP(ExprBinary{BinOp::Mul, EP(ExprVar{"b"}), EP(ExprVar{"c"})})};
    EXPECT_EQ(ts(std::move(e)), "a / (b * c)");
}

TEST(PrettyExpr, SubLeftAssoc) {
    // (a - b) - c  — lhs of - is Sub at prec 1, no parens (left-assoc)
    auto e = ExprBinary{BinOp::Sub,
        EP(ExprBinary{BinOp::Sub, EP(ExprVar{"a"}), EP(ExprVar{"b"})}),
        EP(ExprVar{"c"})};
    EXPECT_EQ(ts(std::move(e)), "a - b - c");
}

TEST(PrettyExpr, SubRhsNeedsParens) {
    // a - (b - c)  — rhs of - is Sub (prec 1 ≤ 1), needs parens
    auto e = ExprBinary{BinOp::Sub,
        EP(ExprVar{"a"}),
        EP(ExprBinary{BinOp::Sub, EP(ExprVar{"b"}), EP(ExprVar{"c"})})};
    EXPECT_EQ(ts(std::move(e)), "a - (b - c)");
}

TEST(PrettyExpr, PowLhsMustBeAtom) {
    // (a + b)^c  — lhs of ^ is Add, not atom-level, needs parens
    auto e = ExprBinary{BinOp::Pow,
        EP(ExprBinary{BinOp::Add, EP(ExprVar{"a"}), EP(ExprVar{"b"})}),
        EP(ExprVar{"c"})};
    EXPECT_EQ(ts(std::move(e)), "(a + b)^c");
}

TEST(PrettyExpr, PowRhsNeedsParensForAdd) {
    // a^(b + c)  — rhs of ^ is Add (prec 1 < 3), needs parens
    auto e = ExprBinary{BinOp::Pow,
        EP(ExprVar{"a"}),
        EP(ExprBinary{BinOp::Add, EP(ExprVar{"b"}), EP(ExprVar{"c"})})};
    EXPECT_EQ(ts(std::move(e)), "a^(b + c)");
}

TEST(PrettyExpr, PowRhsNeedsParensForMul) {
    // a^(b * c)  — rhs of ^ is Mul (prec 2 < 3), needs parens
    auto e = ExprBinary{BinOp::Pow,
        EP(ExprVar{"a"}),
        EP(ExprBinary{BinOp::Mul, EP(ExprVar{"b"}), EP(ExprVar{"c"})})};
    EXPECT_EQ(ts(std::move(e)), "a^(b * c)");
}

TEST(PrettyExpr, PowRightAssocNoParens) {
    // a^(b^c)  — rhs of ^ is Pow (prec 3, not < 3), no parens
    auto e = ExprBinary{BinOp::Pow,
        EP(ExprVar{"a"}),
        EP(ExprBinary{BinOp::Pow, EP(ExprVar{"b"}), EP(ExprVar{"c"})})};
    EXPECT_EQ(ts(std::move(e)), "a^b^c");
}

TEST(PrettyExpr, UnaryNeg) {
    EXPECT_EQ(ts(ExprUnary{UnaryOp::Neg, EP(ExprVar{"x"})}), "-x");
}

TEST(PrettyExpr, UnaryNegOfAdd) {
    // -(a + b)  — operand of - is Add (prec 1 < 3), needs parens
    auto e = ExprUnary{UnaryOp::Neg,
        EP(ExprBinary{BinOp::Add, EP(ExprVar{"a"}), EP(ExprVar{"b"})})};
    EXPECT_EQ(ts(std::move(e)), "-(a + b)");
}

TEST(PrettyExpr, UnaryNegOfPow) {
    // -(a^b) — in our grammar -a^b = -(a^b), so no parens around a^b
    auto e = ExprUnary{UnaryOp::Neg,
        EP(ExprBinary{BinOp::Pow, EP(ExprVar{"a"}), EP(ExprVar{"b"})})};
    EXPECT_EQ(ts(std::move(e)), "-a^b");
}

TEST(PrettyExpr, AbsValue) {
    EXPECT_EQ(ts(ExprAbs{EP(ExprVar{"x"})}), "|x|");
}

TEST(PrettyExpr, FunctionCall) {
    std::vector<ExprPtr> args;
    args.push_back(EP(ExprVar{"x"}));
    args.push_back(EP(ExprVar{"y"}));
    EXPECT_EQ(ts(ExprCall{"f", std::move(args)}), "f(x, y)");
}

TEST(PrettyExpr, ZeroArgCall) {
    EXPECT_EQ(ts(ExprCall{"c", {}}), "c()");
}

TEST(PrettyExpr, InvCall) {
    std::vector<ExprPtr> args;
    args.push_back(EP(ExprVar{"f"}));
    EXPECT_EQ(ts(ExprCall{"inv", std::move(args)}), "inv(f)");
}

TEST(PrettyExpr, Index) {
    EXPECT_EQ(ts(ExprIndex{EP(ExprVar{"a"}), EP(ExprVar{"n"})}), "a[n]");
}

TEST(PrettyExpr, IndexNonAtomLhsNeedsParens) {
    // (a + b)[i]
    auto e = ExprIndex{
        EP(ExprBinary{BinOp::Add, EP(ExprVar{"a"}), EP(ExprVar{"b"})}),
        EP(ExprVar{"i"})};
    EXPECT_EQ(ts(std::move(e)), "(a + b)[i]");
}

TEST(PrettyExpr, Tuple) {
    std::vector<ExprPtr> elems;
    elems.push_back(EP(ExprVar{"a"}));
    elems.push_back(EP(ExprVar{"b"}));
    EXPECT_EQ(ts(ExprTuple{std::move(elems)}), "(a, b)");
}

TEST(PrettyExpr, LambdaNoType) {
    EXPECT_EQ(ts(ExprLambda{"x", std::nullopt, EP(ExprVar{"x"})}), "fun x => x");
}

TEST(PrettyExpr, LambdaWithType) {
    EXPECT_EQ(ts(ExprLambda{"x", TypeNode{TypeNat{}}, EP(ExprVar{"x"})}), "fun x : Nat => x");
}

TEST(PrettyExpr, AggSumTyped) {
    EXPECT_EQ(ts(ExprAgg{AggOp::Sum, "i", TypeNode{TypeNat{}}, std::nullopt, std::nullopt,
                          EP(ExprVar{"i"})}),
              "\xe2\x88\x91 i : Nat, i");
}

TEST(PrettyExpr, AggProdBounded) {
    EXPECT_EQ(ts(ExprAgg{AggOp::Prod, "i", std::nullopt, RelOp::Lt, EP(ExprVar{"n"}),
                          EP(ExprVar{"i"})}),
              "\xe2\x88\x8f i < n, i");
}

// ── Proposition tests ─────────────────────────────────────────────────────────

TEST(PrettyProp, Atomic) {
    EXPECT_EQ(ts(Atomic{"P"}), "P");
}

TEST(PrettyProp, False) {
    EXPECT_EQ(ts(PropFalse{}), "\xe2\x8a\xa5");  // ⊥
}

TEST(PrettyProp, Not) {
    EXPECT_EQ(ts(PropNot{PP(Atomic{"P"})}), "\xc2\xac" "P");  // ¬P
}

TEST(PrettyProp, NotOfAndNeedsParens) {
    // ¬(P ∧ Q)  — operand of ¬ is PropAnd (not atomic), needs parens
    auto e = PropNot{PP(PropAnd{PP(Atomic{"P"}), PP(Atomic{"Q"})})};
    EXPECT_EQ(ts(std::move(e)), "\xc2\xac(P \xe2\x88\xa7 Q)");
}

TEST(PrettyProp, And) {
    EXPECT_EQ(ts(PropAnd{PP(Atomic{"P"}), PP(Atomic{"Q"})}), "P \xe2\x88\xa7 Q");
}

TEST(PrettyProp, AndLeftAssoc) {
    // (P ∧ Q) ∧ R  — lhs of ∧ is PropAnd (prec 4, not < 4), no parens
    auto e = PropAnd{PP(PropAnd{PP(Atomic{"P"}), PP(Atomic{"Q"})}), PP(Atomic{"R"})};
    EXPECT_EQ(ts(std::move(e)), "P \xe2\x88\xa7 Q \xe2\x88\xa7 R");
}

TEST(PrettyProp, AndRhsNeedsParens) {
    // P ∧ (Q ∧ R)  — rhs of ∧ is PropAnd (prec 4 ≤ 4), needs parens
    auto e = PropAnd{PP(Atomic{"P"}), PP(PropAnd{PP(Atomic{"Q"}), PP(Atomic{"R"})})};
    EXPECT_EQ(ts(std::move(e)), "P \xe2\x88\xa7 (Q \xe2\x88\xa7 R)");
}

TEST(PrettyProp, Or) {
    EXPECT_EQ(ts(PropOr{PP(Atomic{"P"}), PP(Atomic{"Q"})}), "P \xe2\x88\xa8 Q");
}

TEST(PrettyProp, OrLhsImplNeedsParens) {
    // (P → Q) ∨ R  — lhs of ∨ is PropImpl (prec 2 < 3), needs parens
    auto e = PropOr{PP(PropImpl{PP(Atomic{"P"}), PP(Atomic{"Q"})}), PP(Atomic{"R"})};
    EXPECT_EQ(ts(std::move(e)), "(P \xe2\x86\x92 Q) \xe2\x88\xa8 R");
}

TEST(PrettyProp, AndBindsTighterThanOr) {
    // (P ∧ Q) ∨ R  — lhs of ∨ is PropAnd (prec 4, not < 3), no parens
    auto e = PropOr{PP(PropAnd{PP(Atomic{"P"}), PP(Atomic{"Q"})}), PP(Atomic{"R"})};
    EXPECT_EQ(ts(std::move(e)), "P \xe2\x88\xa7 Q \xe2\x88\xa8 R");
}

TEST(PrettyProp, Impl) {
    EXPECT_EQ(ts(PropImpl{PP(Atomic{"P"}), PP(Atomic{"Q"})}), "P \xe2\x86\x92 Q");
}

TEST(PrettyProp, ImplRightAssoc) {
    // P → (Q → R)  — rhs of → is PropImpl, no parens (right-assoc)
    auto e = PropImpl{PP(Atomic{"P"}), PP(PropImpl{PP(Atomic{"Q"}), PP(Atomic{"R"})})};
    EXPECT_EQ(ts(std::move(e)), "P \xe2\x86\x92 Q \xe2\x86\x92 R");
}

TEST(PrettyProp, ImplLhsImplNeedsParens) {
    // (P → Q) → R  — lhs of → is PropImpl (prec 2 ≤ 2), needs parens
    auto e = PropImpl{PP(PropImpl{PP(Atomic{"P"}), PP(Atomic{"Q"})}), PP(Atomic{"R"})};
    EXPECT_EQ(ts(std::move(e)), "(P \xe2\x86\x92 Q) \xe2\x86\x92 R");
}

TEST(PrettyProp, ImplLhsOrNoParens) {
    // P ∨ Q → R  — lhs of → is PropOr (prec 3, not ≤ 2), no parens
    auto e = PropImpl{PP(PropOr{PP(Atomic{"P"}), PP(Atomic{"Q"})}), PP(Atomic{"R"})};
    EXPECT_EQ(ts(std::move(e)), "P \xe2\x88\xa8 Q \xe2\x86\x92 R");
}

TEST(PrettyProp, Forall) {
    EXPECT_EQ(ts(PropForall{"x", std::nullopt, PP(Atomic{"P"})}), "\xe2\x88\x80 x, P");
}

TEST(PrettyProp, ForallWithType) {
    EXPECT_EQ(ts(PropForall{"x", TypeNode{TypeNat{}}, PP(Atomic{"P"})}), "\xe2\x88\x80 x : Nat, P");
}

TEST(PrettyProp, Exists) {
    EXPECT_EQ(ts(PropExists{"x", std::nullopt, PP(Atomic{"P"})}), "\xe2\x88\x83 x, P");
}

TEST(PrettyProp, ForallLhsOfImplNeedsParens) {
    // (∀ x, P) → Q  — lhs of → is PropForall (prec 0 ≤ 2), needs parens
    auto e = PropImpl{PP(PropForall{"x", std::nullopt, PP(Atomic{"P"})}), PP(Atomic{"Q"})};
    EXPECT_EQ(ts(std::move(e)), "(\xe2\x88\x80 x, P) \xe2\x86\x92 Q");
}

TEST(PrettyProp, Rel) {
    EXPECT_EQ(ts(PropRel{EP(ExprVar{"x"}), EP(ExprVar{"y"}), RelOp::Lt}), "x < y");
    EXPECT_EQ(ts(PropRel{EP(ExprVar{"x"}), EP(ExprVar{"y"}), RelOp::Eq}), "x = y");
    EXPECT_EQ(ts(PropRel{EP(ExprVar{"x"}), EP(ExprVar{"y"}), RelOp::LtEq}),
              "x \xe2\x89\xa4 y");  // ≤
}

TEST(PrettyProp, Pred) {
    std::vector<ExprPtr> args;
    args.push_back(EP(ExprVar{"n"}));
    EXPECT_EQ(ts(PropPred{"isPrime", std::move(args)}), "isPrime(n)");
}

// ── Set terms ─────────────────────────────────────────────────────────────────

TEST(PrettyProp, SetMembership) {
    EXPECT_EQ(ts(PropRel{EP(ExprVar{"x"}), EP(ExprVar{"S"}), RelOp::In}),
              "x \xe2\x88\x88 S");  // x ∈ S
}

TEST(PrettyProp, SetNonMembership) {
    EXPECT_EQ(ts(PropRel{EP(ExprVar{"x"}), EP(ExprVar{"S"}), RelOp::NotIn}),
              "x \xe2\x88\x89 S");  // x ∉ S
}

TEST(PrettyProp, SubsetEq) {
    EXPECT_EQ(ts(PropRel{EP(ExprVar{"A"}), EP(ExprVar{"B"}), RelOp::SubsetEq}),
              "A \xe2\x8a\x86 B");  // A ⊆ B
}

TEST(PrettyProp, StrictSubset) {
    EXPECT_EQ(ts(PropRel{EP(ExprVar{"A"}), EP(ExprVar{"B"}), RelOp::Subset}),
              "A \xe2\x8a\x82 B");  // A ⊂ B
}

TEST(PrettyProp, SupersetEq) {
    EXPECT_EQ(ts(PropRel{EP(ExprVar{"A"}), EP(ExprVar{"B"}), RelOp::SupersetEq}),
              "A \xe2\x8a\x87 B");  // A ⊇ B
}

TEST(PrettyExpr, SetLiteralEmpty) {
    EXPECT_EQ(ts(ExprSetLit{}), "{}");
}

TEST(PrettyExpr, SetLiteralElements) {
    std::vector<ExprPtr> elems;
    elems.push_back(EP(ExprVar{"a"}));
    elems.push_back(EP(ExprVar{"b"}));
    elems.push_back(EP(ExprVar{"c"}));
    EXPECT_EQ(ts(ExprSetLit{std::move(elems)}), "{a, b, c}");
}

TEST(PrettyExpr, SetComprehensionNoType) {
    EXPECT_EQ(ts(ExprSetCompr{"x", std::nullopt,
                               PP(PropRel{EP(ExprVar{"x"}), EP(ExprLit{"0"}), RelOp::Gt})}),
              "{x | x > 0}");
}

TEST(PrettyExpr, SetComprehensionWithType) {
    EXPECT_EQ(ts(ExprSetCompr{"x", TypeNode{TypeNat{}},
                               PP(PropRel{EP(ExprVar{"x"}), EP(ExprLit{"0"}), RelOp::Gt})}),
              "{x : Nat | x > 0}");
}

TEST(PrettyExpr, SetUnion) {
    EXPECT_EQ(ts(ExprBinary{BinOp::Union, EP(ExprVar{"A"}), EP(ExprVar{"B"})}),
              "A \xe2\x88\xaa B");  // A ∪ B
}

TEST(PrettyExpr, SetInter) {
    EXPECT_EQ(ts(ExprBinary{BinOp::Inter, EP(ExprVar{"A"}), EP(ExprVar{"B"})}),
              "A \xe2\x88\xa9 B");  // A ∩ B
}

TEST(PrettyExpr, SetMinus) {
    EXPECT_EQ(ts(ExprBinary{BinOp::SetMinus, EP(ExprVar{"A"}), EP(ExprVar{"B"})}),
              "A \xe2\x88\x96 B");  // A ∖ B
}

TEST(PrettyExpr, SetInterBindsTighterThanUnion) {
    // (A ∩ B) ∪ C — no extra parens needed; inter (prec 2) > union (prec 1)
    auto e = ExprBinary{BinOp::Union,
                EP(ExprBinary{BinOp::Inter, EP(ExprVar{"A"}), EP(ExprVar{"B"})}),
                EP(ExprVar{"C"})};
    EXPECT_EQ(ts(std::move(e)), "A \xe2\x88\xa9 B \xe2\x88\xaa C");
}

TEST(PrettyExpr, SetUnionLhsOfInterNeedsParens) {
    // (A ∪ B) ∩ C — lhs of inter is union (prec 1 < 2), needs parens
    auto e = ExprBinary{BinOp::Inter,
                EP(ExprBinary{BinOp::Union, EP(ExprVar{"A"}), EP(ExprVar{"B"})}),
                EP(ExprVar{"C"})};
    EXPECT_EQ(ts(std::move(e)), "(A \xe2\x88\xaa B) \xe2\x88\xa9 C");
}

TEST(PrettyExpr, SetLiteralIsAtomicNoParensInIndex) {
    // {a}[0]  — set literal is atomic, no extra parens needed
    std::vector<ExprPtr> elems;
    elems.push_back(EP(ExprVar{"a"}));
    auto base = EP(ExprSetLit{std::move(elems)});
    EXPECT_EQ(ts(ExprIndex{std::move(base), EP(ExprLit{"0"})}), "{a}[0]");
}
