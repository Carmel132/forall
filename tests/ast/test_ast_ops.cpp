#include <gtest/gtest.h>
#include <forall/ast/node.hpp>

#include <set>
#include <string>

using namespace forall;
using namespace forall::ast;

// ── Helpers ───────────────────────────────────────────────────────────────────

static Expr evar(std::string name) { return {diag::SourceLocation{}, ExprVar{std::move(name)}}; }
static Expr elit(std::string val)  { return {diag::SourceLocation{}, ExprLit{std::move(val)}}; }
static Expr ebin(BinOp op, Expr l, Expr r) {
    return {diag::SourceLocation{}, ExprBinary{op, make_expr(std::move(l)), make_expr(std::move(r))}};
}
static Expr elambda(std::string v, Expr body) {
    return {diag::SourceLocation{}, ExprLambda{std::move(v), std::nullopt, make_expr(std::move(body))}};
}
static Prop atom(std::string name) { return {diag::SourceLocation{}, Atomic{std::move(name)}}; }
static Prop prel(Expr l, RelOp op, Expr r) {
    return {diag::SourceLocation{}, PropRel{make_expr(std::move(l)), make_expr(std::move(r)), op}};
}
static Prop pforall(std::string v, Prop body) {
    return {diag::SourceLocation{}, PropForall{std::move(v), std::nullopt, make_prop(std::move(body))}};
}

// ── free_vars: expression tests ───────────────────────────────────────────────

TEST(FreeVars, ExprLit) {
    EXPECT_TRUE(free_vars(elit("42")).empty());
}

TEST(FreeVars, ExprVar) {
    EXPECT_EQ(free_vars(evar("x")), (std::set<std::string>{"x"}));
}

TEST(FreeVars, ExprBinary) {
    EXPECT_EQ(free_vars(ebin(BinOp::Add, evar("x"), evar("y"))),
              (std::set<std::string>{"x", "y"}));
}

TEST(FreeVars, ExprLambdaBoundNotFree) {
    // fun x => x   — x is bound
    EXPECT_TRUE(free_vars(elambda("x", evar("x"))).empty());
}

TEST(FreeVars, ExprLambdaFreeVar) {
    // fun x => y   — y is free
    EXPECT_EQ(free_vars(elambda("x", evar("y"))), (std::set<std::string>{"y"}));
}

TEST(FreeVars, ExprLambdaShadowing) {
    // fun x => x + z   — x is bound, z is free
    auto body = ebin(BinOp::Add, evar("x"), evar("z"));
    EXPECT_EQ(free_vars(elambda("x", std::move(body))), (std::set<std::string>{"z"}));
}

TEST(FreeVars, ExprLambdaNested) {
    // fun x => fun y => x + y + z   — x,y bound; z free
    auto inner = ebin(BinOp::Add, ebin(BinOp::Add, evar("x"), evar("y")), evar("z"));
    auto e = elambda("x", elambda("y", std::move(inner)));
    EXPECT_EQ(free_vars(e), (std::set<std::string>{"z"}));
}

// ── free_vars: proposition tests ──────────────────────────────────────────────

TEST(FreeVars, PropAtomNoTermVars) {
    // Atomic{P} carries no term variables
    EXPECT_TRUE(free_vars(atom("P")).empty());
}

TEST(FreeVars, PropRelHasFreeVars) {
    // x < y
    EXPECT_EQ(free_vars(prel(evar("x"), RelOp::Lt, evar("y"))),
              (std::set<std::string>{"x", "y"}));
}

TEST(FreeVars, PropForallBoundNotFree) {
    // ∀ x, x = x   — x is bound
    auto body = prel(evar("x"), RelOp::Eq, evar("x"));
    EXPECT_TRUE(free_vars(pforall("x", std::move(body))).empty());
}

TEST(FreeVars, PropForallFreeVar) {
    // ∀ x, x = y   — y is free
    auto body = prel(evar("x"), RelOp::Eq, evar("y"));
    EXPECT_EQ(free_vars(pforall("x", std::move(body))), (std::set<std::string>{"y"}));
}

TEST(FreeVars, PropForallShadowsBinder) {
    // ∀ x, ∀ x, x = 0   — inner binder shadows outer; x not free
    auto inner = pforall("x", prel(evar("x"), RelOp::Eq, elit("0")));
    EXPECT_TRUE(free_vars(pforall("x", std::move(inner))).empty());
}

// ── subst: expression tests ───────────────────────────────────────────────────

TEST(Subst, ExprVarMatch) {
    // subst(x, "x", 5) = 5
    auto result = subst(evar("x"), "x", elit("5"));
    const auto* l = std::get_if<ExprLit>(&result.node);
    ASSERT_NE(l, nullptr);
    EXPECT_EQ(l->value, "5");
}

TEST(Subst, ExprVarNoMatch) {
    // subst(y, "x", 5) = y
    auto result = subst(evar("y"), "x", elit("5"));
    const auto* v = std::get_if<ExprVar>(&result.node);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(v->name, "y");
}

TEST(Subst, ExprLitUnchanged) {
    auto result = subst(elit("42"), "x", elit("5"));
    const auto* l = std::get_if<ExprLit>(&result.node);
    ASSERT_NE(l, nullptr);
    EXPECT_EQ(l->value, "42");
}

TEST(Subst, ExprBinaryBothSides) {
    // subst(x + y, "x", 5) = 5 + y
    auto result = subst(ebin(BinOp::Add, evar("x"), evar("y")), "x", elit("5"));
    const auto* b = std::get_if<ExprBinary>(&result.node);
    ASSERT_NE(b, nullptr);
    const auto* lhs = std::get_if<ExprLit>(&b->lhs->node);
    ASSERT_NE(lhs, nullptr);
    EXPECT_EQ(lhs->value, "5");
    const auto* rhs = std::get_if<ExprVar>(&b->rhs->node);
    ASSERT_NE(rhs, nullptr);
    EXPECT_EQ(rhs->name, "y");
}

TEST(Subst, ExprLambdaShadowed) {
    // subst(fun x => x, "x", 5) = fun x => x   (binder shadows x)
    auto orig = elambda("x", evar("x"));
    EXPECT_EQ(subst(orig, "x", elit("5")), orig);
}

TEST(Subst, ExprLambdaNotShadowed) {
    // subst(fun x => y, "y", 5) = fun x => 5
    auto result = subst(elambda("x", evar("y")), "y", elit("5"));
    const auto* lam = std::get_if<ExprLambda>(&result.node);
    ASSERT_NE(lam, nullptr);
    EXPECT_EQ(lam->var, "x");
    const auto* body = std::get_if<ExprLit>(&lam->body->node);
    ASSERT_NE(body, nullptr);
    EXPECT_EQ(body->value, "5");
}

TEST(Subst, ExprSubstPropagatesDeep) {
    // subst(x + (y * x), "x", z) = z + (y * z)
    auto inner = ebin(BinOp::Mul, evar("y"), evar("x"));
    auto orig  = ebin(BinOp::Add, evar("x"), std::move(inner));
    auto result = subst(orig, "x", evar("z"));
    EXPECT_EQ(result, ebin(BinOp::Add, evar("z"), ebin(BinOp::Mul, evar("y"), evar("z"))));
}

// ── subst: proposition tests ──────────────────────────────────────────────────

TEST(Subst, PropAtomUnchanged) {
    // Atomic has no term vars — substitution is a no-op
    auto orig = atom("P");
    EXPECT_EQ(subst(orig, "x", elit("5")), orig);
}

TEST(Subst, PropRelSubstitutes) {
    // subst(x < y, "x", 5) => PropRel with lhs = 5
    auto result = subst(prel(evar("x"), RelOp::Lt, evar("y")), "x", elit("5"));
    const auto* rel = std::get_if<PropRel>(&result.node);
    ASSERT_NE(rel, nullptr);
    const auto* lhs = std::get_if<ExprLit>(&rel->lhs->node);
    ASSERT_NE(lhs, nullptr);
    EXPECT_EQ(lhs->value, "5");
    const auto* rhs = std::get_if<ExprVar>(&rel->rhs->node);
    ASSERT_NE(rhs, nullptr);
    EXPECT_EQ(rhs->name, "y");
}

TEST(Subst, PropForallShadowed) {
    // subst(∀ x, x = 0, "x", 5) = ∀ x, x = 0   (binder shadows x)
    auto orig = pforall("x", prel(evar("x"), RelOp::Eq, elit("0")));
    EXPECT_EQ(subst(orig, "x", elit("5")), orig);
}

TEST(Subst, PropForallNotShadowed) {
    // subst(∀ x, x = y, "y", 5) = ∀ x, x = 5
    auto result = subst(pforall("x", prel(evar("x"), RelOp::Eq, evar("y"))), "y", elit("5"));
    const auto* fa = std::get_if<PropForall>(&result.node);
    ASSERT_NE(fa, nullptr);
    EXPECT_EQ(fa->var, "x");
    const auto* body = std::get_if<PropRel>(&fa->body->node);
    ASSERT_NE(body, nullptr);
    const auto* rhs = std::get_if<ExprLit>(&body->rhs->node);
    ASSERT_NE(rhs, nullptr);
    EXPECT_EQ(rhs->value, "5");
}

TEST(Subst, PropForallNestedShadowing) {
    // subst(∀ x, ∀ y, x = y, "x", z) = ∀ x, ∀ y, x = y  (outer binder shadows)
    auto inner = pforall("y", prel(evar("x"), RelOp::Eq, evar("y")));
    auto orig  = pforall("x", std::move(inner));
    EXPECT_EQ(subst(orig, "x", evar("z")), orig);
}

// ── infer_type tests ──────────────────────────────────────────────────────────

static Expr elambda_typed(std::string v, TypeNode t, Expr body) {
    return {diag::SourceLocation{}, ExprLambda{std::move(v), std::move(t),
                                               make_expr(std::move(body))}};
}
static Expr eunary(Expr operand) {
    return {diag::SourceLocation{},
            ExprUnary{UnaryOp::Neg, make_expr(std::move(operand))}};
}
static Expr eabs(Expr operand) {
    return {diag::SourceLocation{}, ExprAbs{make_expr(std::move(operand))}};
}
static Expr eif(Expr then_, Expr else_) {
    auto cond = make_prop({diag::SourceLocation{}, Atomic{"P"}});
    return {diag::SourceLocation{},
            ExprIf{std::move(cond), make_expr(std::move(then_)), make_expr(std::move(else_))}};
}

TEST(InferType, Literal_NatNoDecimal) {
    EXPECT_EQ(*infer_type(elit("42"), {}), TypeNode{TypeNat{}});
}

TEST(InferType, Literal_RealWithDecimal) {
    EXPECT_EQ(*infer_type(elit("3.14"), {}), TypeNode{TypeReal{}});
}

TEST(InferType, Literal_RealScientific) {
    EXPECT_EQ(*infer_type(elit("1e10"), {}), TypeNode{TypeReal{}});
}

TEST(InferType, Var_Found) {
    TypeEnv env{{"x", TypeNode{TypeNat{}}}};
    EXPECT_EQ(*infer_type(evar("x"), env), TypeNode{TypeNat{}});
}

TEST(InferType, Var_NotFound) {
    EXPECT_FALSE(infer_type(evar("x"), {}).has_value());
}

TEST(InferType, Binary_NatPlusNat_IsNat) {
    auto e = ebin(BinOp::Add, elit("1"), elit("2"));
    EXPECT_EQ(*infer_type(e, {}), TypeNode{TypeNat{}});
}

TEST(InferType, Binary_RealPlusNat_PromotesToReal) {
    auto e = ebin(BinOp::Add, elit("1.0"), elit("2"));
    EXPECT_EQ(*infer_type(e, {}), TypeNode{TypeReal{}});
}

TEST(InferType, Binary_NatTimesReal_PromotesToReal) {
    auto e = ebin(BinOp::Mul, elit("3"), elit("2.5"));
    EXPECT_EQ(*infer_type(e, {}), TypeNode{TypeReal{}});
}

TEST(InferType, Binary_PropOperandIsError) {
    // A variable of type Prop cannot be added to a Nat
    TypeEnv env{{"P", TypeNode{TypeProp{}}}};
    auto e = ebin(BinOp::Add, evar("P"), elit("1"));
    EXPECT_FALSE(infer_type(e, env).has_value());
}

TEST(InferType, Unary_Neg_PropagatesType) {
    TypeEnv env{{"x", TypeNode{TypeReal{}}}};
    EXPECT_EQ(*infer_type(eunary(evar("x")), env), TypeNode{TypeReal{}});
}

TEST(InferType, Abs_PropagatesType) {
    TypeEnv env{{"x", TypeNode{TypeInt{}}}};
    EXPECT_EQ(*infer_type(eabs(evar("x")), env), TypeNode{TypeInt{}});
}

TEST(InferType, Lambda_WithAnnotation_ReturnsFunType) {
    // fun x : Nat => x + 1  — body type is Nat (Nat+Nat), result is Nat->Nat
    auto body = ebin(BinOp::Add, evar("x"), elit("1"));
    auto e = elambda_typed("x", TypeNode{TypeNat{}}, std::move(body));
    auto result = infer_type(e, {});
    ASSERT_TRUE(result.has_value());
    const auto* tf = std::get_if<TypeFun>(&result->node);
    ASSERT_NE(tf, nullptr);
    EXPECT_EQ(*tf->domain, TypeNode{TypeNat{}});
    EXPECT_EQ(*tf->codomain, TypeNode{TypeNat{}});
}

TEST(InferType, Lambda_NoAnnotation_IsError) {
    auto e = elambda("x", evar("x")); // uses helper without type annotation
    EXPECT_FALSE(infer_type(e, {}).has_value());
}

TEST(InferType, Agg_WithAnnotation_PropagatesBodyType) {
    // sum i : Nat, i  — body is Nat (from env), result is Nat
    auto e = Expr{diag::SourceLocation{},
                  ExprAgg{AggOp::Sum, "i", TypeNode{TypeNat{}},
                          std::nullopt, std::nullopt, make_expr(evar("i"))}};
    EXPECT_EQ(*infer_type(e, {}), TypeNode{TypeNat{}});
}

TEST(InferType, Conditional_SameTypes) {
    // if P then 1 else 2  — both Nat
    EXPECT_EQ(*infer_type(eif(elit("1"), elit("2")), {}), TypeNode{TypeNat{}});
}

TEST(InferType, Conditional_PromotesNatToReal) {
    // if P then 1 else 2.0  — Nat + Real → Real
    EXPECT_EQ(*infer_type(eif(elit("1"), elit("2.0")), {}), TypeNode{TypeReal{}});
}

// ── infer_type with FuncSigTable ──────────────────────────────────────────────

TEST(InferType, ExprCall_NoSigTable_IsError) {
    // f(x) with empty sig table → Unknown error
    auto e = Expr{diag::SourceLocation{}, ExprCall{"f", {make_expr(evar("x"))}}};
    auto r = infer_type(e, {});
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error().kind, TypeErrorKind::Unknown);
}

TEST(InferType, ExprCall_MatchingSig_ReturnsCodeomain) {
    // f : Nat -> Prop, f(n) with n:Nat → TypeProp
    auto sig = TypeFun{std::make_shared<TypeNode>(TypeNode{TypeNat{}}),
                       std::make_shared<TypeNode>(TypeNode{TypeProp{}})};
    FuncSigTable sigs{{"f", sig}};
    TypeEnv env{{"n", TypeNode{TypeNat{}}}};
    auto e = Expr{diag::SourceLocation{}, ExprCall{"f", {make_expr(evar("n"))}}};
    EXPECT_EQ(*infer_type(e, env, sigs), TypeNode{TypeProp{}});
}

TEST(InferType, ExprCall_ArgTypeMismatch_IsMismatch) {
    // f : Nat -> Prop, f(P) with P:Prop → Mismatch (expected Nat, got Prop)
    auto sig = TypeFun{std::make_shared<TypeNode>(TypeNode{TypeNat{}}),
                       std::make_shared<TypeNode>(TypeNode{TypeProp{}})};
    FuncSigTable sigs{{"f", sig}};
    TypeEnv env{{"P", TypeNode{TypeProp{}}}};
    auto e = Expr{diag::SourceLocation{}, ExprCall{"f", {make_expr(evar("P"))}}};
    auto r = infer_type(e, env, sigs);
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error().kind, TypeErrorKind::Mismatch);
}

TEST(InferType, ExprCall_TwoParamSig_BothMatch) {
    // g : Nat -> Real -> Prop, g(n, x) with n:Nat, x:Real → TypeProp
    auto inner = TypeFun{std::make_shared<TypeNode>(TypeNode{TypeReal{}}),
                         std::make_shared<TypeNode>(TypeNode{TypeProp{}})};
    auto outer = TypeFun{std::make_shared<TypeNode>(TypeNode{TypeNat{}}),
                         std::make_shared<TypeNode>(TypeNode{std::move(inner)})};
    FuncSigTable sigs{{"g", outer}};
    TypeEnv env{{"n", TypeNode{TypeNat{}}}, {"x", TypeNode{TypeReal{}}}};
    auto e = Expr{diag::SourceLocation{},
                  ExprCall{"g", {make_expr(evar("n")), make_expr(evar("x"))}}};
    EXPECT_EQ(*infer_type(e, env, sigs), TypeNode{TypeProp{}});
}

// ── TypeSet equality ──────────────────────────────────────────────────────────

TEST(TypeSetEquality, SameElementType) {
    EXPECT_EQ(type_set(type_nat()), type_set(type_nat()));
}

TEST(TypeSetEquality, DifferentElementType) {
    EXPECT_NE(type_set(type_nat()), type_set(type_real()));
}

TEST(TypeSetEquality, Nested) {
    EXPECT_EQ(type_set(type_set(type_nat())), type_set(type_set(type_nat())));
    EXPECT_NE(type_set(type_set(type_nat())), type_set(type_nat()));
}

// ── infer_type: set literals ──────────────────────────────────────────────────

TEST(InferType, SetLit_SingleNat_ReturnsSetNat) {
    // {42} → Set Nat
    auto e = Expr{diag::SourceLocation{},
                  ExprSetLit{{make_expr(elit("42"))}}};
    EXPECT_EQ(*infer_type(e, {}), type_set(type_nat()));
}

TEST(InferType, SetLit_MultiElement_Promotes) {
    // {1, 2.0} → Set Real  (Nat promoted to Real)
    auto e = Expr{diag::SourceLocation{},
                  ExprSetLit{{make_expr(elit("1")), make_expr(elit("2.0"))}}};
    EXPECT_EQ(*infer_type(e, {}), type_set(type_real()));
}

TEST(InferType, SetLit_Empty_ReturnsUnknown) {
    // {} — cannot infer element type
    auto e = Expr{diag::SourceLocation{}, ExprSetLit{{}}};
    auto r = infer_type(e, {});
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error().kind, TypeErrorKind::Unknown);
}

// ── infer_type: set comprehension ────────────────────────────────────────────

TEST(InferType, SetCompr_WithType_ReturnsSet) {
    // {x : Nat | P} → Set Nat
    auto pred = make_prop(atom("P"));
    auto e = Expr{diag::SourceLocation{}, ExprSetCompr{"x", type_nat(), std::move(pred)}};
    EXPECT_EQ(*infer_type(e, {}), type_set(type_nat()));
}

TEST(InferType, SetCompr_NoType_ReturnsUnknown) {
    // {x | P} — no type annotation → Unknown
    auto pred = make_prop(atom("P"));
    auto e = Expr{diag::SourceLocation{}, ExprSetCompr{"x", std::nullopt, std::move(pred)}};
    auto r = infer_type(e, {});
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error().kind, TypeErrorKind::Unknown);
}

// ── infer_type: set binary operations ────────────────────────────────────────

TEST(InferType, Union_SameElementType_ReturnsSet) {
    // A ∪ B where A:Set Nat, B:Set Nat → Set Nat
    TypeEnv env{{"A", type_set(type_nat())}, {"B", type_set(type_nat())}};
    auto e = ebin(BinOp::Union, evar("A"), evar("B"));
    EXPECT_EQ(*infer_type(e, env), type_set(type_nat()));
}

TEST(InferType, Union_DifferentElementTypes_IsMismatch) {
    // A ∪ B where A:Set Nat, B:Set Real → Mismatch
    TypeEnv env{{"A", type_set(type_nat())}, {"B", type_set(type_real())}};
    auto e = ebin(BinOp::Union, evar("A"), evar("B"));
    auto r = infer_type(e, env);
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error().kind, TypeErrorKind::Mismatch);
}

TEST(InferType, Union_NonSetOperand_IsMismatch) {
    // n ∪ m where n:Nat, m:Nat — not sets → Mismatch
    TypeEnv env{{"n", type_nat()}, {"m", type_nat()}};
    auto e = ebin(BinOp::Union, evar("n"), evar("m"));
    auto r = infer_type(e, env);
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error().kind, TypeErrorKind::Mismatch);
}

TEST(InferType, Inter_SameElementType_ReturnsSet) {
    // A ∩ B where A:Set Real, B:Set Real → Set Real
    TypeEnv env{{"A", type_set(type_real())}, {"B", type_set(type_real())}};
    auto e = ebin(BinOp::Inter, evar("A"), evar("B"));
    EXPECT_EQ(*infer_type(e, env), type_set(type_real()));
}

// ── infer_type: ExprAbs — absolute value vs cardinality ──────────────────────

TEST(InferType, ExprAbs_SetOperand_ReturnsNat) {
    // |S| where S:Set Nat → Nat (cardinality)
    TypeEnv env{{"S", type_set(type_nat())}};
    auto e = Expr{diag::SourceLocation{}, ExprAbs{make_expr(evar("S"))}};
    EXPECT_EQ(*infer_type(e, env), type_nat());
}

TEST(InferType, ExprAbs_NumericOperand_Propagates) {
    // |x| where x:Real → Real (absolute value)
    TypeEnv env{{"x", type_real()}};
    auto e = Expr{diag::SourceLocation{}, ExprAbs{make_expr(evar("x"))}};
    EXPECT_EQ(*infer_type(e, env), type_real());
}

// ── beta_reduce tests ─────────────────────────────────────────────────────────

// Helper: build ExprApp{func, args}
static Expr eapp(Expr func, std::vector<Expr> args) {
    std::vector<ExprPtr> ptrs;
    ptrs.reserve(args.size());
    for (auto& a : args) ptrs.push_back(make_expr(std::move(a)));
    return {diag::SourceLocation{}, ExprApp{make_expr(std::move(func)), std::move(ptrs)}};
}

// Helper: build ExprCall{name, args}
static Expr ecall(std::string name, std::vector<Expr> args) {
    std::vector<ExprPtr> ptrs;
    ptrs.reserve(args.size());
    for (auto& a : args) ptrs.push_back(make_expr(std::move(a)));
    return {diag::SourceLocation{}, ExprCall{std::move(name), std::move(ptrs)}};
}

TEST(BetaReduce, AlreadyNormal_Lit) {
    // A literal has no redexes.
    EXPECT_EQ(beta_reduce(elit("42")), elit("42"));
}

TEST(BetaReduce, AlreadyNormal_Var) {
    EXPECT_EQ(beta_reduce(evar("x")), evar("x"));
}

TEST(BetaReduce, IdentityApp_ReducesToArg) {
    // ExprApp{fun x => x, [42]}  →  42
    Expr redex = eapp(elambda("x", evar("x")), {elit("42")});
    EXPECT_EQ(beta_reduce(redex), elit("42"));
}

TEST(BetaReduce, ConstantApp_ReducesToConstant) {
    // ExprApp{fun x => 1, [42]}  →  1
    Expr redex = eapp(elambda("x", elit("1")), {elit("42")});
    EXPECT_EQ(beta_reduce(redex), elit("1"));
}

TEST(BetaReduce, AddOneApp_SubstitutesArg) {
    // ExprApp{fun x => x + 1, [5]}  →  5 + 1
    Expr lam = elambda("x", ebin(BinOp::Add, evar("x"), elit("1")));
    Expr redex = eapp(lam, {elit("5")});
    Expr expected = ebin(BinOp::Add, elit("5"), elit("1"));
    EXPECT_EQ(beta_reduce(redex), expected);
}

TEST(BetaReduce, CurriedApp_TwoArgs) {
    // ExprApp{fun x => fun y => x + y, [3, 4]}
    // After first reduction: ExprApp{fun y => 3 + y, [4]}
    // After second reduction: 3 + 4
    Expr inner_lam = elambda("y", ebin(BinOp::Add, evar("x"), evar("y")));
    Expr outer_lam = elambda("x", inner_lam);
    Expr redex = eapp(outer_lam, {elit("3"), elit("4")});
    Expr expected = ebin(BinOp::Add, elit("3"), elit("4"));
    EXPECT_EQ(beta_reduce(redex), expected);
}

TEST(BetaReduce, NoRedex_ExprApp_NonLambdaFunc) {
    // ExprApp{x, [42]} where x is a plain variable — collapse to ExprCall{"x",[42]}.
    // This normalisation ensures ForallElim witnesses of function type produce the
    // canonical ExprCall form rather than a stuck ExprApp.
    Expr app = eapp(evar("x"), {elit("42")});
    Expr reduced = beta_reduce(app);
    const auto* c = std::get_if<ExprCall>(&reduced.node);
    ASSERT_NE(c, nullptr);
    EXPECT_EQ(c->name, "x");
    ASSERT_EQ(c->args.size(), 1u);
    EXPECT_EQ(*c->args[0], elit("42"));
}

TEST(BetaReduce, NestedRedex_ReducesBoth) {
    // ExprApp{fun x => ExprApp{fun y => y, [x]}, [5]}
    // Step 1: substitute x=5: ExprApp{fun y => y, [5]}
    // Step 2: substitute y=5: 5
    Expr inner_redex = eapp(elambda("y", evar("y")), {evar("x")});
    Expr outer_lam   = elambda("x", inner_redex);
    Expr full_redex  = eapp(outer_lam, {elit("5")});
    EXPECT_EQ(beta_reduce(full_redex), elit("5"));
}

// TR1 via subst: when subst replaces a function-position variable with a lambda,
// the resulting ExprApp is a beta-redex that beta_reduce collapses.
TEST(BetaReduce, SubstCreatesExprApp_ThenReduces) {
    // Expr: f(3)  →  ExprCall{"f", [3]}
    // Replacement for "f": fun x => x + 1
    // subst_expr produces ExprApp{fun x => x + 1, [3]}
    // beta_reduce collapses it to 3 + 1
    Expr call_f3 = ecall("f", {elit("3")});
    Expr lam = elambda("x", ebin(BinOp::Add, evar("x"), elit("1")));
    Expr after_subst = subst(call_f3, "f", lam);
    // After subst, the node should be ExprApp (lambda applied to [3])
    ASSERT_TRUE(std::holds_alternative<ExprApp>(after_subst.node));
    Expr reduced = beta_reduce(after_subst);
    Expr expected = ebin(BinOp::Add, elit("3"), elit("1"));
    EXPECT_EQ(reduced, expected);
}

// ── beta_reduce(Prop) tests ───────────────────────────────────────────────────

TEST(BetaReduceProp, PropRelReducesExprs) {
    // PropRel: ExprApp{fun x => x + 1, [3]} > 0
    // After beta_reduce(Prop): (3 + 1) > 0
    Expr lam = elambda("x", ebin(BinOp::Add, evar("x"), elit("1")));
    Expr redex = eapp(lam, {elit("3")});
    Prop p = prel(redex, RelOp::Gt, elit("0"));
    Prop reduced = beta_reduce(p);
    const auto* rel = std::get_if<PropRel>(&reduced.node);
    ASSERT_NE(rel, nullptr);
    Expr expected_lhs = ebin(BinOp::Add, elit("3"), elit("1"));
    EXPECT_EQ(*rel->lhs, expected_lhs);
}

TEST(BetaReduceProp, AtomUnchanged) {
    Prop p{{}, Atomic{"P"}};
    EXPECT_EQ(beta_reduce(p), p);
}

// ── eta_reduce tests ──────────────────────────────────────────────────────────

TEST(EtaReduce, AlreadyNormal_NoEta) {
    // fun x => x + 1  — body is not a call ending in x; no eta
    Expr e = elambda("x", ebin(BinOp::Add, evar("x"), elit("1")));
    EXPECT_EQ(eta_reduce(e), e);
}

TEST(EtaReduce, SingleArgCall_Reduces) {
    // fun x => f(x)  where f is a distinct name  →  ExprVar{"f"}
    Expr e = elambda("x", ecall("f", {evar("x")}));
    Expr reduced = eta_reduce(e);
    const auto* v = std::get_if<ExprVar>(&reduced.node);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(v->name, "f");
}

TEST(EtaReduce, MultiArgCall_DropsLastArg) {
    // fun x => g(a, x)  →  g(a)  (provided x not free in g(a))
    Expr e = elambda("x", ecall("g", {evar("a"), evar("x")}));
    Expr reduced = eta_reduce(e);
    const auto* call = std::get_if<ExprCall>(&reduced.node);
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->name, "g");
    ASSERT_EQ(call->args.size(), 1u);
    EXPECT_EQ(*call->args[0], evar("a"));
}

TEST(EtaReduce, NoEta_LastArgNotVar) {
    // fun x => f(1)  — last arg is not ExprVar{x}; no eta
    Expr e = elambda("x", ecall("f", {elit("1")}));
    Expr reduced = eta_reduce(e);
    // Should still be a lambda
    EXPECT_TRUE(std::holds_alternative<ExprLambda>(reduced.node));
}

TEST(EtaReduce, NoEta_XFreeInRemainingArgs) {
    // fun x => g(x, x)  — last arg is ExprVar{x} but x is also free in g(x)
    Expr e = elambda("x", ecall("g", {evar("x"), evar("x")}));
    Expr reduced = eta_reduce(e);
    // Cannot eta-reduce because x is free in g(x)
    EXPECT_TRUE(std::holds_alternative<ExprLambda>(reduced.node));
}

// ── defn_eq tests ─────────────────────────────────────────────────────────────

TEST(DefnEq, StructurallyEqual_IsTrue) {
    EXPECT_TRUE(defn_eq(evar("x"), evar("x")));
    EXPECT_TRUE(defn_eq(elit("42"), elit("42")));
}

TEST(DefnEq, StructurallyUnequal_IsFalse) {
    EXPECT_FALSE(defn_eq(evar("x"), evar("y")));
}

TEST(DefnEq, BetaRedexEqualsReducedForm) {
    // ExprApp{fun x => x + 1, [3]}  defn_eq  3 + 1
    Expr redex = eapp(elambda("x", ebin(BinOp::Add, evar("x"), elit("1"))), {elit("3")});
    Expr normal = ebin(BinOp::Add, elit("3"), elit("1"));
    EXPECT_TRUE(defn_eq(redex, normal));
}

TEST(DefnEq, EtaExpandedEqualsOriginal) {
    // fun x => f(x)  defn_eq  ExprVar{"f"}
    Expr eta_expanded = elambda("x", ecall("f", {evar("x")}));
    Expr original = evar("f");
    EXPECT_TRUE(defn_eq(eta_expanded, original));
}

TEST(DefnEq, PropDefnEq_Atomic) {
    Prop p{{}, Atomic{"P"}};
    EXPECT_TRUE(defn_eq(p, p));
}

TEST(DefnEq, PropDefnEq_BetaInRel) {
    // PropRel with beta-redex on lhs vs. already-reduced form
    Expr redex = eapp(elambda("x", ebin(BinOp::Add, evar("x"), elit("1"))), {elit("3")});
    Expr normal = ebin(BinOp::Add, elit("3"), elit("1"));
    Prop p_redex = prel(redex,  RelOp::Gt, elit("0"));
    Prop p_normal = prel(normal, RelOp::Gt, elit("0"));
    EXPECT_TRUE(defn_eq(p_redex, p_normal));
}
