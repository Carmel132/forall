#pragma once
#include <forall/diagnostics/source_location.hpp>

#include <expected>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <variant>
#include <vector>

namespace forall::ast {

// ── Types ──────────────────────────────────────────────────────────────────────
//
// Ground types: Nat Int Rat Real Prop; user types via TypeUser.
// Recursive types: TypeFun{domain→codomain} and TypeTuple{T1,T2,...}.
//
// Recognised keywords: Nat Int Rat Real Prop; everything else → TypeUser{name}.

struct TypeNode; // forward declaration — needed by TypeFun and TypeTuple

struct TypeNat  { bool operator==(const TypeNat&)  const = default; };  // ℕ
struct TypeInt  { bool operator==(const TypeInt&)  const = default; };  // ℤ
struct TypeRat  { bool operator==(const TypeRat&)  const = default; };  // ℚ
struct TypeReal { bool operator==(const TypeReal&) const = default; };  // ℝ
struct TypeProp { bool operator==(const TypeProp&) const = default; };  // Prop
struct TypeUser {
    std::string name;
    bool operator==(const TypeUser&) const = default;
};

// Function type T₁ → T₂; right-associative. Uses shared_ptr to handle the
// incomplete TypeNode at declaration time. operator== defined in node.cpp.
struct TypeFun {
    std::shared_ptr<TypeNode> domain;
    std::shared_ptr<TypeNode> codomain;
    bool operator==(const TypeFun& o) const;
};

// Product / tuple type (T₁, T₂, …). operator== defined in node.cpp.
struct TypeTuple {
    std::vector<std::shared_ptr<TypeNode>> elements;
    bool operator==(const TypeTuple& o) const;
};

using TypeVariant = std::variant<TypeNat, TypeInt, TypeRat, TypeReal, TypeProp, TypeUser,
                                 TypeFun, TypeTuple>;

struct TypeNode {
    TypeVariant node;
    bool operator==(const TypeNode& o) const; // defined in node.cpp (needs complete TypeFun/Tuple)
};

// Convenience constructors used in tests and the parser.
inline TypeNode type_nat()                   { return TypeNode{TypeNat{}}; }
inline TypeNode type_int()                   { return TypeNode{TypeInt{}}; }
inline TypeNode type_rat()                   { return TypeNode{TypeRat{}}; }
inline TypeNode type_real()                  { return TypeNode{TypeReal{}}; }
inline TypeNode type_prop()                  { return TypeNode{TypeProp{}}; }
inline TypeNode type_user(std::string name)  { return TypeNode{TypeUser{std::move(name)}}; }
inline TypeNode type_fun(TypeNode domain, TypeNode codomain) {
    return TypeNode{TypeFun{std::make_shared<TypeNode>(std::move(domain)),
                            std::make_shared<TypeNode>(std::move(codomain))}};
}
inline TypeNode type_tuple(std::vector<TypeNode> elems) {
    TypeTuple tt;
    for (auto& e : elems)
        tt.elements.push_back(std::make_shared<TypeNode>(std::move(e)));
    return TypeNode{std::move(tt)};
}

// ── Forward declarations ───────────────────────────────────────────────────────
struct Prop;
using PropPtr = std::shared_ptr<Prop>;

struct Expr;
using ExprPtr = std::shared_ptr<Expr>;

struct Step; // forward-declared so CasesStep can hold std::unique_ptr<Step>

// ── Expressions ───────────────────────────────────────────────────────────────
//
// Term-level arithmetic expressions, separate from Prop.
// They enter the proposition layer via PropRel and PropPred.

enum class BinOp { Add, Sub, Mul, Div, IDiv, Mod, Pow, Compose, Union, Inter, SetMinus };
//                  +    -    *    /   div  mod   ^      ∘      ∪     ∩       ∖

enum class UnaryOp { Neg }; // unary minus; absolute value is its own ExprAbs node

// RelOp lives here (before ExprAgg which uses it) and is also used by PropRel.
enum class RelOp { Lt, Gt, LtEq, GtEq, Eq, NotEq, In, NotIn, SubsetEq, Subset, SupersetEq };
//                  <   >   <=    >=    =   /=    ∈    ∉      ⊆        ⊂        ⊇

enum class AggOp { Sum, Prod };

struct ExprLit    { std::string value;  };                          // 42, 3.14
struct ExprVar    { std::string name;   };                          // x, n, eps
struct ExprBinary { BinOp op; ExprPtr lhs, rhs; };                 // a + b
struct ExprUnary  { UnaryOp op; ExprPtr operand; };                 // -x
struct ExprAbs    { ExprPtr operand; };                              // |x|
struct ExprCall   { std::string name; std::vector<ExprPtr> args; }; // f(x, y)
struct ExprIndex  { ExprPtr array; ExprPtr index; };                // a[n]
struct ExprTuple  { std::vector<ExprPtr> elements; };               // (a, b, c)

struct ExprSetLit  { std::vector<ExprPtr> elements; };               // {a, b, c}  or  {}

struct ExprSetCompr {                                                // {x [: T] | P}
    std::string              var;
    std::optional<TypeNode> type;
    PropPtr                  pred;
};

struct ExprLambda {                                                  // fun x [: T] => body  /  λ x, body
    std::string              var;
    std::optional<TypeNode> type;
    ExprPtr                  body;
};

struct ExprIf {                                                      // if P then a else b
    PropPtr cond;
    ExprPtr then_;
    ExprPtr else_;
};

struct ExprAgg {                                                     // sum/prod with binder
    AggOp                      op;
    std::string                var;
    std::optional<TypeNode> type;    // typed binder:   sum i : T, f i
    std::optional<RelOp>       rel;     // bounded binder: sum i < n, f i
    std::optional<ExprPtr>     bound;   // bound expression (bounded form only)
    ExprPtr                    body;
};

using ExprNode = std::variant<
    ExprLit, ExprVar, ExprBinary, ExprUnary, ExprAbs, ExprCall,
    ExprIndex, ExprTuple, ExprLambda, ExprIf, ExprAgg,
    ExprSetLit, ExprSetCompr
>;

struct Expr {
    diag::SourceLocation                loc;
    ExprNode                            node;
    std::optional<diag::SourceLocation> end_loc{}; // start of first token AFTER this expression
    bool operator==(const Expr&) const; // structural, ignores loc and end_loc
};

inline ExprPtr make_expr(Expr e) {
    return std::make_shared<Expr>(std::move(e));
}

// ── Propositions ───────────────────────────────────────────────────────────────
struct Atomic   { std::string name; };         // P, Q, excluded_middle, …
struct PropFalse {};                           // ⊥
struct PropNot  { PropPtr inner; };            // ¬P
struct PropAnd  { PropPtr lhs, rhs; };         // P ∧ Q
struct PropOr   { PropPtr lhs, rhs; };         // P ∨ Q
struct PropImpl   { PropPtr lhs, rhs; };       // P → Q
struct PropForall {                            // ∀ x [: T], P
    std::string              var;
    std::optional<TypeNode> type;
    PropPtr                  body;
};
struct PropExists {                            // ∃ x [: T], P
    std::string              var;
    std::optional<TypeNode> type;
    PropPtr                  body;
};

// ── Relational propositions (bridge between Expr and Prop) ────────────────────

// expr rel expr  —  e.g. n + 1 > 0,  |a - b| < eps,  x ^ 2 >= 0
struct PropRel {
    ExprPtr lhs, rhs;
    RelOp   op;
};

// identifier "(" arg_list ")"  as a proposition  —  e.g. isPrime(n), P(x)
// Checker stub: accepted as an opaque proposition; no proof rules yet.
struct PropPred {
    std::string          name;
    std::vector<ExprPtr> args;
};

using PropNode = std::variant<
    Atomic, PropFalse,
    PropNot, PropAnd, PropOr, PropImpl,
    PropForall, PropExists,
    PropRel, PropPred
>;

struct Prop {
    diag::SourceLocation                loc;
    PropNode                            node;
    std::optional<diag::SourceLocation> end_loc{}; // start of first token AFTER this proposition

    bool operator==(const Prop&) const;  // structural, ignores loc and end_loc
};

inline PropPtr make_prop(Prop p) {
    return std::make_shared<Prop>(std::move(p));
}

// ── Proof steps ────────────────────────────────────────────────────────────────

// A single arm of a 'cases' step.  Introduces arm.name : arm.prop as a local
// assumption and sub-checks the arm.steps, which must end with a 'then' step.
struct CaseArm {
    std::string                        name;
    Prop                               prop;
    std::vector<std::unique_ptr<Step>> steps; // unique_ptr for incomplete-type recursion
};

// cases <name> : <ref>
//   case <arm.name> : <arm.prop> => <arm.steps...>
//   case <arm.name> : <arm.prop> => <arm.steps...>
//
// Desugars to OrElim.  Must be the last step before 'end'/'qed' in the proof.
struct CasesStep {
    std::string          name;         // label under which the result is stored in env
    std::string          disjunct_ref; // ref to the P ∨ Q hypothesis
    std::vector<CaseArm> arms;
};

struct LetStep {
    std::string           var;
    std::optional<TypeNode> type; // e.g. TypeProp for "let P be a Prop"
};

// take x [: T] — introduces a fresh term variable for ∀-intro.
// The checker verifies x does not appear free in any undischarged assumption,
// records x as "taken", and allows ForallIntro for any ∀ x, P proven afterward.
struct TakeStep {
    std::string                var;
    std::optional<TypeNode> type; // optional type annotation
};

struct SupposeStep {
    bool                  for_contradiction{false};
    std::optional<std::string> name;  // the hypothesis label
    Prop                  prop;
};

struct HaveStep {
    std::string              name;
    Prop                     prop;
    std::vector<std::string> justification; // ref names after "by"
    std::optional<ExprPtr>   witness;       // term after "at" — for ForallElim / ExistsIntro
};

struct ThenStep {
    Prop                     prop;
    std::vector<std::string> justification;
    std::optional<ExprPtr>   witness;       // term after "at" — for ForallElim / ExistsIntro
};

struct ContradictionStep {
    std::vector<std::string> justification;
};

// obtain <name> from <ref>
//   case <var> [: <type>] , <hyp_name> : <hyp_prop> => <steps...> [ "done" ]
//
// Desugars to ExistsElim.  <ref> must be ∃ var, P; the checker verifies:
//   - <var> is fresh (not free in any undischarged assumption)
//   - <hyp_prop> == subst(∃-body, ∃-var, ExprVar{var})
//   - sub-proof concludes some Q where <var> ∉ free(Q)
// Without "done" it must be the last step; with "done" subsequent steps may follow.
struct ObtainStep {
    std::string                        name;       // label for the result in scope
    std::string                        exists_ref; // ref to the ∃ x, P hypothesis
    std::string                        var;        // fresh variable introduced
    std::optional<TypeNode>            type;       // optional type annotation for var
    std::string                        hyp_name;   // name for P(var) hypothesis
    Prop                               hyp_prop;   // stated proposition P(var)
    std::vector<std::unique_ptr<Step>> steps;
};

using StepNode = std::variant<
    LetStep, TakeStep, SupposeStep, HaveStep, ThenStep, ContradictionStep,
    CasesStep, ObtainStep
>;

struct Step {
    diag::SourceLocation loc;
    StepNode             node;
};

struct ProofBlock {
    std::vector<Step> steps;
};

// ── Top-level declarations ─────────────────────────────────────────────────────

enum class DeclKind { Axiom, Definition, Lemma, Theorem, Import };

// A single named parameter of a definition, e.g. (x : Nat).
struct Param {
    std::string name;
    TypeNode    type;
    bool operator==(const Param&) const = default;
};

struct Decl {
    DeclKind                  kind;
    std::string               name;       // for Import: the file path (quotes stripped)
    diag::SourceLocation      loc;
    Prop                      statement;  // for Import: dummy PropFalse{}
    std::optional<ProofBlock> proof;      // absent for Axiom / Import
    std::vector<Param>        params;     // definition parameters; empty for others
};

using DeclPtr = std::unique_ptr<Decl>;

// ── Module ─────────────────────────────────────────────────────────────────────

struct Module {
    std::string          path;
    std::vector<DeclPtr> decls;
};

// ── Type environment and inference ────────────────────────────────────────────

// Maps term variable names to their annotated types (from binders / takes / lets).
using TypeEnv = std::map<std::string, TypeNode>;

// Carry-type for infer_type failures.
struct TypeError {
    std::string message;
};

// Infers the type of an expression given a type environment.
// Returns TypeError when the type cannot be determined: unknown variable,
// arithmetic type mismatch, or expression form not yet handled (calls, sets,
// tuples — deferred until the signature table and Set-type exist).
[[nodiscard]] std::expected<TypeNode, TypeError>
infer_type(const Expr& e, const TypeEnv& env);

// ── Free-variable enumeration and syntactic substitution ─────────────────────

// Returns the set of all term variable names (ExprVar) that appear free.
// Propositional atoms and PropFalse carry no term variables.
// Binders (∀/∃/fun/sum/prod/{x|…}) exclude their variable within their scope.
std::set<std::string> free_vars(const Prop& prop);
std::set<std::string> free_vars(const Expr& expr);

// Returns a copy with every free occurrence of term variable `var` replaced by
// `replacement`.  Stops substituting inside any binder that shadows `var`.
//
// Note: capture-avoiding renaming is not performed.  Callers must ensure that
// free variables of `replacement` are not captured by inner binders of `prop`.
Prop subst(const Prop& prop, const std::string& var, const Expr& replacement);
Expr subst(const Expr& expr, const std::string& var, const Expr& replacement);

} // namespace forall::ast
