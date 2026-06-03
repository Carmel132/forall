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

// Set type  Set T  — the type whose values are sets with element type T.
// Written "Set Nat", "Set Real", etc.  operator== defined in node.cpp.
struct TypeSet {
    std::shared_ptr<TypeNode> element_type;
    bool operator==(const TypeSet& o) const;
};

// Dependent function type  (x : A) → B(x).
// When B does not mention x this is just A → B (ordinary function type).
// Uses shared_ptr to handle the incomplete TypeNode at declaration time.
// operator== defined in node.cpp.
struct TypePi {
    std::string               var;      // bound variable name
    std::shared_ptr<TypeNode> domain;   // type of the variable
    std::shared_ptr<TypeNode> codomain; // return type, may mention var
    bool operator==(const TypePi& o) const;
};

using TypeVariant = std::variant<TypeNat, TypeInt, TypeRat, TypeReal, TypeProp, TypeUser,
                                 TypeFun, TypeTuple, TypeSet, TypePi>;

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
inline TypeNode type_set(TypeNode elem) {
    return TypeNode{TypeSet{std::make_shared<TypeNode>(std::move(elem))}};
}
inline TypeNode type_pi(std::string var, TypeNode domain, TypeNode codomain) {
    return TypeNode{TypePi{std::move(var),
                           std::make_shared<TypeNode>(std::move(domain)),
                           std::make_shared<TypeNode>(std::move(codomain))}};
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

// ExprApp represents application of an arbitrary expression (typically a
// lambda) to a list of arguments.  This arises after substitution replaces a
// function-position variable with an ExprLambda: subst_expr converts
// ExprCall{name, args} where name == var and the replacement is a lambda into
// ExprApp{lambda, substituted_args}.  beta_reduce then collapses these redexes.
struct ExprApp {                                                     // e(arg1, arg2, ...)
    ExprPtr              func;
    std::vector<ExprPtr> args;
};

// Field projection: base.field_name — e.g. g.mul, g.carrier
struct ExprField {
    ExprPtr     base;
    std::string field_name;
};

using ExprNode = std::variant<
    ExprLit, ExprVar, ExprBinary, ExprUnary, ExprAbs, ExprCall,
    ExprIndex, ExprTuple, ExprLambda, ExprIf, ExprAgg,
    ExprSetLit, ExprSetCompr, ExprApp, ExprField
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
struct PropTrue  {};                           // ⊤
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
    Atomic, PropFalse, PropTrue,
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
    std::string             var;
    std::optional<TypeNode> type;       // e.g. TypeProp for "let P be a Prop"
    std::optional<ExprPtr>  definition; // e.g. ExprBinary{/} for "let delta = eps / 2"
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

// induction <name> on <var> : <body>
//   base:       <steps...>    -- must conclude subst(body, var, 0)
//   inductive:  <steps...>    -- has ih : body in scope; must conclude subst(body, var, succ(var))
//
// Proves ∀ var : Nat, body.  The checker:
//   1. verifies the base block concludes body[var:=0]
//   2. injects ih : body as an assumption and verifies the inductive block
//      concludes body[var:=succ(var)]
//   3. applies NatInduction to certify ∀ var : Nat, body
// The result is stored under `name` in the enclosing scope.
struct InductionStep {
    std::string                        name;            // label for the result in scope
    std::string                        var;             // induction variable
    Prop                               body;            // P(var) — the inductive predicate
    std::vector<std::unique_ptr<Step>> base_steps;      // proves P(0)
    std::vector<std::unique_ptr<Step>> inductive_steps; // proves P(succ(var)) using ih : P(var)
};

struct ShowStep {
    Prop prop;  // asserted goal; checker verifies prop == decl.statement
};

struct ExactStep {
    std::string hyp_ref;  // hypothesis name whose prop must equal the current goal
};

struct RewriteStep {
    std::string hyp_ref;  // hypothesis name; must be PropRel{Eq}
    bool        reverse;  // if true, rewrite rhs→lhs instead of lhs→rhs
};

struct ApplyStep {
    std::string hyp_ref;  // hypothesis name; must be PropImpl{A, B} where B == current goal
};

// ── calc block (NL1) ───────────────────────────────────────────────────────────
//
// calc
//   a ≤ b   by h1
//     = c   by h2
//     < d   by h3
//
// Each link is one relation step.  The checker verifies each step individually,
// then assembles the transitive conclusion (a ≤ d here) and stores it.

struct CalcLink {
    RelOp                      op;            // the relational operator for this link
    ExprPtr                    rhs;           // right-hand side of this link
    std::vector<std::string>   justification; // refs after "by"
};

struct CalcStep {
    std::string              name;   // result label (empty → fresh name)
    ExprPtr                  lhs;    // LHS of the first link
    std::vector<CalcLink>    links;  // at least 1 link
};

// ── split block (NL2) ─────────────────────────────────────────────────────────
//
// split [name :]
//   case left  => <steps...> then P
//   case right => <steps...> then Q
//
// Decomposes a conjunction goal P ∧ Q into two sub-proofs.
// For biconditionals (desugared to (P→Q) ∧ (Q→P)):
//   case (->) => ... then P → Q
//   case (<-) => ... then Q → P
// Combines the two judgments with AndIntro.
// The result is stored under `name` (or a fresh label if name is empty).

struct SplitArm {
    std::string                        label; // "left", "right", "(->)", "(<-)", etc.
    std::vector<std::unique_ptr<Step>> steps;
};

struct SplitStep {
    std::string              name;  // optional result label (empty → fresh)
    std::vector<SplitArm>    arms;
};

using StepNode = std::variant<
    LetStep, TakeStep, SupposeStep, HaveStep, ThenStep, ContradictionStep,
    CasesStep, ObtainStep, InductionStep, ShowStep, ExactStep, RewriteStep, ApplyStep,
    CalcStep, SplitStep
>;

struct Step {
    diag::SourceLocation loc;
    StepNode             node;
};

struct ProofBlock {
    std::vector<Step> steps;
};

// ── Structure fields ───────────────────────────────────────────────────────────

// A term field in a structure: e.g. "carrier : Type" or "mul : carrier -> carrier -> carrier"
struct FieldTerm {
    std::string name;
    TypeNode    type;
    bool operator==(const FieldTerm&) const = default;
};

// A bundled axiom field in a structure: e.g. "axiom mul_assoc : ∀ a b c : carrier, ..."
struct FieldAxiom {
    std::string name;
    Prop        prop;
    bool operator==(const FieldAxiom& o) const;
};

using StructField = std::variant<FieldTerm, FieldAxiom>;

// ── Top-level declarations ─────────────────────────────────────────────────────

enum class DeclKind { Axiom, Definition, Lemma, Theorem, Import, Instance, Structure, Quotient };

// A single named parameter of a definition, e.g. (x : Nat).
struct Param {
    std::string name;
    TypeNode    type;
    bool operator==(const Param&) const = default;
};

struct Decl {
    DeclKind                  kind;
    std::string               name;           // for Import: file path; for Instance: type name
    diag::SourceLocation      loc;
    Prop                      statement;      // for Import/Instance/Structure/Instantiation: dummy PropFalse{}
    std::optional<ProofBlock> proof;          // absent for Axiom / Import / Instance / Structure
    std::vector<Param>        params;         // definition parameters; empty for others
    std::string               instance_class; // for Instance: the class name (e.g. "Ring")
    std::vector<StructField>  fields;         // for Structure: term fields and axiom fields
    // For DeclKind::Definition used as a structure instantiation:
    std::string                          struct_type;     // the structure being instantiated
    std::map<std::string, ExprPtr>       struct_bindings; // field_name → value expression
    // For DeclKind::Quotient:
    std::string                          quot_carrier;    // carrier type name (e.g. "Int")
    std::string                          quot_rel;        // equivalence relation name (e.g. "int_eq")
};

// Maps structure name → its field list.  Used by the checker to process
// structure instantiations (DT3).
using StructEnv = std::map<std::string, std::vector<StructField>>;

using DeclPtr = std::unique_ptr<Decl>;

// ── Module ─────────────────────────────────────────────────────────────────────

struct Module {
    std::string          path;
    std::vector<DeclPtr> decls;
};

// ── Type environment and inference ────────────────────────────────────────────

// Maps term variable names to their annotated types (from binders / takes / lets).
using TypeEnv = std::map<std::string, TypeNode>;

// Maps function names to their curried type signatures.
// Seeded from `definition f (x : T₁) (y : T₂) : P` declarations as
// TypeFun{T₁, TypeFun{T₂, Prop}}.  Used by infer_type for ExprCall nodes.
using FuncSigTable = std::map<std::string, TypeFun>;

// Category for infer_type failures.  Mismatch indicates two concrete,
// incompatible types (e.g. Prop in arithmetic); Unknown means the type
// could not be determined from available annotations.
enum class TypeErrorKind { Unknown, Mismatch };

// Carry-type for infer_type failures.
struct TypeError {
    std::string   message;
    TypeErrorKind kind{TypeErrorKind::Unknown};
};

// Infers the type of an expression given a type environment and an optional
// function signature table.  Returns TypeError when the type cannot be
// determined: unknown variable, arithmetic mismatch, unsupported expression
// form (sets, tuples — deferred), or ExprCall without a matching signature.
[[nodiscard]] std::expected<TypeNode, TypeError>
infer_type(const Expr& e, const TypeEnv& env, const FuncSigTable& sigs = {},
           const StructEnv* struct_env = nullptr);

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

// ── Beta-reduction ────────────────────────────────────────────────────────────
//
// Reduces ExprApp{ExprLambda{x,_,body}, [arg, ...]} → subst(body, x, arg)
// and then reduces any further ExprApp nodes that may appear after substitution.
// Also collapses ExprCall{name, args} where name is the bound variable of a
// surrounding lambda (handled via subst_expr producing ExprApp) — see note in
// subst_expr below.
// Recurses into all subexpressions; all other ExprNode variants are reconstructed.
//
// beta_reduce(Prop) recurses into all PropNode variants that contain ExprPtr
// fields (PropRel, PropPred) and sub-props (PropNot/And/Or/Impl/Forall/Exists).
[[nodiscard]] Expr beta_reduce(const Expr& e);
[[nodiscard]] Prop beta_reduce(const Prop& p);

// ── Eta-reduction ─────────────────────────────────────────────────────────────
//
// Reduces ExprLambda{x, t, ExprCall{name, args}} where the last arg is
// ExprVar{x} and x does not appear free in ExprCall{name, args_without_last}
// → ExprCall{name, args_without_last}  (or ExprVar{name} if no args remain).
// Recurses into subexpressions after reducing the outermost lambda.
[[nodiscard]] Expr eta_reduce(const Expr& e);

// ── Definitional equality ─────────────────────────────────────────────────────
//
// Two expressions/propositions are definitionally equal if they are structurally
// equal after beta- and eta-reduction.  Used by the kernel to compare props that
// may differ by a beta-redex introduced through ForallElim/ExistsIntro witnesses.
[[nodiscard]] bool defn_eq(const Expr& a, const Expr& b);
[[nodiscard]] bool defn_eq(const Prop& a, const Prop& b);

} // namespace forall::ast
