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
struct TypeType { bool operator==(const TypeType&) const = default; };  // Type (universe)
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

using TypeVariant = std::variant<TypeNat, TypeInt, TypeRat, TypeReal, TypeProp, TypeType, TypeUser,
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
inline TypeNode type_type()                  { return TypeNode{TypeType{}}; }
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
// Forward declaration so HaveStep can hold an optional sub-proof.
struct ProofBlock;

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
    std::vector<ExprPtr>     witnesses;     // terms after "at" — chained ForallElim / ExistsIntro
    std::unique_ptr<ProofBlock> sub_proof;  // present when "proof ... end" follows
};

struct ThenStep {
    Prop                     prop;
    std::vector<std::string> justification;
    std::vector<ExprPtr>     witnesses;     // terms after "at" — chained ForallElim / ExistsIntro
};

struct ContradictionStep {
    std::vector<std::string> justification;
};

// obtain <name> from <ref>
//   case <var> [: <type>] , <hyp_name> : <hyp_prop> [, <hyp_name2> : <hyp_prop2> ...] => <steps...> [ "done" ]
//
// Desugars to ExistsElim.  <ref> must be ∃ var, P; the checker verifies:
//   - <var> is fresh (not free in any undischarged assumption)
//   - hyp_bindings[0].second == subst(∃-body, ∃-var, ExprVar{var})
//   - extra bindings destructure conjuncts of the body via AndElimL/R
//   - sub-proof concludes some Q where <var> ∉ free(Q)
// Without "done" it must be the last step; with "done" subsequent steps may follow.
struct ObtainHypBinding {
    std::string name;
    Prop        prop;
};

struct ObtainStep {
    std::string                        name;         // label for the result in scope
    std::string                        exists_ref;   // ref to the ∃ x, P hypothesis
    std::string                        var;          // fresh variable introduced
    std::optional<TypeNode>            type;         // optional type annotation for var
    std::vector<ObtainHypBinding>      hyp_bindings; // ≥1 bindings; extras destructure conjuncts
    std::vector<std::unique_ptr<Step>> steps;
};

// One arm of a structural induction step (one constructor case).
struct InductionArm {
    std::string                        ctor_name;  // constructor name (e.g. "nil", "cons")
    std::vector<std::string>           vars;       // variables bound in this arm
    std::vector<std::string>           ih_names;   // IH names for recursive args (empty for base ctors)
    std::vector<std::unique_ptr<Step>> steps;      // must end with a ThenStep
};

// induction <name> on <var> : <body>
//   base:       <steps...>    -- must conclude subst(body, var, 0)    [Nat only]
//   inductive:  <steps...>    -- has ih : body in scope               [Nat only]
//
// OR for user-defined inductive types (type_name != "Nat"):
//   induction <name> on <var> : <body>
//     case nil:  <steps...>
//     case cons head tail ih: <steps...>
//
// Proves ∀ var : T, body.
struct InductionStep {
    std::string                        name;            // label for the result in scope
    std::string                        var;             // induction variable
    std::string                        type_name;       // "Nat" for Nat induction; else inductive type
    Prop                               body;            // P(var) — the inductive predicate
    // Nat induction sub-blocks (used when type_name == "Nat"):
    std::vector<std::unique_ptr<Step>> base_steps;      // proves P(0)
    std::vector<std::unique_ptr<Step>> inductive_steps; // proves P(succ(var)) using ih : P(var)
    // Structural induction arms (used when type_name != "Nat"):
    std::vector<InductionArm>          arms;
};

struct ShowStep {
    Prop prop;  // asserted goal; checker verifies prop == decl.statement
};

struct ExactStep {
    std::string hyp_ref;  // hypothesis name whose prop must equal the current goal
};

struct RewriteItem {
    std::string hyp_ref;    // hypothesis name
    bool        reverse;    // if true, rewrite rhs→lhs (or Q→P for iff form)
    bool        iff_rewrite;// if true, h must be P↔Q; rewrites propositions
    bool operator==(const RewriteItem&) const = default;
};

struct RewriteStep {
    std::vector<RewriteItem> rewrites;  // applied left-to-right
};

struct ApplyStep {
    std::string hyp_ref;  // hypothesis name; must be PropImpl{A, B} where B == current goal
};

// wlog <name> : <prop>
struct WlogStep {
    std::string name;
    Prop        prop;
};

struct CalcLink {
    RelOp                      op;
    ExprPtr                    rhs;
    std::vector<std::string>   justification;
};

struct CalcStep {
    std::string              name;
    ExprPtr                  lhs;
    std::vector<CalcLink>    links;
};

struct SplitArm {
    std::string                        label;
    std::vector<std::unique_ptr<Step>> steps;
};

struct SplitStep {
    std::string              name;
    std::vector<SplitArm>    arms;
};

// push neg [at h] — push negations inward via De Morgan + classical equivalences.
struct PushNegStep {
    std::optional<std::string> hyp;  // nullopt → apply to goal; string → apply to named hyp
};

using StepNode = std::variant<
    LetStep, TakeStep, SupposeStep, HaveStep, ThenStep, ContradictionStep,
    CasesStep, ObtainStep, InductionStep, ShowStep, ExactStep, RewriteStep, ApplyStep,
    CalcStep, SplitStep, WlogStep, PushNegStep
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

// One constructor of a user-defined inductive type.
// arg_types holds the types of each constructor argument as raw strings (pre-type-system).
// is_recursive[i] is true when arg_types[i] refers back to the inductive type itself.
struct InductiveConstructor {
    std::string              name;
    std::vector<std::string> arg_types;    // raw type strings, e.g. {"Nat", "List"}
    std::vector<bool>        is_recursive; // true for args whose type == inductive type name
};

// Namespace kind groups declarations under a qualified prefix.
// Open kind brings a namespace into unqualified scope.
enum class DeclKind { Axiom, Definition, Lemma, Theorem, Import, Instance, Structure, Quotient,
                      Namespace, Open, TypeAlias, Inductive, NamespaceAlias };

// visibility of a declaration (controls export during import).
enum class Visibility { Public, Private, Protected };

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
    // for DeclKind::Namespace — inner declarations
    std::vector<std::unique_ptr<Decl>> ns_decls;
    // for DeclKind::Open with "open X in <decl>" scoped form — the single inner decl
    std::unique_ptr<Decl> open_scope_decl;
    // for DeclKind::NamespaceAlias — the dotted target (e.g. "Analysis.Sequence")
    std::string alias_target;
    // visibility for export control
    Visibility                visibility{Visibility::Public};
    // abstract flag — definition body not unfoldable
    bool                      is_abstract{false};
    // propositional body for `definition P(x : T) := body` forms.
    // When present, the checker registers P as a predicate definition that
    // can be unfolded: P(t) → subst(body, param_names, args).
    std::optional<PropPtr>    def_body;
    // for DeclKind::TypeAlias: the right-hand side type expression.
    std::optional<TypeNode>   type_alias_body;
    // for DeclKind::Inductive: the constructor list.
    std::vector<InductiveConstructor> inductive_ctors;
};

// Maps structure name → its field list.  Used by the checker to process
// structure instantiations.
using StructEnv = std::map<std::string, std::vector<StructField>>;

// Maps inductive type name → its constructor list.  Built by the checker when
// processing DeclKind::Inductive declarations; consulted by check_induction_step.
using InductiveEnv = std::map<std::string, std::vector<InductiveConstructor>>;

using DeclPtr = std::unique_ptr<Decl>;

// ── Module ─────────────────────────────────────────────────────────────────────

struct Module {
    std::string          path;
    std::vector<DeclPtr> decls;
};

// ── Type environment and inference ────────────────────────────────────────────

// Maps term variable names to their annotated types (from binders / takes / lets).
using TypeEnv = std::map<std::string, TypeNode>;

// Maps type alias names to their expanded TypeNode bodies.
// Populated from DeclKind::TypeAlias declarations; consulted by expand_type_aliases().
using TypeAliasTable = std::map<std::string, TypeNode>;

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

// Recursively expands TypeUser{name} nodes in t using the alias table.
// Stops when no further expansion is possible (idempotent for closed aliases).
// Returns t unchanged if aliases is empty.
[[nodiscard]] TypeNode
expand_type_aliases(TypeNode t, const TypeAliasTable& aliases);

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

// subst_expr: expression-level find-and-replace.
// Replaces every structurally-equal occurrence of `find` inside `prop` (or
// `expr`) with `replace`.  Unlike `subst`, the target is a full expression
// rather than a named variable — needed for rewriting e.g. `b[k]` → `a[phi(k)]`
// inside an absolute-value term.
[[nodiscard]] Prop subst_expr(const Prop& prop, const Expr& find, const Expr& replace);
[[nodiscard]] Expr subst_expr(const Expr& expr, const Expr& find, const Expr& replace);

// subst_prop: proposition-level find-and-replace.
// Replaces every structurally-equal occurrence of `find` inside `prop` with
// `replace`.  Used to implement `rewrite ↔ h` (propositional rewriting).
[[nodiscard]] Prop subst_prop(const Prop& prop, const Prop& find, const Prop& replace);

// subst_type: type-level substitution of a term variable.
// Replaces every occurrence of TypeUser{var} in `t` with TypeUser{arg_name}
// where arg_name is the variable name extracted from `arg` (if arg is ExprVar).
// Used to compute the return type of a TypePi-typed function application:
//   (x : A) -> B(x)  applied to  t : A  yields  subst_type(B, x, t).
[[nodiscard]] TypeNode subst_type(const TypeNode& t, const std::string& var, const Expr& arg);

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
