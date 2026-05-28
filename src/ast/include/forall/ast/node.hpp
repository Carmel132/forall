#pragma once
#include <forall/diagnostics/source_location.hpp>

#include <memory>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace forall::ast {

// ── Forward declarations ───────────────────────────────────────────────────────
struct Prop;
using PropPtr = std::shared_ptr<Prop>;

struct Step; // forward-declared so CasesStep can hold std::unique_ptr<Step>

// ── Propositions ───────────────────────────────────────────────────────────────
struct Atomic   { std::string name; };         // P, Q, excluded_middle, …
struct PropFalse {};                           // ⊥
struct PropNot  { PropPtr inner; };            // ¬P
struct PropAnd  { PropPtr lhs, rhs; };         // P ∧ Q
struct PropOr   { PropPtr lhs, rhs; };         // P ∨ Q
struct PropImpl { PropPtr lhs, rhs; };         // P → Q

using PropNode = std::variant<
    Atomic, PropFalse,
    PropNot, PropAnd, PropOr, PropImpl
>;

struct Prop {
    diag::SourceLocation loc;
    PropNode             node;

    bool operator==(const Prop&) const;  // structural, ignores loc
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
    std::optional<std::string> type; // "let P be a Prop"
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
};

struct ThenStep {
    Prop                     prop;
    std::vector<std::string> justification;
};

struct ContradictionStep {
    std::vector<std::string> justification;
};

using StepNode = std::variant<
    LetStep, SupposeStep, HaveStep, ThenStep, ContradictionStep, CasesStep
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

struct Decl {
    DeclKind                  kind;
    std::string               name;       // for Import: the file path (quotes stripped)
    diag::SourceLocation      loc;
    Prop                      statement;  // for Import: dummy PropFalse{}
    std::optional<ProofBlock> proof;      // absent for Axiom / Import
};

using DeclPtr = std::unique_ptr<Decl>;

// ── Module ─────────────────────────────────────────────────────────────────────

struct Module {
    std::string          path;
    std::vector<DeclPtr> decls;
};

} // namespace forall::ast
