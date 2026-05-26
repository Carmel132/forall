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

// ── Propositions ───────────────────────────────────────────────────────────────
// Propositional nodes. Quantifiers and arithmetic expressions are not yet
// modelled; they will be added when the checker grows to predicate logic.

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
    LetStep, SupposeStep, HaveStep, ThenStep, ContradictionStep
>;

struct Step {
    diag::SourceLocation loc;
    StepNode             node;
};

struct ProofBlock {
    std::vector<Step> steps;
};

// ── Top-level declarations ─────────────────────────────────────────────────────

enum class DeclKind { Axiom, Definition, Lemma, Theorem };

struct Decl {
    DeclKind                  kind;
    std::string               name;
    diag::SourceLocation      loc;
    Prop                      statement;
    std::optional<ProofBlock> proof; // present for Theorem / Lemma
};

using DeclPtr = std::unique_ptr<Decl>;

// ── Module ─────────────────────────────────────────────────────────────────────

struct Module {
    std::string          path;
    std::vector<DeclPtr> decls;
};

} // namespace forall::ast
