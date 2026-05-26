#pragma once
#include <forall/diagnostics/source_location.hpp>

#include <memory>
#include <string>
#include <vector>

namespace forall::ast {

// ── Proposition ────────────────────────────────────────────────────────────────
// Placeholder: stores the raw source text until ast::Prop becomes a proper
// expression tree (connectives, quantifiers, variables).
struct Prop {
    diag::SourceLocation loc;
    std::string          raw;
};

// ── Top-level declarations ─────────────────────────────────────────────────────
// Every item at the top level of a .forall file is a Decl.
// Axioms carry no proof; Theorems and Lemmas carry a proof body.
enum class DeclKind { Axiom, Definition, Lemma, Theorem };

struct Decl {
    DeclKind             kind;
    std::string          name;
    diag::SourceLocation loc;
    Prop                 statement;
};

using DeclPtr = std::unique_ptr<Decl>;

// ── Module ─────────────────────────────────────────────────────────────────────
// One parsed .forall source file.
struct Module {
    std::string          path;
    std::vector<DeclPtr> decls;
};

} // namespace forall::ast
