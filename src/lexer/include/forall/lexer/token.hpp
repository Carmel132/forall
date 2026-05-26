#pragma once
#include <forall/diagnostics/source_location.hpp>
#include <string>

namespace forall::lexer {

enum class TokenKind {
    // Literals & identifiers
    Identifier,

    // Keywords
    KwAxiom, KwDefinition, KwLemma, KwTheorem,
    KwProof, KwEnd,
    KwAssume, KwExact, KwApply, KwHave,
    KwBy, KwCase, KwCases, KwOn,

    // Punctuation
    Colon, ColonColon,  // :  ::
    Comma,              // ,
    Dot,                // .
    FatArrow,           // =>

    // Math symbols (ASCII alternatives accepted alongside Unicode)
    Arrow,              // →  (or ->)
    Iff,                // ↔  (or <->)
    Forall,             // ∀  (or \forall)
    Exists,             // ∃  (or \exists)
    And,                // ∧  (or /\)
    Or,                 // ∨  (or \/)
    Not,                // ¬  (or ~)

    // Brackets
    LParen, RParen,     // ( )
    LBrace, RBrace,     // { }

    // Sentinels
    Eof,
    Error,
};

struct Token {
    TokenKind            kind;
    std::string          lexeme;
    diag::SourceLocation loc;
};

} // namespace forall::lexer
