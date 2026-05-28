#pragma once
#include <forall/diagnostics/source_location.hpp>
#include <string>

namespace forall::lexer {

enum class TokenKind {
    // Literals & identifiers
    Identifier,
    Number,
    StringLit,                   // "..."

    // Declaration keywords
    KwAxiom, KwDefinition, KwLemma, KwTheorem,
    KwProof, KwEnd, KwImport,

    // Proof-step keywords
    KwLet, KwBe, KwSuppose, KwHave, KwThen,
    KwContradiction, KwBy, KwWith,

    // Logical keywords (natural-language alternatives to symbols)
    KwIf,                       // "if"
    KwFor, KwAll, KwThere,      // "for all", "there exists"
    KwImplies,                  // "implies"
    KwFalse,                    // "false" / ⊥
    KwIn,                       // "in"
    KwDiv, KwMod,               // integer division and modulo
    KwFun,                      // "fun"
    KwElse,                     // "else"
    KwSum,                      // "sum"
    KwProd,                     // "prod"
    Lambda,                     // λ  U+03BB
    Sigma,                      // ∑  U+2211
    Pi,                         // ∏  U+220F
    LFloor, RFloor,             // ⌊ ⌋  U+230A / U+230B
    LCeil,  RCeil,              // ⌈ ⌉  U+2308 / U+2309
    Bang,                       // !  (factorial postfix)
    KwCompose,                  // "compose" / "circ"
    Circ,                       // ∘  U+2218
    KwInv,                      // "inv" (prefix function inverse)

    // Proof-step tactic keywords
    KwCase, KwCases, KwOn,

    // Punctuation
    Colon, ColonColon,          // :  ::
    Comma,                      // ,
    Dot,                        // .
    FatArrow,                   // =>

    // Arithmetic operators
    Plus, Minus, Star, Slash, Caret,    // + - * / ^

    // Comparison operators
    Equals,                     // =
    Less, Greater,              // <  >
    LessEq, GreaterEq,          // <=  >=
    NotEq,                      // /=

    // Math symbols — Unicode and ASCII alternatives both produce these
    Arrow,                      // →  (or ->  or "implies")
    Iff,                        // ↔
    Forall,                     // ∀  (or "for all")
    Exists,                     // ∃  (or "there exists")
    And,                        // ∧  (or /\  or "and")
    Or,                         // ∨  (or \/  or "or")
    Not,                        // ¬  (or ~   or "not")
    Pipe,                       // |  (absolute value)

    // Brackets
    LParen, RParen,             // ( )
    LBracket, RBracket,         // [ ]
    LBrace, RBrace,             // { }

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
