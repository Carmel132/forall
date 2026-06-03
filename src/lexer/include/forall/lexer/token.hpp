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
    KwProof, KwEnd, KwImport, KwInstance, KwStructure, KwQuotient,

    // Proof-step keywords
    KwLet, KwBe, KwSuppose, KwHave, KwThen,
    KwContradiction, KwBy, KwWith, KwAt, KwDone, KwTake, KwObtain, KwFrom, KwSo,

    // Logical keywords (natural-language alternatives to symbols)
    KwIf,                       // "if"
    KwFor, KwAll, KwThere,      // "for all", "there exists"
    KwImplies,                  // "implies"
    KwFalse,                    // "false" / ⊥
    KwTrue,                     // "true"  / ⊤
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
    KwCalc,                          // "calc"
    KwCase, KwCases, KwOn,
    KwInduction,                // "induction"
    KwShow,                     // "show"   (goal annotation step)
    KwExact,                    // "exact"  (close goal by hypothesis)
    KwRewrite,                  // "rewrite" (equality rewriting step)
    // "apply" is context-sensitive — lexed as Identifier, dispatched by parseStep()
    KwDecide,                   // "decide"    (tactic keyword)
    KwNormNum,                  // "norm_num"  (tactic keyword)
    KwRing,                     // "ring"      (tactic keyword)
    KwLinarith,                 // "linarith"  (linear arithmetic tactic)
    KwSimp,                     // "simp"      (propositional simplification tactic)
    // "contra" is context-sensitive — lexed as Identifier, handled in parseJustification()
    // "base" and "inductive" are context-sensitive — lexed as Identifier

    // Punctuation
    Colon, ColonColon,          // :  ::
    ColonEquals,                // :=
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
    Pipe,                       // |  (absolute value / set-comprehension separator)

    // Set relation operators (proposition level)
    MemberOf,                   // ∈  U+2208  (or "in")
    NotMemberOf,                // ∉  U+2209  (or "not in")
    KwSubseteq,                 // "subseteq"
    SubseteqSym,                // ⊆  U+2286
    KwSubset,                   // "subset"  (strict subset)
    SubsetSym,                  // ⊂  U+2282
    KwSupseteq,                 // "supseteq"
    SuperseteqSym,              // ⊇  U+2287

    // Set binary operators (expression level)
    KwUnion,                    // "union"
    CupSym,                     // ∪  U+222A
    KwInter,                    // "inter"
    CapSym,                     // ∩  U+2229
    KwSetMinus,                 // "setminus"
    Backslash,                  // \  (set difference ASCII alternative)
    KwCompl,                    // "compl"  (set complement prefix)

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
