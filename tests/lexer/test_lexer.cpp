#include <gtest/gtest.h>
#include <forall/lexer/lexer.hpp>

using namespace forall;

TEST(LexerTest, KeywordsAreRecognised) {
    diag::DiagnosticEngine diag;
    lexer::Lexer lex{"axiom theorem lemma proof end", "test", diag};
    auto toks = lex.tokenize();

    EXPECT_FALSE(diag.hasErrors());
    EXPECT_EQ(toks[0].kind, lexer::TokenKind::KwAxiom);
    EXPECT_EQ(toks[1].kind, lexer::TokenKind::KwTheorem);
    EXPECT_EQ(toks[2].kind, lexer::TokenKind::KwLemma);
    EXPECT_EQ(toks[3].kind, lexer::TokenKind::KwProof);
    EXPECT_EQ(toks[4].kind, lexer::TokenKind::KwEnd);
    EXPECT_EQ(toks[5].kind, lexer::TokenKind::Eof);
}

TEST(LexerTest, IdentifiersAreRecognised) {
    diag::DiagnosticEngine diag;
    lexer::Lexer lex{"my_prop hello_world", "test", diag};
    auto toks = lex.tokenize();

    EXPECT_FALSE(diag.hasErrors());
    EXPECT_EQ(toks[0].kind, lexer::TokenKind::Identifier);
    EXPECT_EQ(toks[0].lexeme, "my_prop");
    EXPECT_EQ(toks[1].kind, lexer::TokenKind::Identifier);
    EXPECT_EQ(toks[1].lexeme, "hello_world");
}

TEST(LexerTest, LineCommentsAreSkipped) {
    diag::DiagnosticEngine diag;
    lexer::Lexer lex{"axiom -- this is a comment\ntheorem", "test", diag};
    auto toks = lex.tokenize();

    EXPECT_FALSE(diag.hasErrors());
    EXPECT_EQ(toks[0].kind, lexer::TokenKind::KwAxiom);
    EXPECT_EQ(toks[1].kind, lexer::TokenKind::KwTheorem);
    EXPECT_EQ(toks[2].kind, lexer::TokenKind::Eof);
}

TEST(LexerTest, UnicodeMathSymbolsAreLexed) {
    diag::DiagnosticEngine diag;
    // ∀ ∃ ∧ ∨ ¬ →  as raw UTF-8 bytes
    lexer::Lexer lex{"\xe2\x88\x80 \xe2\x88\x83 \xe2\x88\xa7 \xe2\x88\xa8 \xc2\xac \xe2\x86\x92", "test", diag};
    auto toks = lex.tokenize();

    EXPECT_FALSE(diag.hasErrors());
    EXPECT_EQ(toks[0].kind, lexer::TokenKind::Forall);
    EXPECT_EQ(toks[1].kind, lexer::TokenKind::Exists);
    EXPECT_EQ(toks[2].kind, lexer::TokenKind::And);
    EXPECT_EQ(toks[3].kind, lexer::TokenKind::Or);
    EXPECT_EQ(toks[4].kind, lexer::TokenKind::Not);
    EXPECT_EQ(toks[5].kind, lexer::TokenKind::Arrow);
}

TEST(LexerTest, SourceLocationTracksLineAndColumn) {
    diag::DiagnosticEngine diag;
    lexer::Lexer lex{"axiom\ntheorem", "test", diag};
    auto toks = lex.tokenize();

    EXPECT_EQ(toks[0].loc.line, 1u);
    EXPECT_EQ(toks[0].loc.col,  1u);
    EXPECT_EQ(toks[1].loc.line, 2u);
    EXPECT_EQ(toks[1].loc.col,  1u);
}

// ── Set terms ──────────────────────────────────────────────────────────────────

TEST(LexerTest, SetTermUnicodeSymbols) {
    diag::DiagnosticEngine diag;
    // ∈  ∉  ⊆  ⊂  ⊇  ∪  ∩  (raw UTF-8)
    lexer::Lexer lex{
        "\xe2\x88\x88 "   // ∈ U+2208
        "\xe2\x88\x89 "   // ∉ U+2209
        "\xe2\x8a\x86 "   // ⊆ U+2286
        "\xe2\x8a\x82 "   // ⊂ U+2282
        "\xe2\x8a\x87 "   // ⊇ U+2287
        "\xe2\x88\xaa "   // ∪ U+222A
        "\xe2\x88\xa9",   // ∩ U+2229
        "test", diag};
    auto toks = lex.tokenize();

    ASSERT_FALSE(diag.hasErrors());
    EXPECT_EQ(toks[0].kind, lexer::TokenKind::MemberOf);
    EXPECT_EQ(toks[1].kind, lexer::TokenKind::NotMemberOf);
    EXPECT_EQ(toks[2].kind, lexer::TokenKind::SubseteqSym);
    EXPECT_EQ(toks[3].kind, lexer::TokenKind::SubsetSym);
    EXPECT_EQ(toks[4].kind, lexer::TokenKind::SuperseteqSym);
    EXPECT_EQ(toks[5].kind, lexer::TokenKind::CupSym);
    EXPECT_EQ(toks[6].kind, lexer::TokenKind::CapSym);
}

TEST(LexerTest, SetTermKeywords) {
    diag::DiagnosticEngine diag;
    lexer::Lexer lex{"subseteq subset supseteq union inter setminus compl in", "test", diag};
    auto toks = lex.tokenize();

    ASSERT_FALSE(diag.hasErrors());
    EXPECT_EQ(toks[0].kind, lexer::TokenKind::KwSubseteq);
    EXPECT_EQ(toks[1].kind, lexer::TokenKind::KwSubset);
    EXPECT_EQ(toks[2].kind, lexer::TokenKind::KwSupseteq);
    EXPECT_EQ(toks[3].kind, lexer::TokenKind::KwUnion);
    EXPECT_EQ(toks[4].kind, lexer::TokenKind::KwInter);
    EXPECT_EQ(toks[5].kind, lexer::TokenKind::KwSetMinus);
    EXPECT_EQ(toks[6].kind, lexer::TokenKind::KwCompl);
    EXPECT_EQ(toks[7].kind, lexer::TokenKind::KwIn);
}

TEST(LexerTest, BackslashTokenForSetDifference) {
    diag::DiagnosticEngine diag;
    lexer::Lexer lex{"A \\ B", "test", diag};
    auto toks = lex.tokenize();

    ASSERT_FALSE(diag.hasErrors());
    EXPECT_EQ(toks[0].kind, lexer::TokenKind::Identifier);
    EXPECT_EQ(toks[1].kind, lexer::TokenKind::Backslash);
    EXPECT_EQ(toks[2].kind, lexer::TokenKind::Identifier);
}

TEST(LexerTest, BackslashSlashIsOrNotBackslash) {
    // "\/" is the ASCII alternative for ∨; a lone "\" is Backslash
    diag::DiagnosticEngine diag;
    lexer::Lexer lex{"P \\/ Q", "test", diag};
    auto toks = lex.tokenize();

    ASSERT_FALSE(diag.hasErrors());
    EXPECT_EQ(toks[0].kind, lexer::TokenKind::Identifier); // P
    EXPECT_EQ(toks[1].kind, lexer::TokenKind::Or);          // \/
    EXPECT_EQ(toks[2].kind, lexer::TokenKind::Identifier); // Q
}
