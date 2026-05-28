#include <forall/lexer/lexer.hpp>

#include <cctype>
#include <string_view>
#include <utility>

namespace forall::lexer {

Lexer::Lexer(std::string source, std::string filename, diag::DiagnosticEngine& diag)
    : source_{std::move(source)}, filename_{std::move(filename)}, diag_{diag} {}

void Lexer::skipWhitespaceAndComments() {
    while (!isAtEnd()) {
        const char c = source_[pos_];
        if (c == '\n') {
            ++pos_; ++line_; col_ = 1;
        } else if (c == ' ' || c == '\t' || c == '\r') {
            ++pos_; ++col_;
        } else if (c == '-' && pos_ + 1 < source_.size() && source_[pos_ + 1] == '-') {
            while (!isAtEnd() && source_[pos_] != '\n') { ++pos_; ++col_; }
        } else {
            break;
        }
    }
}

Token Lexer::nextToken() {
    skipWhitespaceAndComments();
    if (isAtEnd())
        return Token{TokenKind::Eof, "", {filename_, line_, col_}};

    const std::size_t   start_pos  = pos_;
    const std::uint32_t start_line = line_;
    const std::uint32_t start_col  = col_;

    auto make = [&](TokenKind kind) -> Token {
        return Token{kind, source_.substr(start_pos, pos_ - start_pos), {filename_, start_line, start_col}};
    };

    // Column numbers are byte offsets, not codepoint indices.
    auto consume = [&](std::size_t n) {
        pos_ += n;
        col_ += static_cast<std::uint32_t>(n);
    };

    const unsigned char uc = static_cast<unsigned char>(source_[pos_]);

    // ── Multi-byte Unicode math symbols ───────────────────────────────────────
    //   ¬  U+00AC  →  C2 AC
    //   →  U+2192  →  E2 86 92
    //   ↔  U+2194  →  E2 86 94
    //   ∀  U+2200  →  E2 88 80
    //   ∃  U+2203  →  E2 88 83
    //   ∧  U+2227  →  E2 88 A7
    //   ∨  U+2228  →  E2 88 A8
    if (uc == 0xC2 && pos_ + 1 < source_.size()) {
        const auto b = static_cast<unsigned char>(source_[pos_ + 1]);
        if (b == 0xAC) { consume(2); return make(TokenKind::Not); }
    }
    if (uc == 0xE2 && pos_ + 2 < source_.size()) {
        const auto b1 = static_cast<unsigned char>(source_[pos_ + 1]);
        const auto b2 = static_cast<unsigned char>(source_[pos_ + 2]);
        if (b1 == 0x86) {
            if (b2 == 0x92) { consume(3); return make(TokenKind::Arrow);  }
            if (b2 == 0x94) { consume(3); return make(TokenKind::Iff);    }
        }
        if (b1 == 0x88) {
            if (b2 == 0x80) { consume(3); return make(TokenKind::Forall); }
            if (b2 == 0x83) { consume(3); return make(TokenKind::Exists); }
            if (b2 == 0xA7) { consume(3); return make(TokenKind::And);    }
            if (b2 == 0xA8) { consume(3); return make(TokenKind::Or);     }
        }
        // □  U+25A1  →  E2 96 A1  (alternative proof terminator)
        if (b1 == 0x96 && b2 == 0xA1) { consume(3); return make(TokenKind::KwEnd); }
    }

    // ── Numbers ───────────────────────────────────────────────────────────────
    if (std::isdigit(uc)) {
        while (!isAtEnd() && std::isdigit(static_cast<unsigned char>(source_[pos_])))
            consume(1);
        if (!isAtEnd() && source_[pos_] == '.') {
            consume(1);
            while (!isAtEnd() && std::isdigit(static_cast<unsigned char>(source_[pos_])))
                consume(1);
        }
        return make(TokenKind::Number);
    }

    // ── ASCII ─────────────────────────────────────────────────────────────────
    consume(1);
    const char c = static_cast<char>(uc);

    switch (c) {
        case '(': return make(TokenKind::LParen);
        case ')': return make(TokenKind::RParen);
        case '{': return make(TokenKind::LBrace);
        case '}': return make(TokenKind::RBrace);
        case ',': return make(TokenKind::Comma);
        case '.': return make(TokenKind::Dot);
        case '+': return make(TokenKind::Plus);
        case '*': return make(TokenKind::Star);
        case '|': return make(TokenKind::Pipe);
        case ':':
            if (!isAtEnd() && source_[pos_] == ':') { consume(1); return make(TokenKind::ColonColon); }
            return make(TokenKind::Colon);
        case '=':
            if (!isAtEnd() && source_[pos_] == '>') { consume(1); return make(TokenKind::FatArrow); }
            return make(TokenKind::Equals);
        case '<':
            if (!isAtEnd() && source_[pos_] == '=') { consume(1); return make(TokenKind::LessEq); }
            return make(TokenKind::Less);
        case '>':
            if (!isAtEnd() && source_[pos_] == '=') { consume(1); return make(TokenKind::GreaterEq); }
            return make(TokenKind::Greater);
        case '-':
            if (!isAtEnd() && source_[pos_] == '>') { consume(1); return make(TokenKind::Arrow); }
            return make(TokenKind::Minus);
        case '~': return make(TokenKind::Not);
        case '/':
            if (!isAtEnd() && source_[pos_] == '\\') { consume(1); return make(TokenKind::And); }
            if (!isAtEnd() && source_[pos_] == '=')  { consume(1); return make(TokenKind::NotEq); }
            return make(TokenKind::Slash);
        case '\\':
            if (!isAtEnd() && source_[pos_] == '/') { consume(1); return make(TokenKind::Or); }
            break;
    }

    // ── Identifiers and keywords ──────────────────────────────────────────────
    if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
        while (!isAtEnd() && (std::isalnum(static_cast<unsigned char>(source_[pos_])) || source_[pos_] == '_'))
            consume(1);

        const std::string_view word{source_.data() + start_pos, pos_ - start_pos};

        static constexpr std::pair<std::string_view, TokenKind> keywords[] = {
            // Declaration
            {"axiom",        TokenKind::KwAxiom},
            {"definition",   TokenKind::KwDefinition},
            {"lemma",        TokenKind::KwLemma},
            {"theorem",      TokenKind::KwTheorem},
            {"proof",        TokenKind::KwProof},
            {"end",          TokenKind::KwEnd},
            // Proof steps (primary keywords and accessibility aliases)
            {"let",          TokenKind::KwLet},
            {"be",           TokenKind::KwBe},
            {"suppose",      TokenKind::KwSuppose},
            {"assume",       TokenKind::KwSuppose},  // alias: assume h : P
            {"have",         TokenKind::KwHave},
            {"then",         TokenKind::KwThen},
            {"therefore",    TokenKind::KwThen},     // alias: therefore P by ...
            {"thus",         TokenKind::KwThen},     // alias: thus P by ...
            {"contradiction",TokenKind::KwContradiction},
            {"qed",          TokenKind::KwEnd},      // alias: qed closes proof block
            {"by",           TokenKind::KwBy},
            {"with",         TokenKind::KwWith},
            {"exact",        TokenKind::KwExact},
            {"apply",        TokenKind::KwApply},
            // Logic keywords (natural-language symbols)
            {"if",           TokenKind::KwIf},
            {"for",          TokenKind::KwFor},
            {"all",          TokenKind::KwAll},
            {"there",        TokenKind::KwThere},
            {"exists",       TokenKind::Exists},  // shares token with ∃
            {"implies",      TokenKind::Arrow},   // shares token with →
            {"false",        TokenKind::KwFalse},
            {"in",           TokenKind::KwIn},
            // Connective words (share tokens with symbols)
            {"and",          TokenKind::And},
            {"or",           TokenKind::Or},
            {"not",          TokenKind::Not},
            // Misc
            {"case",         TokenKind::KwCase},
            {"cases",        TokenKind::KwCases},
            {"on",           TokenKind::KwOn},
        };
        for (const auto& [kw, kind] : keywords)
            if (word == kw) return make(kind);
        return make(TokenKind::Identifier);
    }

    diag_.emit({diag::Severity::Error, {filename_, start_line, start_col},
                std::string{"unexpected character: '"} + c + "'"});
    return make(TokenKind::Error);
}

std::vector<Token> Lexer::tokenize() {
    std::vector<Token> tokens;
    while (true) {
        tokens.push_back(nextToken());
        if (tokens.back().kind == TokenKind::Eof) break;
    }
    return tokens;
}

} // namespace forall::lexer
