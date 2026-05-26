#include <forall/parser/parser.hpp>

namespace forall::parser {

Parser::Parser(std::span<const lexer::Token> tokens, diag::DiagnosticEngine& diag)
    : tokens_{tokens}, diag_{diag} {}

const lexer::Token& Parser::peek() const noexcept {
    return tokens_[pos_];
}

const lexer::Token& Parser::advance() noexcept {
    if (!isAtEnd()) ++pos_;
    return tokens_[pos_ - 1];
}

bool Parser::check(lexer::TokenKind kind) const noexcept {
    return peek().kind == kind;
}

bool Parser::isAtEnd() const noexcept {
    return check(lexer::TokenKind::Eof);
}

bool Parser::expect(lexer::TokenKind kind, std::string_view msg) {
    if (check(kind)) { advance(); return true; }
    diag_.emit({diag::Severity::Error, peek().loc, std::string{msg}});
    return false;
}

ast::Prop Parser::parseProp() {
    // Placeholder: greedily consumes tokens until the next declaration keyword.
    // Requires ast::Prop to become a structural expression tree for proper parsing.
    ast::Prop prop{peek().loc, {}};
    while (!isAtEnd()
        && !check(lexer::TokenKind::KwAxiom)
        && !check(lexer::TokenKind::KwDefinition)
        && !check(lexer::TokenKind::KwLemma)
        && !check(lexer::TokenKind::KwTheorem)
        && !check(lexer::TokenKind::KwProof)
        && !check(lexer::TokenKind::KwEnd))
    {
        if (!prop.raw.empty()) prop.raw += ' ';
        prop.raw += advance().lexeme;
    }
    return prop;
}

std::optional<ast::DeclPtr> Parser::parseAxiom() {
    const auto loc = peek().loc;
    advance(); // consume 'axiom'

    if (!check(lexer::TokenKind::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected axiom name"});
        return std::nullopt;
    }
    std::string name{advance().lexeme};
    expect(lexer::TokenKind::Colon, "expected ':' after axiom name");
    auto prop = parseProp();

    return std::make_unique<ast::Decl>(ast::DeclKind::Axiom, std::move(name), loc, std::move(prop));
}

std::optional<ast::DeclPtr> Parser::parseTheorem(ast::DeclKind kind) {
    const auto loc = peek().loc;
    advance(); // consume 'theorem' or 'lemma'

    if (!check(lexer::TokenKind::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected theorem name"});
        return std::nullopt;
    }
    std::string name{advance().lexeme};
    expect(lexer::TokenKind::Colon, "expected ':' after theorem name");
    auto prop = parseProp();

    // Consume optional proof block
    if (check(lexer::TokenKind::KwProof)) {
        advance();
        // TODO: parse proof steps
        while (!isAtEnd() && !check(lexer::TokenKind::KwEnd)) advance();
        expect(lexer::TokenKind::KwEnd, "expected 'end' to close proof");
    }

    return std::make_unique<ast::Decl>(kind, std::move(name), loc, std::move(prop));
}

std::optional<ast::DeclPtr> Parser::parseDeclaration() {
    if (check(lexer::TokenKind::KwAxiom))
        return parseAxiom();
    if (check(lexer::TokenKind::KwTheorem))
        return parseTheorem(ast::DeclKind::Theorem);
    if (check(lexer::TokenKind::KwLemma))
        return parseTheorem(ast::DeclKind::Lemma);

    diag_.emit({diag::Severity::Error, peek().loc,
                "expected 'axiom', 'theorem', or 'lemma'; got '" + peek().lexeme + "'"});
    advance(); // error recovery: skip one token
    return std::nullopt;
}

ast::Module Parser::parse() {
    ast::Module mod;
    while (!isAtEnd()) {
        if (auto decl = parseDeclaration())
            mod.decls.push_back(std::move(*decl));
    }
    return mod;
}

} // namespace forall::parser
