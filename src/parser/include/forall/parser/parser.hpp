#pragma once
#include <forall/ast/node.hpp>
#include <forall/diagnostics/diagnostic.hpp>
#include <forall/lexer/token.hpp>

#include <optional>
#include <span>

namespace forall::parser {

// Recursive-descent parser.  Converts a flat token stream into an ast::Module.
// Errors are emitted to the DiagnosticEngine; parsing always returns a (possibly
// partial) module so the checker can report all errors in one pass.
class Parser {
public:
    explicit Parser(std::span<const lexer::Token> tokens, diag::DiagnosticEngine& diag);

    [[nodiscard]] ast::Module parse();

private:
    [[nodiscard]] std::optional<ast::DeclPtr> parseDeclaration();
    [[nodiscard]] std::optional<ast::DeclPtr> parseAxiom();
    [[nodiscard]] std::optional<ast::DeclPtr> parseTheorem(ast::DeclKind kind);
    [[nodiscard]] ast::Prop                   parseProp();

    [[nodiscard]] const lexer::Token& peek() const noexcept;
    const lexer::Token& advance() noexcept;
    bool expect(lexer::TokenKind kind, std::string_view msg);
    [[nodiscard]] bool check(lexer::TokenKind kind) const noexcept;
    [[nodiscard]] bool isAtEnd() const noexcept;

    std::span<const lexer::Token> tokens_;
    diag::DiagnosticEngine&       diag_;
    std::size_t                   pos_{0};
};

} // namespace forall::parser
