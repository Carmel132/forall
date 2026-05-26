#pragma once
#include <forall/lexer/token.hpp>
#include <forall/diagnostics/diagnostic.hpp>

#include <string>
#include <vector>

namespace forall::lexer {

class Lexer {
public:
    explicit Lexer(std::string source, std::string filename, diag::DiagnosticEngine& diag);

    // Tokenize the full source. The vector always ends with an Eof token.
    [[nodiscard]] std::vector<Token> tokenize();

private:
    [[nodiscard]] Token nextToken();
    void skipWhitespaceAndComments();

    [[nodiscard]] bool isAtEnd() const noexcept { return pos_ >= source_.size(); }

    std::string             source_;
    std::string             filename_;
    diag::DiagnosticEngine& diag_;
    std::size_t             pos_{0};
    std::uint32_t           line_{1};
    std::uint32_t           col_{1};
};

} // namespace forall::lexer
