#pragma once
#include <forall/ast/node.hpp>
#include <forall/diagnostics/diagnostic.hpp>
#include <forall/lexer/token.hpp>

#include <optional>
#include <span>
#include <string>
#include <vector>

namespace forall::parser {

// Recursive-descent parser. Converts a flat token stream into an ast::Module.
// Errors are emitted to the DiagnosticEngine; parsing always returns a (possibly
// partial) module so the checker can report all errors in one pass.
class Parser {
public:
    explicit Parser(std::span<const lexer::Token> tokens, diag::DiagnosticEngine& diag);

    [[nodiscard]] ast::Module parse();

private:
    // Declarations
    [[nodiscard]] std::optional<ast::DeclPtr> parseDeclaration();
    [[nodiscard]] std::optional<ast::DeclPtr> parseAxiom();
    [[nodiscard]] std::optional<ast::DeclPtr> parseDefinition();
    [[nodiscard]] std::optional<ast::DeclPtr> parseTheorem(ast::DeclKind kind);
    [[nodiscard]] std::optional<ast::DeclPtr> parseImport();

    // Proof blocks and steps
    [[nodiscard]] ast::ProofBlock parseProofBlock();
    [[nodiscard]] ast::Step       parseStep();
    [[nodiscard]] ast::Step       parseLetStep();
    [[nodiscard]] ast::Step       parseTakeStep();
    [[nodiscard]] ast::Step       parseObtainStep();
    [[nodiscard]] ast::Step       parseSupposeStep();
    [[nodiscard]] ast::Step       parseHaveStep();
    [[nodiscard]] ast::Step       parseThenStep();
    [[nodiscard]] ast::Step       parseContradictionStep();
    [[nodiscard]] ast::Step       parseCasesStep();

    // Expressions (arithmetic, precedence climbing)
    // Grammar:  expr      = lambda | condExpr | aggregate | exprAdd
    //           lambda    = ("fun" | "λ") id [":" type] ("=>" | ",") expr
    //           condExpr  = "if" prop "then" expr "else" expr
    //           aggregate = ("sum"|"∑"|"prod"|"∏") id (":" type | rel expr) "," expr
    //           exprAdd   = exprMul { ("+" | "-" | "union" | "∪" | "setminus" | "\") exprMul }
    //           exprMul   = exprUnary { ("*" | "/" | "div" | "mod" | "compose" | "circ" | "∘" | "inter" | "∩") exprUnary }
    //           exprUnary = ["-"] exprPow | "inv" exprPow | "compl" exprPow   (→ ExprCall{…})
    //           exprPow   = exprAtom [ "^" exprUnary ]  (right-associative)
    //           exprAtom  = base { "[" expr "]" | "!" }  (postfix, left-assoc)
    //           base = number
    //                | identifier ["(" argList ")"]
    //                | "|" expr "|"
    //                | "⌊" expr "⌋"  (→ floor(expr))
    //                | "⌈" expr "⌉"  (→ ceil(expr))
    //                | "(" expr ")"                                (grouping)
    //                | "(" expr "," expr {"," expr} ")"            (tuple)
    //                | "{" "}"                                     (empty set)
    //                | "{" expr {"," expr} "}"                     (set literal)
    //                | "{" id [":" type] "|" prop "}"              (set comprehension)
    [[nodiscard]] ast::Expr parseExpr();
    [[nodiscard]] ast::Expr parseLambda();
    [[nodiscard]] ast::Expr parseCondExpr();
    [[nodiscard]] ast::Expr parseAggregate();
    [[nodiscard]] ast::Expr parseExprMul();
    [[nodiscard]] ast::Expr parseExprUnary();
    [[nodiscard]] ast::Expr parseExprPow();
    [[nodiscard]] ast::Expr parseExprAtom();
    [[nodiscard]] ast::Expr parseSetExpr();
    [[nodiscard]] std::vector<ast::ExprPtr> parseArgList();

    // Propositions (precedence climbing)
    [[nodiscard]] ast::Prop parseProp();
    [[nodiscard]] ast::Prop parseQuantifier();
    [[nodiscard]] ast::Prop parseBiconditional();
    [[nodiscard]] ast::Prop parseImplication();
    [[nodiscard]] ast::Prop parseDisjunction();
    [[nodiscard]] ast::Prop parseConjunction();
    [[nodiscard]] ast::Prop parseNegation();
    [[nodiscard]] ast::Prop parseAtomicProp();

    // Justification refs
    [[nodiscard]] std::vector<std::string> parseJustification();

    // Source range helper: records peek().loc as end_loc on the node just returned.
    // Call immediately before every `return` that constructs a new Expr or Prop.
    void mark_end(ast::Expr& e) const noexcept { e.end_loc = peek().loc; }
    void mark_end(ast::Prop& p) const noexcept { p.end_loc = peek().loc; }

    // Token stream helpers
    [[nodiscard]] const lexer::Token& peek() const noexcept;
    const lexer::Token& advance() noexcept;
    bool expect(lexer::TokenKind kind, std::string_view msg);
    [[nodiscard]] bool check(lexer::TokenKind kind) const noexcept;
    [[nodiscard]] bool isAtEnd() const noexcept;
    void consumeArticle();
    void syncToDeclaration(); // skip to next top-level keyword after a parse error

    std::span<const lexer::Token> tokens_;
    diag::DiagnosticEngine&       diag_;
    std::size_t                   pos_{0};
};

} // namespace forall::parser
