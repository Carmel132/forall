#include <forall/checker/checker.hpp>
#include <forall/kernel/kernel.hpp>
#include <forall/lexer/lexer.hpp>
#include <forall/parser/parser.hpp>

#include <fstream>
#include <sstream>

namespace forall::checker {

Checker::Checker(diag::DiagnosticEngine& diag) : diag_{diag} {}

void Checker::check(const std::filesystem::path& path) {
    // 1. Read source
    std::ifstream file{path};
    if (!file) {
        diag_.emit({diag::Severity::Error, {}, "cannot open file: " + path.string()});
        return;
    }
    std::ostringstream buf;
    buf << file.rdbuf();

    // 2. Lex
    lexer::Lexer lex{buf.str(), path.string(), diag_};
    auto tokens = lex.tokenize();
    if (diag_.hasErrors()) return;

    // 3. Parse
    parser::Parser parser{tokens, diag_};
    ast::Module mod = parser.parse();
    mod.path = path.string();
    if (diag_.hasErrors()) return;

    // 4. Kernel validation
    kernel::Kernel kernel;
    for (const auto& decl : mod.decls) {
        if (decl->kind == ast::DeclKind::Axiom) {
            auto result = kernel.introduce_axiom(decl->statement);
            if (!result)
                diag_.emit({diag::Severity::Error, decl->loc,
                            "invalid axiom: " + result.error().message});
        }
        // TODO: theorem validation requires ast::Prop expression tree and proof step parsing.
    }
}

} // namespace forall::checker
