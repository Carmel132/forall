#include <forall/checker/checker.hpp>
#include <forall/diagnostics/diagnostic.hpp>
#include <forall/formatter/formatter.hpp>
#include <forall/lexer/lexer.hpp>
#include <forall/parser/parser.hpp>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <print>
#include <sstream>
#include <string_view>

namespace fs = std::filesystem;

// ── forall check <file> ──────────────────────────────────────────────────────

static int cmd_check(const fs::path& path) {
    forall::diag::DiagnosticEngine engine;
    forall::checker::Checker checker{engine};
    checker.check(path);

    for (const auto& d : engine.diagnostics()) {
        const char* sev = [&] {
            switch (d.severity) {
                case forall::diag::Severity::Error:   return "error";
                case forall::diag::Severity::Warning: return "warning";
                case forall::diag::Severity::Note:    return "note";
            }
            return "unknown";
        }();
        std::println("{}:{}:{}: {}: {}", d.loc.file, d.loc.line, d.loc.col, sev, d.message);
    }
    return engine.hasErrors() ? EXIT_FAILURE : EXIT_SUCCESS;
}

// ── forall fmt [--write | --check] <file> ────────────────────────────────────

static int cmd_fmt(bool write_mode, bool check_mode, const fs::path& path) {
    // Read source.
    std::ifstream file{path};
    if (!file) {
        std::println(stderr, "forall fmt: cannot open '{}'", path.string());
        return EXIT_FAILURE;
    }
    std::ostringstream buf;
    buf << file.rdbuf();
    const std::string source = buf.str();

    // Lex + parse.
    forall::diag::DiagnosticEngine diag;
    forall::lexer::Lexer lex{source, path.string(), diag};
    auto tokens = lex.tokenize();
    if (diag.hasErrors()) {
        for (const auto& d : diag.diagnostics())
            std::println(stderr, "{}:{}:{}: error: {}", d.loc.file, d.loc.line, d.loc.col, d.message);
        return EXIT_FAILURE;
    }

    forall::parser::Parser parser{tokens, diag};
    auto mod = parser.parse();
    mod.path = path.string();
    if (diag.hasErrors()) {
        for (const auto& d : diag.diagnostics())
            std::println(stderr, "{}:{}:{}: error: {}", d.loc.file, d.loc.line, d.loc.col, d.message);
        return EXIT_FAILURE;
    }

    const std::string formatted = forall::formatter::format_module(mod);

    if (check_mode) {
        // Exit 1 if the file is not already in canonical form.
        if (source != formatted) {
            std::println(stderr, "{}: not in canonical format (run 'forall fmt --write' to fix)", path.string());
            return EXIT_FAILURE;
        }
        return EXIT_SUCCESS;
    }

    if (write_mode) {
        std::ofstream out{path, std::ios::trunc};
        if (!out) {
            std::println(stderr, "forall fmt: cannot write '{}'", path.string());
            return EXIT_FAILURE;
        }
        out << formatted;
        return EXIT_SUCCESS;
    }

    // Default: print to stdout.
    std::cout << formatted;
    return EXIT_SUCCESS;
}

// ── main ─────────────────────────────────────────────────────────────────────

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::println(stderr, "usage: forall <file.forall>");
        std::println(stderr, "       forall fmt [--write|--check] <file.forall>");
        return EXIT_FAILURE;
    }

    const std::string_view first{argv[1]};

    if (first == "fmt") {
        bool write_mode = false;
        bool check_mode = false;
        int file_arg = 2;

        if (argc >= 4) {
            const std::string_view flag{argv[2]};
            if (flag == "--write") { write_mode = true; file_arg = 3; }
            else if (flag == "--check") { check_mode = true; file_arg = 3; }
        }
        if (file_arg >= argc) {
            std::println(stderr, "usage: forall fmt [--write|--check] <file.forall>");
            return EXIT_FAILURE;
        }
        return cmd_fmt(write_mode, check_mode, fs::path{argv[file_arg]});
    }

    // Default: check mode (backwards-compatible: forall <file>).
    return cmd_check(fs::path{argv[1]});
}
