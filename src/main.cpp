#include <forall/checker/checker.hpp>
#include <forall/diagnostics/diagnostic.hpp>

#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <print>

namespace fs = std::filesystem;

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::println(stderr, "usage: forall <file.forall>");
        return EXIT_FAILURE;
    }

    const fs::path path{argv[1]};
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
