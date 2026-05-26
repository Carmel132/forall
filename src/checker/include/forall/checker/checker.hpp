#pragma once
#include <forall/diagnostics/diagnostic.hpp>
#include <filesystem>

namespace forall::checker {

// Orchestrates the full validation pipeline:
//   read file → lex → parse → kernel validate → emit diagnostics
//
// The Checker bridges the untrusted world (I/O, parser) with the trusted
// kernel. Nothing here is in the trusted base; correctness flows upward
// from the Kernel's invariants.
class Checker {
public:
    explicit Checker(diag::DiagnosticEngine& diag);
    void check(const std::filesystem::path& path);

private:
    diag::DiagnosticEngine& diag_;
};

} // namespace forall::checker
