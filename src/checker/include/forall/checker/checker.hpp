#pragma once
#include <forall/diagnostics/diagnostic.hpp>
#include <filesystem>
#include <map>
#include <string>

namespace forall::checker {

// Per-name LSP metadata exposed for hover and go-to-definition.
// prop_text  : pretty-printed proposition string (e.g. "∀ n : Nat, n ≥ 0")
// intro_loc  : source location of the declaration that introduced this name
struct LspEntry {
    std::string          prop_text;
    diag::SourceLocation intro_loc;
};

// Map from declaration name to its LSP metadata.
using LspEnv = std::map<std::string, LspEntry>;

// Orchestrates the full validation pipeline:
//   read file → lex → parse → kernel validate → emit diagnostics
//
// The Checker bridges the untrusted world (I/O, parser) with the trusted
// kernel. Nothing here is in the trusted base; correctness flows upward
// from the Kernel's invariants.
class Checker {
public:
    explicit Checker(diag::DiagnosticEngine& diag);

    // Optional: set the stdlib root directory so that "stdlib/..." imports
    // resolve relative to this path rather than relative to the importing file.
    void set_stdlib_path(const std::filesystem::path& stdlib_root);

    void check(const std::filesystem::path& path);

    // Check source content from a string buffer (for LSP in-memory validation).
    void check_content(const std::string& source, const std::string& filename);

    // Like check_content but also returns LSP metadata (hover + go-to-definition).
    // The returned LspEnv maps every module-level declaration name to its
    // pretty-printed proposition and introduction source location.
    [[nodiscard]] LspEnv check_content_lsp(const std::string& source,
                                           const std::string& filename);

private:
    diag::DiagnosticEngine&  diag_;
    std::filesystem::path    stdlib_root_; // empty = use file-relative resolution
};

} // namespace forall::checker
