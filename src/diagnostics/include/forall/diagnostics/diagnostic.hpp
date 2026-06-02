#pragma once
#include <forall/diagnostics/source_location.hpp>
#include <string>
#include <vector>

namespace forall::diag {

enum class Severity { Error, Warning, Note };

struct Diagnostic {
    Severity       severity;
    SourceLocation loc;
    std::string    message;
    std::uint32_t  end_col{0}; // 0 = unknown; >0 = column of last char + 1 (exclusive)
};

class DiagnosticEngine {
public:
    struct Checkpoint {
        std::size_t size;
        bool        had_errors;
    };

    void emit(Diagnostic d);

    [[nodiscard]] bool hasErrors() const noexcept { return hasErrors_; }
    [[nodiscard]] const std::vector<Diagnostic>& diagnostics() const noexcept { return diagnostics_; }

    // Speculative-parse support: save the current diagnostic state, then either
    // commit (just drop the checkpoint) or rollback to erase any emitted diagnostics.
    [[nodiscard]] Checkpoint save() const noexcept {
        return {diagnostics_.size(), hasErrors_};
    }
    void rollback(Checkpoint cp) noexcept {
        diagnostics_.resize(cp.size);
        hasErrors_ = cp.had_errors;
    }

private:
    std::vector<Diagnostic> diagnostics_;
    bool hasErrors_{false};
};

} // namespace forall::diag
