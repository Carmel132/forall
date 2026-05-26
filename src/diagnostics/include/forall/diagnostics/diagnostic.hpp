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
};

class DiagnosticEngine {
public:
    void emit(Diagnostic d);

    [[nodiscard]] bool hasErrors() const noexcept { return hasErrors_; }
    [[nodiscard]] const std::vector<Diagnostic>& diagnostics() const noexcept { return diagnostics_; }

private:
    std::vector<Diagnostic> diagnostics_;
    bool hasErrors_{false};
};

} // namespace forall::diag
