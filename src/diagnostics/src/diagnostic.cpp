#include <forall/diagnostics/diagnostic.hpp>

namespace forall::diag {

void DiagnosticEngine::emit(Diagnostic d) {
    if (d.severity == Severity::Error)
        hasErrors_ = true;
    diagnostics_.push_back(std::move(d));
}

} // namespace forall::diag
