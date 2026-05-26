#pragma once
#include <cstdint>
#include <string>

namespace forall::diag {

struct SourceLocation {
    std::string   file;
    std::uint32_t line{1};
    std::uint32_t col{1};

    [[nodiscard]] static SourceLocation unknown() { return {}; }
};

} // namespace forall::diag
