#pragma once
#include <forall/ast/node.hpp>

namespace forall::kernel {

class Kernel;

// A Judgment is the kernel's certificate that a proposition has been proved.
//
// The central trust invariant: ONLY the Kernel can construct a Judgment.
// All constructors are private; Kernel is the sole friend. This is the
// "abstract type" trick from the LCF tradition (1979) — the trusted core
// is defined as exactly the code that can create values of this type.
//
// Code outside the kernel can hold, copy, and inspect judgments, but it
// cannot forge one. This means any Judgment in the system is genuinely proved.
//
// Carries only the proved Prop; a proof term (derivation tree) can be added
// here to enable independent re-verification and proof export.
struct Judgment {
    [[nodiscard]] const ast::Prop& prop() const noexcept { return prop_; }

private:
    friend class Kernel;
    explicit Judgment(ast::Prop p) : prop_{std::move(p)} {}

    ast::Prop prop_;
};

} // namespace forall::kernel
