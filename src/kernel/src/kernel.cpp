#include <forall/kernel/kernel.hpp>

namespace forall::kernel {

std::expected<Judgment, KernelError>
Kernel::apply(Rule rule, std::span<const Judgment> /*premises*/, const ast::Prop& conclusion) {
    // TODO: verify premises match the rule's required shape once ast::Prop is
    // a structural expression tree (e.g. AndElimL needs one premise of "A ∧ B").
    (void)rule;
    return make(conclusion);
}

std::expected<Judgment, KernelError>
Kernel::introduce_axiom(const ast::Prop& prop) {
    return make(prop);
}

} // namespace forall::kernel
