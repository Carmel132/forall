#pragma once
#include <forall/kernel/judgment.hpp>
#include <forall/kernel/rule.hpp>
#include <forall/ast/node.hpp>

#include <expected>
#include <span>
#include <string>

namespace forall::kernel {

struct KernelError {
    Rule        rule_attempted;
    std::string message;
};

// The trusted core of the proof system.
//
// Design constraints (must never be relaxed):
//   1. This is the ONLY class that constructs Judgment values.
//   2. It must never depend on forall::lexer or forall::parser.
//   3. Every public method is const-correct and stateless where possible.
//   4. Keep this class small. Automation and tactics live elsewhere.
//
// TODO: premise shape verification requires ast::Prop to be a structural
// expression tree rather than a raw string.
class Kernel {
public:
    // Apply a named inference rule to zero or more premise judgments.
    // Returns a new Judgment if valid; KernelError if the application is ill-formed.
    [[nodiscard]] std::expected<Judgment, KernelError>
    apply(Rule rule, std::span<const Judgment> premises, const ast::Prop& conclusion);

    // Introduce an axiom: produces a Judgment with no premises.
    [[nodiscard]] std::expected<Judgment, KernelError>
    introduce_axiom(const ast::Prop& prop);

private:
    [[nodiscard]] Judgment make(ast::Prop p) const { return Judgment{std::move(p)}; }
};

} // namespace forall::kernel
