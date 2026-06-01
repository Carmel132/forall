#pragma once
#include <forall/ast/node.hpp>
#include <string>

namespace forall::formatter {

// Format a complete .forall module as a canonical string.
// Declarations are separated by blank lines; proof blocks are indented 2 spaces.
// Comments are not preserved (the formatter parses to AST first).
std::string format_module(const ast::Module& mod);

// Format a single declaration.
std::string format_decl(const ast::Decl& decl);

} // namespace forall::formatter
