#pragma once
#include <forall/ast/node.hpp>
#include <string>

namespace forall::pretty {

std::string to_string(const ast::Expr& e);
std::string to_string(const ast::Prop& p);

inline std::string to_string(const ast::ExprPtr& e) { return to_string(*e); }
inline std::string to_string(const ast::PropPtr& p) { return to_string(*p); }

} // namespace forall::pretty
