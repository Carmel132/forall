#include <forall/ast/node.hpp>

namespace forall::ast {

// ── Expr::operator== ──────────────────────────────────────────────────────────

bool Expr::operator==(const Expr& other) const {
    if (node.index() != other.node.index()) return false;
    return std::visit([&](const auto& x) -> bool {
        using T = std::decay_t<decltype(x)>;
        const auto& y = std::get<T>(other.node);
        if constexpr (std::is_same_v<T, ExprLit>)
            return x.value == y.value;
        else if constexpr (std::is_same_v<T, ExprVar>)
            return x.name == y.name;
        else if constexpr (std::is_same_v<T, ExprBinary>)
            return x.op == y.op && *x.lhs == *y.lhs && *x.rhs == *y.rhs;
        else if constexpr (std::is_same_v<T, ExprUnary>)
            return x.op == y.op && *x.operand == *y.operand;
        else if constexpr (std::is_same_v<T, ExprAbs>)
            return *x.operand == *y.operand;
        else if constexpr (std::is_same_v<T, ExprCall>) {
            if (x.name != y.name || x.args.size() != y.args.size()) return false;
            for (std::size_t i = 0; i < x.args.size(); ++i)
                if (!(*x.args[i] == *y.args[i])) return false;
            return true;
        }
        else if constexpr (std::is_same_v<T, ExprIndex>)
            return *x.array == *y.array && *x.index == *y.index;
        else if constexpr (std::is_same_v<T, ExprTuple>) {
            if (x.elements.size() != y.elements.size()) return false;
            for (std::size_t i = 0; i < x.elements.size(); ++i)
                if (!(*x.elements[i] == *y.elements[i])) return false;
            return true;
        }
        else if constexpr (std::is_same_v<T, ExprLambda>)
            return x.var == y.var && x.type == y.type && *x.body == *y.body;
        else if constexpr (std::is_same_v<T, ExprIf>)
            return *x.cond == *y.cond && *x.then_ == *y.then_ && *x.else_ == *y.else_;
        else if constexpr (std::is_same_v<T, ExprAgg>) {
            if (x.op != y.op || x.var != y.var || x.type != y.type || x.rel != y.rel)
                return false;
            const bool lb = x.bound.has_value(), rb = y.bound.has_value();
            if (lb != rb) return false;
            if (lb && !(**x.bound == **y.bound)) return false;
            return *x.body == *y.body;
        }
        else if constexpr (std::is_same_v<T, ExprSetLit>) {
            if (x.elements.size() != y.elements.size()) return false;
            for (std::size_t i = 0; i < x.elements.size(); ++i)
                if (!(*x.elements[i] == *y.elements[i])) return false;
            return true;
        }
        else if constexpr (std::is_same_v<T, ExprSetCompr>)
            return x.var == y.var && x.type == y.type && *x.pred == *y.pred;
        else return false; // unreachable — all ExprNode alternatives are listed above
    }, node);
}

// ── Prop::operator== ──────────────────────────────────────────────────────────

bool Prop::operator==(const Prop& other) const {
    if (node.index() != other.node.index()) return false;
    return std::visit([&](const auto& x) -> bool {
        using T = std::decay_t<decltype(x)>;
        const auto& y = std::get<T>(other.node);
        if constexpr (std::is_same_v<T, Atomic>)
            return x.name == y.name;
        else if constexpr (std::is_same_v<T, PropFalse>)
            return true;
        else if constexpr (std::is_same_v<T, PropNot>)
            return *x.inner == *y.inner;
        else if constexpr (std::is_same_v<T, PropForall> || std::is_same_v<T, PropExists>)
            return x.var == y.var && x.type == y.type && *x.body == *y.body;
        else if constexpr (std::is_same_v<T, PropRel>)
            return x.op == y.op && *x.lhs == *y.lhs && *x.rhs == *y.rhs;
        else if constexpr (std::is_same_v<T, PropPred>) {
            if (x.name != y.name || x.args.size() != y.args.size()) return false;
            for (std::size_t i = 0; i < x.args.size(); ++i)
                if (!(*x.args[i] == *y.args[i])) return false;
            return true;
        }
        else if constexpr (std::is_same_v<T, PropAnd> || std::is_same_v<T, PropOr>
                           || std::is_same_v<T, PropImpl>)
            return *x.lhs == *y.lhs && *x.rhs == *y.rhs;
        else return false; // unreachable — all PropNode alternatives are listed above
    }, node);
}

} // namespace forall::ast
