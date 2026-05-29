#include <forall/ast/node.hpp>

#include <algorithm>

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

// ── free_vars implementation ───────────────────────────────────────────────────

static void collect_fv_expr(const Expr& expr, std::set<std::string>& out);
static void collect_fv_prop(const Prop& prop, std::set<std::string>& out);

static void collect_fv_expr(const Expr& expr, std::set<std::string>& out) {
    std::visit([&](const auto& e) {
        using T = std::decay_t<decltype(e)>;
        if constexpr (std::is_same_v<T, ExprLit>) {
            // no variables
        } else if constexpr (std::is_same_v<T, ExprVar>) {
            out.insert(e.name);
        } else if constexpr (std::is_same_v<T, ExprBinary>) {
            collect_fv_expr(*e.lhs, out); collect_fv_expr(*e.rhs, out);
        } else if constexpr (std::is_same_v<T, ExprUnary>) {
            collect_fv_expr(*e.operand, out);
        } else if constexpr (std::is_same_v<T, ExprAbs>) {
            collect_fv_expr(*e.operand, out);
        } else if constexpr (std::is_same_v<T, ExprCall>) {
            for (const auto& a : e.args) collect_fv_expr(*a, out);
        } else if constexpr (std::is_same_v<T, ExprIndex>) {
            collect_fv_expr(*e.array, out); collect_fv_expr(*e.index, out);
        } else if constexpr (std::is_same_v<T, ExprTuple>) {
            for (const auto& el : e.elements) collect_fv_expr(*el, out);
        } else if constexpr (std::is_same_v<T, ExprSetLit>) {
            for (const auto& el : e.elements) collect_fv_expr(*el, out);
        } else if constexpr (std::is_same_v<T, ExprSetCompr>) {
            // var is bound in pred; collect inner free vars then remove binder
            std::set<std::string> inner;
            collect_fv_prop(*e.pred, inner);
            inner.erase(e.var);
            out.insert(inner.begin(), inner.end());
        } else if constexpr (std::is_same_v<T, ExprLambda>) {
            std::set<std::string> inner;
            collect_fv_expr(*e.body, inner);
            inner.erase(e.var);
            out.insert(inner.begin(), inner.end());
        } else if constexpr (std::is_same_v<T, ExprIf>) {
            collect_fv_prop(*e.cond, out);
            collect_fv_expr(*e.then_, out);
            collect_fv_expr(*e.else_, out);
        } else if constexpr (std::is_same_v<T, ExprAgg>) {
            // bound expression is in the outer scope
            if (e.bound) collect_fv_expr(**e.bound, out);
            // var is bound in body
            std::set<std::string> inner;
            collect_fv_expr(*e.body, inner);
            inner.erase(e.var);
            out.insert(inner.begin(), inner.end());
        }
    }, expr.node);
}

static void collect_fv_prop(const Prop& prop, std::set<std::string>& out) {
    std::visit([&](const auto& p) {
        using T = std::decay_t<decltype(p)>;
        if constexpr (std::is_same_v<T, Atomic> || std::is_same_v<T, PropFalse>) {
            // no term variables
        } else if constexpr (std::is_same_v<T, PropNot>) {
            collect_fv_prop(*p.inner, out);
        } else if constexpr (std::is_same_v<T, PropAnd> ||
                             std::is_same_v<T, PropOr>  ||
                             std::is_same_v<T, PropImpl>) {
            collect_fv_prop(*p.lhs, out); collect_fv_prop(*p.rhs, out);
        } else if constexpr (std::is_same_v<T, PropForall> ||
                             std::is_same_v<T, PropExists>) {
            std::set<std::string> inner;
            collect_fv_prop(*p.body, inner);
            inner.erase(p.var);
            out.insert(inner.begin(), inner.end());
        } else if constexpr (std::is_same_v<T, PropRel>) {
            collect_fv_expr(*p.lhs, out); collect_fv_expr(*p.rhs, out);
        } else if constexpr (std::is_same_v<T, PropPred>) {
            for (const auto& a : p.args) collect_fv_expr(*a, out);
        }
    }, prop.node);
}

std::set<std::string> free_vars(const Prop& prop) {
    std::set<std::string> out;
    collect_fv_prop(prop, out);
    return out;
}

std::set<std::string> free_vars(const Expr& expr) {
    std::set<std::string> out;
    collect_fv_expr(expr, out);
    return out;
}

// ── subst implementation ───────────────────────────────────────────────────────

static Prop subst_prop(const Prop& prop, const std::string& var, const Expr& r);
static Expr subst_expr(const Expr& expr, const std::string& var, const Expr& r);

static Expr subst_expr(const Expr& expr, const std::string& var, const Expr& r) {
    return std::visit([&](const auto& e) -> Expr {
        using T = std::decay_t<decltype(e)>;
        const auto& loc = expr.loc;

        if constexpr (std::is_same_v<T, ExprLit>) {
            return expr;
        } else if constexpr (std::is_same_v<T, ExprVar>) {
            return e.name == var ? r : expr;
        } else if constexpr (std::is_same_v<T, ExprBinary>) {
            return Expr{loc, ExprBinary{e.op,
                make_expr(subst_expr(*e.lhs, var, r)),
                make_expr(subst_expr(*e.rhs, var, r))}};
        } else if constexpr (std::is_same_v<T, ExprUnary>) {
            return Expr{loc, ExprUnary{e.op,
                make_expr(subst_expr(*e.operand, var, r))}};
        } else if constexpr (std::is_same_v<T, ExprAbs>) {
            return Expr{loc, ExprAbs{make_expr(subst_expr(*e.operand, var, r))}};
        } else if constexpr (std::is_same_v<T, ExprCall>) {
            std::vector<ExprPtr> args;
            args.reserve(e.args.size());
            for (const auto& a : e.args)
                args.push_back(make_expr(subst_expr(*a, var, r)));
            return Expr{loc, ExprCall{e.name, std::move(args)}};
        } else if constexpr (std::is_same_v<T, ExprIndex>) {
            return Expr{loc, ExprIndex{
                make_expr(subst_expr(*e.array, var, r)),
                make_expr(subst_expr(*e.index, var, r))}};
        } else if constexpr (std::is_same_v<T, ExprTuple>) {
            std::vector<ExprPtr> elems;
            elems.reserve(e.elements.size());
            for (const auto& el : e.elements)
                elems.push_back(make_expr(subst_expr(*el, var, r)));
            return Expr{loc, ExprTuple{std::move(elems)}};
        } else if constexpr (std::is_same_v<T, ExprSetLit>) {
            std::vector<ExprPtr> elems;
            elems.reserve(e.elements.size());
            for (const auto& el : e.elements)
                elems.push_back(make_expr(subst_expr(*el, var, r)));
            return Expr{loc, ExprSetLit{std::move(elems)}};
        } else if constexpr (std::is_same_v<T, ExprSetCompr>) {
            if (e.var == var) return expr; // binder shadows var
            return Expr{loc, ExprSetCompr{e.var, e.type,
                make_prop(subst_prop(*e.pred, var, r))}};
        } else if constexpr (std::is_same_v<T, ExprLambda>) {
            if (e.var == var) return expr; // binder shadows var
            return Expr{loc, ExprLambda{e.var, e.type,
                make_expr(subst_expr(*e.body, var, r))}};
        } else if constexpr (std::is_same_v<T, ExprIf>) {
            return Expr{loc, ExprIf{
                make_prop(subst_prop(*e.cond, var, r)),
                make_expr(subst_expr(*e.then_, var, r)),
                make_expr(subst_expr(*e.else_, var, r))}};
        } else if constexpr (std::is_same_v<T, ExprAgg>) {
            // bound expression is in the outer scope; always substitute
            std::optional<ExprPtr> new_bound;
            if (e.bound) new_bound = make_expr(subst_expr(**e.bound, var, r));
            if (e.var == var) {
                // binder shadows var inside the body
                return Expr{loc, ExprAgg{e.op, e.var, e.type, e.rel,
                    std::move(new_bound), e.body}};
            }
            return Expr{loc, ExprAgg{e.op, e.var, e.type, e.rel,
                std::move(new_bound),
                make_expr(subst_expr(*e.body, var, r))}};
        }
        return expr; // unreachable — all ExprNode alternatives listed above
    }, expr.node);
}

static Prop subst_prop(const Prop& prop, const std::string& var, const Expr& r) {
    return std::visit([&](const auto& p) -> Prop {
        using T = std::decay_t<decltype(p)>;
        const auto& loc = prop.loc;

        if constexpr (std::is_same_v<T, Atomic> || std::is_same_v<T, PropFalse>) {
            return prop;
        } else if constexpr (std::is_same_v<T, PropNot>) {
            return Prop{loc, PropNot{make_prop(subst_prop(*p.inner, var, r))}};
        } else if constexpr (std::is_same_v<T, PropAnd>) {
            return Prop{loc, PropAnd{make_prop(subst_prop(*p.lhs, var, r)),
                                     make_prop(subst_prop(*p.rhs, var, r))}};
        } else if constexpr (std::is_same_v<T, PropOr>) {
            return Prop{loc, PropOr{make_prop(subst_prop(*p.lhs, var, r)),
                                    make_prop(subst_prop(*p.rhs, var, r))}};
        } else if constexpr (std::is_same_v<T, PropImpl>) {
            return Prop{loc, PropImpl{make_prop(subst_prop(*p.lhs, var, r)),
                                      make_prop(subst_prop(*p.rhs, var, r))}};
        } else if constexpr (std::is_same_v<T, PropForall>) {
            if (p.var == var) return prop; // binder shadows var
            return Prop{loc, PropForall{p.var, p.type,
                make_prop(subst_prop(*p.body, var, r))}};
        } else if constexpr (std::is_same_v<T, PropExists>) {
            if (p.var == var) return prop; // binder shadows var
            return Prop{loc, PropExists{p.var, p.type,
                make_prop(subst_prop(*p.body, var, r))}};
        } else if constexpr (std::is_same_v<T, PropRel>) {
            return Prop{loc, PropRel{
                make_expr(subst_expr(*p.lhs, var, r)),
                make_expr(subst_expr(*p.rhs, var, r)),
                p.op}};
        } else if constexpr (std::is_same_v<T, PropPred>) {
            std::vector<ExprPtr> args;
            args.reserve(p.args.size());
            for (const auto& a : p.args)
                args.push_back(make_expr(subst_expr(*a, var, r)));
            return Prop{loc, PropPred{p.name, std::move(args)}};
        }
        return prop; // unreachable — all PropNode alternatives listed above
    }, prop.node);
}

Prop subst(const Prop& prop, const std::string& var, const Expr& replacement) {
    return subst_prop(prop, var, replacement);
}

Expr subst(const Expr& expr, const std::string& var, const Expr& replacement) {
    return subst_expr(expr, var, replacement);
}

} // namespace forall::ast
