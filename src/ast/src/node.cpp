#include <forall/ast/node.hpp>

#include <algorithm>

namespace forall::ast {

// ── FieldAxiom equality ────────────────────────────────────────────────────────

bool FieldAxiom::operator==(const FieldAxiom& o) const {
    return name == o.name && prop == o.prop;
}

// ── TypeNode equality (recursive, defined here where all types are complete) ──

bool TypeFun::operator==(const TypeFun& o) const {
    return *domain == *o.domain && *codomain == *o.codomain;
}

bool TypeTuple::operator==(const TypeTuple& o) const {
    if (elements.size() != o.elements.size()) return false;
    for (std::size_t i = 0; i < elements.size(); ++i)
        if (!(*elements[i] == *o.elements[i])) return false;
    return true;
}

bool TypeSet::operator==(const TypeSet& o) const {
    return *element_type == *o.element_type;
}

bool TypePi::operator==(const TypePi& o) const {
    return var == o.var && *domain == *o.domain && *codomain == *o.codomain;
}

bool TypeNode::operator==(const TypeNode& o) const {
    return node == o.node;
}

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
        else if constexpr (std::is_same_v<T, ExprApp>) {
            if (*x.func != *y.func || x.args.size() != y.args.size()) return false;
            for (std::size_t i = 0; i < x.args.size(); ++i)
                if (!(*x.args[i] == *y.args[i])) return false;
            return true;
        }
        else if constexpr (std::is_same_v<T, ExprField>)
            return x.field_name == y.field_name && *x.base == *y.base;
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
        else if constexpr (std::is_same_v<T, PropFalse> || std::is_same_v<T, PropTrue>)
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
        } else if constexpr (std::is_same_v<T, ExprApp>) {
            collect_fv_expr(*e.func, out);
            for (const auto& a : e.args) collect_fv_expr(*a, out);
        } else if constexpr (std::is_same_v<T, ExprField>) {
            collect_fv_expr(*e.base, out);
        }
    }, expr.node);
}

static void collect_fv_prop(const Prop& prop, std::set<std::string>& out) {
    std::visit([&](const auto& p) {
        using T = std::decay_t<decltype(p)>;
        if constexpr (std::is_same_v<T, Atomic> || std::is_same_v<T, PropFalse>
                                                 || std::is_same_v<T, PropTrue>) {
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
            // First substitute into args.
            std::vector<ExprPtr> args;
            args.reserve(e.args.size());
            for (const auto& a : e.args)
                args.push_back(make_expr(subst_expr(*a, var, r)));
            // If the function name is the variable being substituted and the
            // replacement is a lambda, we have a beta-redex.  Convert to ExprApp
            // so that beta_reduce can collapse it.
            if (e.name == var) {
                return Expr{loc, ExprApp{make_expr(r), std::move(args)}};
            }
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
        } else if constexpr (std::is_same_v<T, ExprApp>) {
            std::vector<ExprPtr> args;
            args.reserve(e.args.size());
            for (const auto& a : e.args)
                args.push_back(make_expr(subst_expr(*a, var, r)));
            return Expr{loc, ExprApp{
                make_expr(subst_expr(*e.func, var, r)),
                std::move(args)}};
        } else if constexpr (std::is_same_v<T, ExprField>) {
            return Expr{loc, ExprField{
                make_expr(subst_expr(*e.base, var, r)),
                e.field_name}};
        }
        return expr; // unreachable — all ExprNode alternatives listed above
    }, expr.node);
}

static Prop subst_prop(const Prop& prop, const std::string& var, const Expr& r) {
    return std::visit([&](const auto& p) -> Prop {
        using T = std::decay_t<decltype(p)>;
        const auto& loc = prop.loc;

        if constexpr (std::is_same_v<T, Atomic> || std::is_same_v<T, PropFalse>
                                                 || std::is_same_v<T, PropTrue>) {
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

// ── subst_expr (expression-level find-and-replace) ───────────────────────────
//
// Replaces every structurally-equal occurrence of `find` inside a Prop or Expr
// with `replace`.  Structural equality uses operator== (ignores source locs).
// Used by the RewriteStep handler to rewrite e.g. b[k] → a[phi(k)] inside
// absolute value or arithmetic expressions.

static Expr find_replace_e(const Expr& e, const Expr& find, const Expr& replace);
static Prop find_replace_p(const Prop& p, const Expr& find, const Expr& replace);

static Expr find_replace_e(const Expr& e, const Expr& find, const Expr& replace) {
    if (e == find) return replace;
    return std::visit([&](const auto& n) -> Expr {
        using T = std::decay_t<decltype(n)>;
        const auto& loc = e.loc;
        if constexpr (std::is_same_v<T, ExprLit> || std::is_same_v<T, ExprVar>)
            return e;
        else if constexpr (std::is_same_v<T, ExprBinary>)
            return Expr{loc, ExprBinary{n.op,
                make_expr(find_replace_e(*n.lhs, find, replace)),
                make_expr(find_replace_e(*n.rhs, find, replace))}};
        else if constexpr (std::is_same_v<T, ExprUnary>)
            return Expr{loc, ExprUnary{n.op, make_expr(find_replace_e(*n.operand, find, replace))}};
        else if constexpr (std::is_same_v<T, ExprAbs>)
            return Expr{loc, ExprAbs{make_expr(find_replace_e(*n.operand, find, replace))}};
        else if constexpr (std::is_same_v<T, ExprCall>) {
            std::vector<ExprPtr> args;
            for (const auto& a : n.args) args.push_back(make_expr(find_replace_e(*a, find, replace)));
            return Expr{loc, ExprCall{n.name, std::move(args)}};
        }
        else if constexpr (std::is_same_v<T, ExprIndex>)
            return Expr{loc, ExprIndex{
                make_expr(find_replace_e(*n.array, find, replace)),
                make_expr(find_replace_e(*n.index, find, replace))}};
        else if constexpr (std::is_same_v<T, ExprTuple>) {
            std::vector<ExprPtr> elems;
            for (const auto& el : n.elements) elems.push_back(make_expr(find_replace_e(*el, find, replace)));
            return Expr{loc, ExprTuple{std::move(elems)}};
        }
        else if constexpr (std::is_same_v<T, ExprSetLit>) {
            std::vector<ExprPtr> elems;
            for (const auto& el : n.elements) elems.push_back(make_expr(find_replace_e(*el, find, replace)));
            return Expr{loc, ExprSetLit{std::move(elems)}};
        }
        else if constexpr (std::is_same_v<T, ExprSetCompr>)
            return Expr{loc, ExprSetCompr{n.var, n.type,
                make_prop(find_replace_p(*n.pred, find, replace))}};
        else if constexpr (std::is_same_v<T, ExprLambda>)
            return Expr{loc, ExprLambda{n.var, n.type,
                make_expr(find_replace_e(*n.body, find, replace))}};
        else if constexpr (std::is_same_v<T, ExprIf>)
            return Expr{loc, ExprIf{
                make_prop(find_replace_p(*n.cond, find, replace)),
                make_expr(find_replace_e(*n.then_, find, replace)),
                make_expr(find_replace_e(*n.else_, find, replace))}};
        else if constexpr (std::is_same_v<T, ExprAgg>)
            return Expr{loc, ExprAgg{n.op, n.var, n.type, n.rel, n.bound,
                make_expr(find_replace_e(*n.body, find, replace))}};
        else if constexpr (std::is_same_v<T, ExprApp>) {
            std::vector<ExprPtr> args;
            for (const auto& a : n.args) args.push_back(make_expr(find_replace_e(*a, find, replace)));
            return Expr{loc, ExprApp{make_expr(find_replace_e(*n.func, find, replace)), std::move(args)}};
        }
        else if constexpr (std::is_same_v<T, ExprField>)
            return Expr{loc, ExprField{make_expr(find_replace_e(*n.base, find, replace)), n.field_name}};
        else
            return e;
    }, e.node);
}

static Prop find_replace_p(const Prop& p, const Expr& find, const Expr& replace) {
    return std::visit([&](const auto& n) -> Prop {
        using T = std::decay_t<decltype(n)>;
        const auto& loc = p.loc;
        if constexpr (std::is_same_v<T, Atomic> || std::is_same_v<T, PropFalse> || std::is_same_v<T, PropTrue>)
            return p;
        else if constexpr (std::is_same_v<T, PropNot>)
            return Prop{loc, PropNot{make_prop(find_replace_p(*n.inner, find, replace))}};
        else if constexpr (std::is_same_v<T, PropAnd>)
            return Prop{loc, PropAnd{make_prop(find_replace_p(*n.lhs, find, replace)),
                                     make_prop(find_replace_p(*n.rhs, find, replace))}};
        else if constexpr (std::is_same_v<T, PropOr>)
            return Prop{loc, PropOr{make_prop(find_replace_p(*n.lhs, find, replace)),
                                    make_prop(find_replace_p(*n.rhs, find, replace))}};
        else if constexpr (std::is_same_v<T, PropImpl>)
            return Prop{loc, PropImpl{make_prop(find_replace_p(*n.lhs, find, replace)),
                                      make_prop(find_replace_p(*n.rhs, find, replace))}};
        else if constexpr (std::is_same_v<T, PropForall>)
            return Prop{loc, PropForall{n.var, n.type, make_prop(find_replace_p(*n.body, find, replace))}};
        else if constexpr (std::is_same_v<T, PropExists>)
            return Prop{loc, PropExists{n.var, n.type, make_prop(find_replace_p(*n.body, find, replace))}};
        else if constexpr (std::is_same_v<T, PropRel>)
            return Prop{loc, PropRel{
                make_expr(find_replace_e(*n.lhs, find, replace)),
                make_expr(find_replace_e(*n.rhs, find, replace)),
                n.op}};
        else if constexpr (std::is_same_v<T, PropPred>) {
            std::vector<ExprPtr> args;
            for (const auto& a : n.args) args.push_back(make_expr(find_replace_e(*a, find, replace)));
            return Prop{loc, PropPred{n.name, std::move(args)}};
        }
        else
            return p;
    }, p.node);
}

Prop subst_expr(const Prop& prop, const Expr& find, const Expr& replace) {
    return find_replace_p(prop, find, replace);
}

// ── subst_prop: proposition-level find-and-replace ───────────────────────────

static Prop find_replace_pp(const Prop& p, const Prop& find, const Prop& replace);

static Prop find_replace_pp(const Prop& p, const Prop& find, const Prop& replace) {
    if (p == find) return replace;
    return std::visit([&](const auto& n) -> Prop {
        using T = std::decay_t<decltype(n)>;
        const auto& loc = p.loc;
        if constexpr (std::is_same_v<T, Atomic> || std::is_same_v<T, PropFalse>
                   || std::is_same_v<T, PropTrue>)
            return p;
        else if constexpr (std::is_same_v<T, PropNot>)
            return Prop{loc, PropNot{make_prop(find_replace_pp(*n.inner, find, replace))}};
        else if constexpr (std::is_same_v<T, PropAnd>)
            return Prop{loc, PropAnd{make_prop(find_replace_pp(*n.lhs, find, replace)),
                                     make_prop(find_replace_pp(*n.rhs, find, replace))}};
        else if constexpr (std::is_same_v<T, PropOr>)
            return Prop{loc, PropOr{make_prop(find_replace_pp(*n.lhs, find, replace)),
                                    make_prop(find_replace_pp(*n.rhs, find, replace))}};
        else if constexpr (std::is_same_v<T, PropImpl>)
            return Prop{loc, PropImpl{make_prop(find_replace_pp(*n.lhs, find, replace)),
                                      make_prop(find_replace_pp(*n.rhs, find, replace))}};
        else if constexpr (std::is_same_v<T, PropForall>)
            return Prop{loc, PropForall{n.var, n.type,
                make_prop(find_replace_pp(*n.body, find, replace))}};
        else if constexpr (std::is_same_v<T, PropExists>)
            return Prop{loc, PropExists{n.var, n.type,
                make_prop(find_replace_pp(*n.body, find, replace))}};
        else
            return p; // PropRel, PropPred — no Prop sub-trees to recurse into
    }, p.node);
}

Prop subst_prop(const Prop& prop, const Prop& find, const Prop& replace) {
    return find_replace_pp(prop, find, replace);
}

Expr subst_expr(const Expr& expr, const Expr& find, const Expr& replace) {
    return find_replace_e(expr, find, replace);
}

// ── beta_reduce implementation ────────────────────────────────────────────────
//
// Reduces ExprApp{ExprLambda{x, t, body}, [arg0, arg1, ...]}:
//   1. substitute arg0 for x in body  → reduced_body
//   2. if remaining args, wrap as ExprApp{reduced_body, [arg1, ...]} and recurse
//   3. otherwise return beta_reduce(reduced_body)
//
// After handling ExprApp, recurse into all subexpressions of all other variants.

static Expr beta_reduce_expr(const Expr& e);
static Prop beta_reduce_prop(const Prop& p);

static Expr beta_reduce_expr(const Expr& e) {
    return std::visit([&](const auto& n) -> Expr {
        using T = std::decay_t<decltype(n)>;
        const auto& loc = e.loc;

        if constexpr (std::is_same_v<T, ExprLit> || std::is_same_v<T, ExprVar>) {
            return e;
        } else if constexpr (std::is_same_v<T, ExprBinary>) {
            return Expr{loc, ExprBinary{n.op,
                make_expr(beta_reduce_expr(*n.lhs)),
                make_expr(beta_reduce_expr(*n.rhs))}};
        } else if constexpr (std::is_same_v<T, ExprUnary>) {
            return Expr{loc, ExprUnary{n.op,
                make_expr(beta_reduce_expr(*n.operand))}};
        } else if constexpr (std::is_same_v<T, ExprAbs>) {
            return Expr{loc, ExprAbs{make_expr(beta_reduce_expr(*n.operand))}};
        } else if constexpr (std::is_same_v<T, ExprCall>) {
            std::vector<ExprPtr> args;
            args.reserve(n.args.size());
            for (const auto& a : n.args)
                args.push_back(make_expr(beta_reduce_expr(*a)));
            return Expr{loc, ExprCall{n.name, std::move(args)}};
        } else if constexpr (std::is_same_v<T, ExprIndex>) {
            return Expr{loc, ExprIndex{
                make_expr(beta_reduce_expr(*n.array)),
                make_expr(beta_reduce_expr(*n.index))}};
        } else if constexpr (std::is_same_v<T, ExprTuple>) {
            std::vector<ExprPtr> elems;
            elems.reserve(n.elements.size());
            for (const auto& el : n.elements)
                elems.push_back(make_expr(beta_reduce_expr(*el)));
            return Expr{loc, ExprTuple{std::move(elems)}};
        } else if constexpr (std::is_same_v<T, ExprSetLit>) {
            std::vector<ExprPtr> elems;
            elems.reserve(n.elements.size());
            for (const auto& el : n.elements)
                elems.push_back(make_expr(beta_reduce_expr(*el)));
            return Expr{loc, ExprSetLit{std::move(elems)}};
        } else if constexpr (std::is_same_v<T, ExprSetCompr>) {
            // Do not reduce into the binder body without proper substitution;
            // but the pred is a Prop so we can reduce its Expr leaves.
            return Expr{loc, ExprSetCompr{n.var, n.type,
                make_prop(beta_reduce_prop(*n.pred))}};
        } else if constexpr (std::is_same_v<T, ExprLambda>) {
            // Recurse into the body but do not treat the whole lambda as a redex.
            return Expr{loc, ExprLambda{n.var, n.type,
                make_expr(beta_reduce_expr(*n.body))}};
        } else if constexpr (std::is_same_v<T, ExprIf>) {
            return Expr{loc, ExprIf{
                make_prop(beta_reduce_prop(*n.cond)),
                make_expr(beta_reduce_expr(*n.then_)),
                make_expr(beta_reduce_expr(*n.else_))}};
        } else if constexpr (std::is_same_v<T, ExprAgg>) {
            std::optional<ExprPtr> new_bound;
            if (n.bound) new_bound = make_expr(beta_reduce_expr(**n.bound));
            return Expr{loc, ExprAgg{n.op, n.var, n.type, n.rel,
                std::move(new_bound),
                make_expr(beta_reduce_expr(*n.body))}};
        } else if constexpr (std::is_same_v<T, ExprApp>) {
            // Reduce the function and args first.
            Expr func_reduced = beta_reduce_expr(*n.func);
            std::vector<ExprPtr> args_reduced;
            args_reduced.reserve(n.args.size());
            for (const auto& a : n.args)
                args_reduced.push_back(make_expr(beta_reduce_expr(*a)));

            // If the function reduces to a lambda, apply it.
            const ExprLambda* lam = std::get_if<ExprLambda>(&func_reduced.node);
            if (lam && !args_reduced.empty()) {
                // Consume the first argument via substitution.
                Expr body_subst = subst(*lam->body, lam->var, *args_reduced[0]);
                if (args_reduced.size() == 1) {
                    // All args consumed — reduce the substituted body.
                    return beta_reduce_expr(body_subst);
                }
                // Remaining args: wrap in a new ExprApp and reduce again.
                std::vector<ExprPtr> remaining(args_reduced.begin() + 1,
                                               args_reduced.end());
                Expr next{loc, ExprApp{make_expr(body_subst), std::move(remaining)}};
                return beta_reduce_expr(next);
            }
            // If the function reduces to a plain variable, collapse to ExprCall so
            // that  subst("f", ExprVar{"g"}) applied to f(x)  gives  ExprCall{"g",[x]}
            // rather than the stuck ExprApp{ExprVar{"g"},[x]}.
            if (const auto* fv = std::get_if<ExprVar>(&func_reduced.node))
                return Expr{loc, ExprCall{fv->name, std::move(args_reduced)}};
            // Function did not reduce to a lambda (or no args) — leave as ExprApp.
            return Expr{loc, ExprApp{make_expr(func_reduced), std::move(args_reduced)}};
        } else if constexpr (std::is_same_v<T, ExprField>) {
            return Expr{loc, ExprField{
                make_expr(beta_reduce_expr(*n.base)),
                n.field_name}};
        }
        return e; // unreachable
    }, e.node);
}

static Prop beta_reduce_prop(const Prop& p) {
    return std::visit([&](const auto& n) -> Prop {
        using T = std::decay_t<decltype(n)>;
        const auto& loc = p.loc;

        if constexpr (std::is_same_v<T, Atomic> || std::is_same_v<T, PropFalse>
                                                 || std::is_same_v<T, PropTrue>) {
            return p;
        } else if constexpr (std::is_same_v<T, PropNot>) {
            return Prop{loc, PropNot{make_prop(beta_reduce_prop(*n.inner))}};
        } else if constexpr (std::is_same_v<T, PropAnd>) {
            return Prop{loc, PropAnd{make_prop(beta_reduce_prop(*n.lhs)),
                                     make_prop(beta_reduce_prop(*n.rhs))}};
        } else if constexpr (std::is_same_v<T, PropOr>) {
            return Prop{loc, PropOr{make_prop(beta_reduce_prop(*n.lhs)),
                                    make_prop(beta_reduce_prop(*n.rhs))}};
        } else if constexpr (std::is_same_v<T, PropImpl>) {
            return Prop{loc, PropImpl{make_prop(beta_reduce_prop(*n.lhs)),
                                      make_prop(beta_reduce_prop(*n.rhs))}};
        } else if constexpr (std::is_same_v<T, PropForall>) {
            return Prop{loc, PropForall{n.var, n.type,
                make_prop(beta_reduce_prop(*n.body))}};
        } else if constexpr (std::is_same_v<T, PropExists>) {
            return Prop{loc, PropExists{n.var, n.type,
                make_prop(beta_reduce_prop(*n.body))}};
        } else if constexpr (std::is_same_v<T, PropRel>) {
            return Prop{loc, PropRel{
                make_expr(beta_reduce_expr(*n.lhs)),
                make_expr(beta_reduce_expr(*n.rhs)),
                n.op}};
        } else if constexpr (std::is_same_v<T, PropPred>) {
            std::vector<ExprPtr> args;
            args.reserve(n.args.size());
            for (const auto& a : n.args)
                args.push_back(make_expr(beta_reduce_expr(*a)));
            return Prop{loc, PropPred{n.name, std::move(args)}};
        }
        return p; // unreachable
    }, p.node);
}

Expr beta_reduce(const Expr& e) { return beta_reduce_expr(e); }
Prop beta_reduce(const Prop& p) { return beta_reduce_prop(p); }

// ── eta_reduce implementation ─────────────────────────────────────────────────
//
// Reduces ExprLambda{x, t, ExprCall{name, args}} where the last arg is
// ExprVar{x} and x does not appear free in ExprCall{name, args_without_last}:
//   fun x => f(a1, a2, x)  →  f(a1, a2)   (if len>1)
//   fun x => f(x)          →  ExprVar{"f"} (if args==[x])
//
// Recurses into all subexpressions.

static Expr eta_reduce_expr(const Expr& e);

static Expr eta_reduce_expr(const Expr& e) {
    return std::visit([&](const auto& n) -> Expr {
        using T = std::decay_t<decltype(n)>;
        const auto& loc = e.loc;

        if constexpr (std::is_same_v<T, ExprLambda>) {
            // First recurse into the body.
            Expr body_reduced = eta_reduce_expr(*n.body);

            // Check for eta-redex: body must be ExprCall{name, [..., ExprVar{x}]}
            if (const auto* call = std::get_if<ExprCall>(&body_reduced.node)) {
                if (!call->args.empty()) {
                    const auto* last_var = std::get_if<ExprVar>(&call->args.back()->node);
                    if (last_var && last_var->name == n.var) {
                        // Build ExprCall without last arg to check free vars.
                        std::vector<ExprPtr> without_last(
                            call->args.begin(),
                            call->args.end() - 1);
                        Expr shorter{loc, ExprCall{call->name, without_last}};
                        // Check that x does not appear free in the shortened call.
                        // free_vars of ExprCall only looks at args, but we also
                        // need to ensure x != call->name (ExprCall name is not
                        // an ExprVar — it is a bare string identifier — but if
                        // call->name == n.var, substituting f(x) where f is a
                        // variable is not a true eta-redex without ExprApp).
                        // We treat call->name as a constant identifier here;
                        // the only free variable concern is in the args.
                        auto fvs = free_vars(shorter);
                        if (fvs.find(n.var) == fvs.end()) {
                            // Eta-reduce.
                            if (without_last.empty()) {
                                // fun x => f(x) → ExprVar{f}
                                return Expr{loc, ExprVar{call->name}};
                            }
                            return shorter;
                        }
                    }
                }
            }
            // No eta-redex or conditions not met; reconstruct with reduced body.
            return Expr{loc, ExprLambda{n.var, n.type, make_expr(body_reduced)}};
        } else if constexpr (std::is_same_v<T, ExprLit> || std::is_same_v<T, ExprVar>) {
            return e;
        } else if constexpr (std::is_same_v<T, ExprBinary>) {
            return Expr{loc, ExprBinary{n.op,
                make_expr(eta_reduce_expr(*n.lhs)),
                make_expr(eta_reduce_expr(*n.rhs))}};
        } else if constexpr (std::is_same_v<T, ExprUnary>) {
            return Expr{loc, ExprUnary{n.op,
                make_expr(eta_reduce_expr(*n.operand))}};
        } else if constexpr (std::is_same_v<T, ExprAbs>) {
            return Expr{loc, ExprAbs{make_expr(eta_reduce_expr(*n.operand))}};
        } else if constexpr (std::is_same_v<T, ExprCall>) {
            std::vector<ExprPtr> args;
            args.reserve(n.args.size());
            for (const auto& a : n.args)
                args.push_back(make_expr(eta_reduce_expr(*a)));
            return Expr{loc, ExprCall{n.name, std::move(args)}};
        } else if constexpr (std::is_same_v<T, ExprIndex>) {
            return Expr{loc, ExprIndex{
                make_expr(eta_reduce_expr(*n.array)),
                make_expr(eta_reduce_expr(*n.index))}};
        } else if constexpr (std::is_same_v<T, ExprTuple>) {
            std::vector<ExprPtr> elems;
            elems.reserve(n.elements.size());
            for (const auto& el : n.elements)
                elems.push_back(make_expr(eta_reduce_expr(*el)));
            return Expr{loc, ExprTuple{std::move(elems)}};
        } else if constexpr (std::is_same_v<T, ExprSetLit>) {
            std::vector<ExprPtr> elems;
            elems.reserve(n.elements.size());
            for (const auto& el : n.elements)
                elems.push_back(make_expr(eta_reduce_expr(*el)));
            return Expr{loc, ExprSetLit{std::move(elems)}};
        } else if constexpr (std::is_same_v<T, ExprSetCompr>) {
            // We don't eta-reduce inside set comprehension predicates via Prop.
            return e;
        } else if constexpr (std::is_same_v<T, ExprIf>) {
            return Expr{loc, ExprIf{n.cond,
                make_expr(eta_reduce_expr(*n.then_)),
                make_expr(eta_reduce_expr(*n.else_))}};
        } else if constexpr (std::is_same_v<T, ExprAgg>) {
            std::optional<ExprPtr> new_bound;
            if (n.bound) new_bound = make_expr(eta_reduce_expr(**n.bound));
            return Expr{loc, ExprAgg{n.op, n.var, n.type, n.rel,
                std::move(new_bound),
                make_expr(eta_reduce_expr(*n.body))}};
        } else if constexpr (std::is_same_v<T, ExprApp>) {
            std::vector<ExprPtr> args;
            args.reserve(n.args.size());
            for (const auto& a : n.args)
                args.push_back(make_expr(eta_reduce_expr(*a)));
            return Expr{loc, ExprApp{
                make_expr(eta_reduce_expr(*n.func)),
                std::move(args)}};
        } else if constexpr (std::is_same_v<T, ExprField>) {
            return Expr{loc, ExprField{
                make_expr(eta_reduce_expr(*n.base)),
                n.field_name}};
        }
        return e; // unreachable
    }, e.node);
}

Expr eta_reduce(const Expr& e) { return eta_reduce_expr(e); }

// ── defn_eq implementation ────────────────────────────────────────────────────

bool defn_eq(const Expr& a, const Expr& b) {
    return beta_reduce(eta_reduce(a)) == beta_reduce(eta_reduce(b));
}

bool defn_eq(const Prop& a, const Prop& b) {
    return beta_reduce(a) == beta_reduce(b);
}

// ── Type inference ─────────────────────────────────────────────────────────────

namespace {

// Numeric widening hierarchy: Nat ≤ Int ≤ Rat ≤ Real.
// Returns the common supertype of two numeric types, or nullopt if either
// is non-numeric (e.g. Prop, TypeFun, TypeUser).
std::optional<TypeNode> numeric_promote(const TypeNode& a, const TypeNode& b) {
    auto rank = [](const TypeNode& t) -> int {
        return std::visit([](const auto& n) -> int {
            using T = std::decay_t<decltype(n)>;
            if constexpr (std::is_same_v<T, TypeNat>)  return 0;
            if constexpr (std::is_same_v<T, TypeInt>)  return 1;
            if constexpr (std::is_same_v<T, TypeRat>)  return 2;
            if constexpr (std::is_same_v<T, TypeReal>) return 3;
            return -1; // non-numeric
        }, t.node);
    };
    int ra = rank(a), rb = rank(b);
    if (ra < 0 || rb < 0) return std::nullopt;
    switch (std::max(ra, rb)) {
        case 0: return TypeNode{TypeNat{}};
        case 1: return TypeNode{TypeInt{}};
        case 2: return TypeNode{TypeRat{}};
        case 3: return TypeNode{TypeReal{}};
        default: return std::nullopt;
    }
}

// Returns the numeric rank of a type (0=Nat, 1=Int, 2=Rat, 3=Real), or -1 if non-numeric.
// Used by numeric subtype coercion checks.
static int numeric_rank(const TypeNode& t) {
    return std::visit([](const auto& n) -> int {
        using T = std::decay_t<decltype(n)>;
        if constexpr (std::is_same_v<T, TypeNat>)  return 0;
        if constexpr (std::is_same_v<T, TypeInt>)  return 1;
        if constexpr (std::is_same_v<T, TypeRat>)  return 2;
        if constexpr (std::is_same_v<T, TypeReal>) return 3;
        return -1;
    }, t.node);
}

// Returns true if `from` can be coerced to `to` via the numeric tower
// (widening only: Nat → Int → Rat → Real).
static bool numeric_coercible(const TypeNode& from, const TypeNode& to) {
    int rf = numeric_rank(from), rt = numeric_rank(to);
    return rf >= 0 && rt >= 0 && rf <= rt;
}

} // anonymous namespace

// Simplified type name for error messages (avoids dependency on pretty::to_string).
static std::string type_name(const TypeNode& t) {
    return std::visit([](const auto& v) -> std::string {
        using T = std::decay_t<decltype(v)>;
        if constexpr (std::is_same_v<T, TypeNat>)   return "Nat";
        if constexpr (std::is_same_v<T, TypeInt>)   return "Int";
        if constexpr (std::is_same_v<T, TypeRat>)   return "Rat";
        if constexpr (std::is_same_v<T, TypeReal>)  return "Real";
        if constexpr (std::is_same_v<T, TypeProp>)  return "Prop";
        if constexpr (std::is_same_v<T, TypeType>)  return "Type";
        if constexpr (std::is_same_v<T, TypeUser>)  return v.name;
        if constexpr (std::is_same_v<T, TypeFun>)   return "function type";
        if constexpr (std::is_same_v<T, TypeTuple>) return "tuple type";
        if constexpr (std::is_same_v<T, TypeSet>)  return "Set " + type_name(*v.element_type);
        if constexpr (std::is_same_v<T, TypePi>)   return "Pi type";
        return "?";
    }, t.node);
}

std::expected<TypeNode, TypeError>
infer_type(const Expr& e, const TypeEnv& env, const FuncSigTable& sigs,
           const StructEnv* struct_env) {
    using Ret = std::expected<TypeNode, TypeError>;
    auto err = [](std::string msg) -> Ret {
        return std::unexpected(TypeError{std::move(msg), TypeErrorKind::Unknown});
    };
    auto mismatch = [](std::string msg) -> Ret {
        return std::unexpected(TypeError{std::move(msg), TypeErrorKind::Mismatch});
    };

    return std::visit([&](const auto& n) -> Ret {
        using T = std::decay_t<decltype(n)>;

        if constexpr (std::is_same_v<T, ExprLit>) {
            bool is_real = n.value.find('.') != std::string::npos
                        || n.value.find('e') != std::string::npos
                        || n.value.find('E') != std::string::npos;
            return TypeNode{is_real ? TypeVariant{TypeReal{}} : TypeVariant{TypeNat{}}};
        }

        if constexpr (std::is_same_v<T, ExprVar>) {
            auto it = env.find(n.name);
            if (it != env.end()) return it->second;
            return err("variable '" + n.name + "' has unknown type");
        }

        if constexpr (std::is_same_v<T, ExprBinary>) {
            if (n.op == BinOp::Union || n.op == BinOp::Inter || n.op == BinOp::SetMinus) {
                auto lt = infer_type(*n.lhs, env, sigs, struct_env);
                if (!lt) return lt;
                auto rt = infer_type(*n.rhs, env, sigs, struct_env);
                if (!rt) return rt;
                const auto* ls = std::get_if<TypeSet>(&lt->node);
                const auto* rs = std::get_if<TypeSet>(&rt->node);
                if (!ls)
                    return mismatch("type mismatch: left operand of set operation is not a set");
                if (!rs)
                    return mismatch("type mismatch: right operand of set operation is not a set");
                if (!(*ls->element_type == *rs->element_type))
                    return mismatch("type mismatch: set operation on sets with different element types");
                return *lt;
            }
            if (n.op == BinOp::Compose)
                return err("function composition deferred to TypeFun integration");
            auto lt = infer_type(*n.lhs, env, sigs, struct_env);
            if (!lt) return lt;
            auto rt = infer_type(*n.rhs, env, sigs, struct_env);
            if (!rt) return rt;
            auto promoted = numeric_promote(*lt, *rt);
            if (!promoted) return mismatch("type mismatch: non-numeric operands in arithmetic");
            return *promoted;
        }

        if constexpr (std::is_same_v<T, ExprUnary>) {
            return infer_type(*n.operand, env, sigs, struct_env);
        }

        if constexpr (std::is_same_v<T, ExprAbs>) {
            auto inner_t = infer_type(*n.operand, env, sigs, struct_env);
            if (!inner_t) return inner_t;
            // If the operand is a set, this is cardinality |S| → result is Nat.
            // Otherwise this is absolute value |x| → result has the same numeric type.
            if (std::get_if<TypeSet>(&inner_t->node))
                return TypeNode{TypeNat{}};
            return inner_t;
        }

        if constexpr (std::is_same_v<T, ExprLambda>) {
            if (!n.type.has_value())
                return err("lambda parameter '" + n.var + "' requires a type annotation");
            TypeEnv inner_env = env;
            inner_env[n.var] = *n.type;
            auto body_t = infer_type(*n.body, inner_env, sigs, struct_env);
            if (!body_t) return body_t;
            return type_fun(*n.type, *body_t);
        }

        if constexpr (std::is_same_v<T, ExprAgg>) {
            if (!n.type.has_value())
                return err("aggregate binder '" + n.var + "' requires a type annotation");
            TypeEnv inner_env = env;
            inner_env[n.var] = *n.type;
            return infer_type(*n.body, inner_env, sigs, struct_env);
        }

        if constexpr (std::is_same_v<T, ExprIf>) {
            auto tt = infer_type(*n.then_, env, sigs, struct_env);
            if (!tt) return tt;
            auto et = infer_type(*n.else_, env, sigs, struct_env);
            if (!et) return et;
            auto promoted = numeric_promote(*tt, *et);
            if (!promoted) return mismatch("type mismatch: conditional branches have incompatible types");
            return *promoted;
        }

        if constexpr (std::is_same_v<T, ExprCall>) {
            auto it = sigs.find(n.name);
            if (it == sigs.end())
                return err("cannot infer type of '" + n.name + "' without a function signature");
            // Walk the curried TypeFun, consuming one argument at a time.
            const TypeFun* cur = &it->second;
            for (std::size_t i = 0; i < n.args.size(); ++i) {
                auto arg_t = infer_type(*n.args[i], env, sigs, struct_env);
                if (!arg_t) return arg_t;
                // allow implicit numeric tower coercions (Nat → Int → Rat → Real).
                const bool types_match = (*arg_t == *cur->domain)
                    || numeric_coercible(*arg_t, *cur->domain);
                if (!types_match)
                    return mismatch("type mismatch: argument " + std::to_string(i + 1)
                                    + " to '" + n.name + "' — expected "
                                    + type_name(*cur->domain) + " but got "
                                    + type_name(*arg_t));
                if (i + 1 < n.args.size()) {
                    // More args to consume — codomain must be another TypeFun.
                    const auto* next = std::get_if<TypeFun>(&cur->codomain->node);
                    if (!next)
                        return err("too many arguments to '" + n.name + "'");
                    cur = next;
                }
            }
            // Return the codomain after consuming all args; for 0-arg calls, return whole sig.
            return n.args.empty() ? TypeNode{*cur} : *cur->codomain;
        }

        if constexpr (std::is_same_v<T, ExprApp>) {
            // Infer the type of the function expression; expect TypeFun or TypePi.
            auto func_t = infer_type(*n.func, env, sigs, struct_env);
            if (!func_t) return func_t;
            TypeNode cur_type = std::move(*func_t);
            for (std::size_t i = 0; i < n.args.size(); ++i) {
                if (const auto* tf = std::get_if<TypeFun>(&cur_type.node)) {
                    auto arg_t = infer_type(*n.args[i], env, sigs, struct_env);
                    if (!arg_t) return arg_t;
                    if (!(*arg_t == *tf->domain))
                        return mismatch("ExprApp: argument type mismatch at position "
                                        + std::to_string(i + 1));
                    cur_type = *tf->codomain;
                } else if (const auto* tp = std::get_if<TypePi>(&cur_type.node)) {
                    // Dependent application: substitute the argument into the codomain.
                    cur_type = subst_type(*tp->codomain, tp->var, *n.args[i]);
                } else {
                    return err("ExprApp: function expression does not have a function type"
                               " at argument " + std::to_string(i + 1));
                }
            }
            return cur_type;
        }

        if constexpr (std::is_same_v<T, ExprIndex>)
            return err("array index type inference not yet implemented");
        if constexpr (std::is_same_v<T, ExprTuple>)
            return err("tuple type inference not yet implemented");
        if constexpr (std::is_same_v<T, ExprField>) {
            // Infer the type of the base expression; if it is a TypeUser, look up
            // the named field in the StructEnv to find its declared type.
            auto base_t = infer_type(*n.base, env, sigs, struct_env);
            if (!base_t) return err("cannot infer type of base expression in field access");
            const auto* user_t = std::get_if<TypeUser>(&base_t->node);
            if (!user_t)
                return err("field projection '" + n.field_name + "' applied to non-struct type");
            if (struct_env) {
                auto sit = struct_env->find(user_t->name);
                if (sit != struct_env->end()) {
                    for (const auto& sf : sit->second) {
                        if (const auto* ft = std::get_if<FieldTerm>(&sf)) {
                            if (ft->name == n.field_name)
                                return ft->type;
                        }
                    }
                }
            }
            return err("unknown field '" + n.field_name + "' on type '" + user_t->name + "'");
        }

        if constexpr (std::is_same_v<T, ExprSetLit>) {
            if (n.elements.empty())
                return err("cannot infer element type of empty set literal");
            auto elem_t = infer_type(*n.elements[0], env, sigs, struct_env);
            if (!elem_t) return elem_t;
            for (std::size_t i = 1; i < n.elements.size(); ++i) {
                auto t = infer_type(*n.elements[i], env, sigs, struct_env);
                if (!t) continue; // skip if element type unknown
                auto promoted = numeric_promote(*elem_t, *t);
                if (promoted) { elem_t = *promoted; continue; }
                if (!(*elem_t == *t))
                    return mismatch("type mismatch: set literal elements have inconsistent types");
            }
            return TypeNode{TypeSet{std::make_shared<TypeNode>(*elem_t)}};
        }
        if constexpr (std::is_same_v<T, ExprSetCompr>) {
            if (n.type.has_value())
                return TypeNode{TypeSet{std::make_shared<TypeNode>(*n.type)}};
            return err("cannot infer element type of set comprehension without type annotation");
        }

        return err("unsupported expression form");
    }, e.node);
}

TypeNode expand_type_aliases(TypeNode t, const TypeAliasTable& aliases) {
    if (aliases.empty()) return t;
    return std::visit([&](auto&& n) -> TypeNode {
        using T = std::decay_t<decltype(n)>;
        if constexpr (std::is_same_v<T, TypeUser>) {
            auto it = aliases.find(n.name);
            if (it != aliases.end())
                return expand_type_aliases(it->second, aliases);
            return t;
        } else if constexpr (std::is_same_v<T, TypeFun>) {
            return TypeNode{TypeFun{
                std::make_shared<TypeNode>(expand_type_aliases(*n.domain, aliases)),
                std::make_shared<TypeNode>(expand_type_aliases(*n.codomain, aliases))}};
        } else if constexpr (std::is_same_v<T, TypeTuple>) {
            TypeTuple tt;
            for (const auto& e : n.elements)
                tt.elements.push_back(
                    std::make_shared<TypeNode>(expand_type_aliases(*e, aliases)));
            return TypeNode{std::move(tt)};
        } else if constexpr (std::is_same_v<T, TypeSet>) {
            return TypeNode{TypeSet{
                std::make_shared<TypeNode>(expand_type_aliases(*n.element_type, aliases))}};
        } else if constexpr (std::is_same_v<T, TypePi>) {
            return TypeNode{TypePi{n.var,
                std::make_shared<TypeNode>(expand_type_aliases(*n.domain, aliases)),
                std::make_shared<TypeNode>(expand_type_aliases(*n.codomain, aliases))}};
        } else {
            return t; // ground types: Nat Int Rat Real Prop
        }
    }, t.node);
}

// ── subst_type ────────────────────────────────────────────────────────────────
//
// Replaces every TypeUser{var} occurrence in `t` with a type derived from `arg`.
// When `arg` is an ExprVar{name}, TypeUser{var} → TypeUser{name}.
// For other expression forms the substitution is left unchanged (TypeUser{var}
// stays) — this covers the non-dependent case safely.
TypeNode subst_type(const TypeNode& t, const std::string& var, const Expr& arg) {
    // Extract the name to substitute in: only defined for variable expressions.
    const std::string* new_name = nullptr;
    if (const auto* ev = std::get_if<ExprVar>(&arg.node))
        new_name = &ev->name;

    return std::visit([&](const auto& n) -> TypeNode {
        using T = std::decay_t<decltype(n)>;
        if constexpr (std::is_same_v<T, TypeUser>) {
            if (n.name == var && new_name)
                return TypeNode{TypeUser{*new_name}};
            return t;
        } else if constexpr (std::is_same_v<T, TypeFun>) {
            return TypeNode{TypeFun{
                std::make_shared<TypeNode>(subst_type(*n.domain, var, arg)),
                std::make_shared<TypeNode>(subst_type(*n.codomain, var, arg))}};
        } else if constexpr (std::is_same_v<T, TypeTuple>) {
            TypeTuple tt;
            for (const auto& e : n.elements)
                tt.elements.push_back(
                    std::make_shared<TypeNode>(subst_type(*e, var, arg)));
            return TypeNode{std::move(tt)};
        } else if constexpr (std::is_same_v<T, TypeSet>) {
            return TypeNode{TypeSet{
                std::make_shared<TypeNode>(subst_type(*n.element_type, var, arg))}};
        } else if constexpr (std::is_same_v<T, TypePi>) {
            // If the inner binder shadows var, don't substitute in the codomain.
            auto dom = std::make_shared<TypeNode>(subst_type(*n.domain, var, arg));
            if (n.var == var)
                return TypeNode{TypePi{n.var, std::move(dom), n.codomain}};
            return TypeNode{TypePi{n.var, std::move(dom),
                std::make_shared<TypeNode>(subst_type(*n.codomain, var, arg))}};
        } else {
            return t; // ground types: Nat Int Rat Real Prop
        }
    }, t.node);
}

} // namespace forall::ast
