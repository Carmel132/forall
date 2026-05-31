#include <forall/pretty/to_string.hpp>

namespace forall::pretty {

std::string to_string(const ast::TypeNode& t) {
    return std::visit([](const auto& n) -> std::string {
        using T = std::decay_t<decltype(n)>;
        if constexpr (std::is_same_v<T, ast::TypeNat>)  return "Nat";
        if constexpr (std::is_same_v<T, ast::TypeInt>)  return "Int";
        if constexpr (std::is_same_v<T, ast::TypeRat>)  return "Rat";
        if constexpr (std::is_same_v<T, ast::TypeReal>) return "Real";
        if constexpr (std::is_same_v<T, ast::TypeProp>) return "Prop";
        if constexpr (std::is_same_v<T, ast::TypeUser>) return n.name;
        if constexpr (std::is_same_v<T, ast::TypeFun>) {
            // right-associative: lhs needs parens only when it is also a TypeFun
            std::string dom = to_string(*n.domain);
            if (std::get_if<ast::TypeFun>(&n.domain->node))
                dom = "(" + dom + ")";
            return dom + " -> " + to_string(*n.codomain);
        }
        if constexpr (std::is_same_v<T, ast::TypeTuple>) {
            std::string r = "(";
            for (std::size_t i = 0; i < n.elements.size(); ++i) {
                if (i > 0) r += ", ";
                r += to_string(*n.elements[i]);
            }
            return r + ")";
        }
        if constexpr (std::is_same_v<T, ast::TypeSet>) {
            // Add parens around the element type when it is a function type,
            // since "Set Nat -> Prop" is otherwise parsed as (Set Nat) -> Prop.
            std::string elem = to_string(*n.element_type);
            if (std::get_if<ast::TypeFun>(&n.element_type->node))
                elem = "(" + elem + ")";
            return "Set " + elem;
        }
        return "?";
    }, t.node);
}

namespace {

// Forward declarations for mutual recursion (ExprIf ↔ Prop, PropRel ↔ Expr).
std::string ts_expr(const ast::Expr& e);
std::string ts_prop(const ast::Prop& p);

// ── Helpers ───────────────────────────────────────────────────────────────────

static std::string paren(bool wrap, std::string s) {
    if (wrap) return "(" + std::move(s) + ")";
    return s;
}

static std::string rel_op_str(ast::RelOp op) {
    switch (op) {
        case ast::RelOp::Lt:          return " < ";
        case ast::RelOp::Gt:          return " > ";
        case ast::RelOp::LtEq:        return " \xe2\x89\xa4 ";  // ≤
        case ast::RelOp::GtEq:        return " \xe2\x89\xa5 ";  // ≥
        case ast::RelOp::Eq:          return " = ";
        case ast::RelOp::NotEq:       return " \xe2\x89\xa0 ";  // ≠
        case ast::RelOp::In:          return " \xe2\x88\x88 ";  // ∈
        case ast::RelOp::NotIn:       return " \xe2\x88\x89 ";  // ∉
        case ast::RelOp::SubsetEq:    return " \xe2\x8a\x86 ";  // ⊆
        case ast::RelOp::Subset:      return " \xe2\x8a\x82 ";  // ⊂
        case ast::RelOp::SupersetEq:  return " \xe2\x8a\x87 ";  // ⊇
    }
    return " ? ";
}

// Grammar-based precedence levels for expressions.
//
//   5 = atom:  ExprLit, ExprVar, ExprCall, ExprAbs, ExprIndex, ExprTuple
//   4 = unary: ExprUnary{Neg}  (parseExprUnary calls parseExprPow)
//   3 = pow:   ExprBinary{Pow} (right-assoc; lhs must be atom per grammar)
//   2 = mul:   ExprBinary{Mul/Div/IDiv/Mod/Compose}
//   1 = add:   ExprBinary{Add/Sub}
//   0 = loose: ExprLambda, ExprIf, ExprAgg

static bool is_expr_atom(const ast::ExprNode& n) {
    return std::holds_alternative<ast::ExprLit>(n)
        || std::holds_alternative<ast::ExprVar>(n)
        || std::holds_alternative<ast::ExprCall>(n)
        || std::holds_alternative<ast::ExprAbs>(n)
        || std::holds_alternative<ast::ExprIndex>(n)
        || std::holds_alternative<ast::ExprTuple>(n)
        || std::holds_alternative<ast::ExprSetLit>(n)
        || std::holds_alternative<ast::ExprSetCompr>(n);
}

static int expr_prec(const ast::ExprNode& n) {
    if (is_expr_atom(n)) return 5;
    if (std::holds_alternative<ast::ExprUnary>(n)) return 4;
    if (const auto* b = std::get_if<ast::ExprBinary>(&n)) {
        switch (b->op) {
            case ast::BinOp::Pow:                          return 3;
            case ast::BinOp::Mul:  case ast::BinOp::Div:
            case ast::BinOp::IDiv: case ast::BinOp::Mod:
            case ast::BinOp::Compose:
            case ast::BinOp::Inter:                        return 2;  // ∩ binds like *
            case ast::BinOp::Add:  case ast::BinOp::Sub:
            case ast::BinOp::Union: case ast::BinOp::SetMinus: return 1; // ∪ ∖ bind like +
        }
    }
    return 0;
}

// Precedence levels for propositions:
//
//   6 = atom:  Atomic, PropFalse, PropPred, PropRel
//   5 = not:   PropNot  (operand must be atomic per grammar)
//   4 = and:   PropAnd  (left-assoc)
//   3 = or:    PropOr   (left-assoc)
//   2 = impl:  PropImpl (right-assoc; rhs handled by parseImplication)
//   0 = quant: PropForall, PropExists (loosest; body is full prop)

static bool is_prop_atom(const ast::PropNode& n) {
    return std::holds_alternative<ast::Atomic>(n)
        || std::holds_alternative<ast::PropFalse>(n)
        || std::holds_alternative<ast::PropPred>(n)
        || std::holds_alternative<ast::PropRel>(n);
}

static int prop_prec(const ast::PropNode& n) {
    if (is_prop_atom(n))                               return 6;
    if (std::holds_alternative<ast::PropNot>(n))       return 5;
    if (std::holds_alternative<ast::PropAnd>(n))       return 4;
    if (std::holds_alternative<ast::PropOr>(n))        return 3;
    if (std::holds_alternative<ast::PropImpl>(n))      return 2;
    return 0;
}

static std::string ts_args(const std::vector<ast::ExprPtr>& args) {
    std::string s;
    for (std::size_t i = 0; i < args.size(); ++i) {
        if (i > 0) s += ", ";
        s += ts_expr(*args[i]);
    }
    return s;
}

// ── Expression ────────────────────────────────────────────────────────────────

std::string ts_expr(const ast::Expr& e) {
    return std::visit([](const auto& n) -> std::string {
        using T = std::decay_t<decltype(n)>;

        if constexpr (std::is_same_v<T, ast::ExprLit>) {
            return n.value;
        }
        else if constexpr (std::is_same_v<T, ast::ExprVar>) {
            return n.name;
        }
        else if constexpr (std::is_same_v<T, ast::ExprUnary>) {
            // Operand was parsed by parseExprPow (atom or pow chain, prec ≥ 3).
            // Anything below prec 3 (mul, add, loose) needs explicit parens.
            return "-" + paren(expr_prec(n.operand->node) < 3, ts_expr(*n.operand));
        }
        else if constexpr (std::is_same_v<T, ast::ExprAbs>) {
            return "|" + ts_expr(*n.operand) + "|";
        }
        else if constexpr (std::is_same_v<T, ast::ExprCall>) {
            return n.name + "(" + ts_args(n.args) + ")";
        }
        else if constexpr (std::is_same_v<T, ast::ExprIndex>) {
            // Grammar: exprAtom = base { "[" expr "]" }.  The base must be atom-level.
            return paren(!is_expr_atom(n.array->node), ts_expr(*n.array))
                   + "[" + ts_expr(*n.index) + "]";
        }
        else if constexpr (std::is_same_v<T, ast::ExprTuple>) {
            std::string s = "(";
            for (std::size_t i = 0; i < n.elements.size(); ++i) {
                if (i > 0) s += ", ";
                s += ts_expr(*n.elements[i]);
            }
            return s + ")";
        }
        else if constexpr (std::is_same_v<T, ast::ExprSetLit>) {
            if (n.elements.empty()) return "{}";
            std::string s = "{";
            for (std::size_t i = 0; i < n.elements.size(); ++i) {
                if (i > 0) s += ", ";
                s += ts_expr(*n.elements[i]);
            }
            return s + "}";
        }
        else if constexpr (std::is_same_v<T, ast::ExprSetCompr>) {
            std::string s = "{" + n.var;
            if (n.type) s += " : " + to_string(*n.type);
            return s + " | " + ts_prop(*n.pred) + "}";
        }
        else if constexpr (std::is_same_v<T, ast::ExprLambda>) {
            std::string s = "fun " + n.var;
            if (n.type) s += " : " + to_string(*n.type);
            return s + " => " + ts_expr(*n.body);
        }
        else if constexpr (std::is_same_v<T, ast::ExprIf>) {
            return "if " + ts_prop(*n.cond)
                   + " then " + ts_expr(*n.then_)
                   + " else " + ts_expr(*n.else_);
        }
        else if constexpr (std::is_same_v<T, ast::ExprAgg>) {
            // ∑ or ∏ (UTF-8)
            std::string s = (n.op == ast::AggOp::Sum
                             ? "\xe2\x88\x91"   // ∑ U+2211
                             : "\xe2\x88\x8f");  // ∏ U+220F
            s += " " + n.var;
            if (n.type) {
                s += " : " + to_string(*n.type);
            } else if (n.rel && n.bound) {
                s += rel_op_str(*n.rel) + ts_expr(**n.bound);
            }
            return s + ", " + ts_expr(*n.body);
        }
        else if constexpr (std::is_same_v<T, ast::ExprBinary>) {
            const int lp = expr_prec(n.lhs->node);
            const int rp = expr_prec(n.rhs->node);

            // Pow: right-associative.  Grammar constrains lhs to exprAtom.
            // rhs calls exprUnary so prec ≥ 3 is fine; parens if prec < 3.
            if (n.op == ast::BinOp::Pow) {
                return paren(!is_expr_atom(n.lhs->node), ts_expr(*n.lhs))
                       + "^"
                       + paren(rp < 3, ts_expr(*n.rhs));
            }

            // All other binary ops: left-associative.
            //   lhs: parens if prec(lhs) < cur_prec  (strict — same prec lhs is fine)
            //   rhs: parens if prec(rhs) ≤ cur_prec  (same prec rhs needs parens)
            const char* op_str = "?";
            int cur_prec = 0;
            switch (n.op) {
                case ast::BinOp::Add:      op_str = " + ";             cur_prec = 1; break;
                case ast::BinOp::Sub:      op_str = " - ";             cur_prec = 1; break;
                case ast::BinOp::Union:    op_str = " \xe2\x88\xaa "; cur_prec = 1; break; // ∪ U+222A
                case ast::BinOp::SetMinus: op_str = " \xe2\x88\x96 "; cur_prec = 1; break; // ∖ U+2216
                case ast::BinOp::Mul:      op_str = " * ";             cur_prec = 2; break;
                case ast::BinOp::Div:      op_str = " / ";             cur_prec = 2; break;
                case ast::BinOp::IDiv:     op_str = " div ";           cur_prec = 2; break;
                case ast::BinOp::Mod:      op_str = " mod ";           cur_prec = 2; break;
                case ast::BinOp::Inter:    op_str = " \xe2\x88\xa9 "; cur_prec = 2; break; // ∩ U+2229
                case ast::BinOp::Compose:  op_str = " \xe2\x88\x98 "; cur_prec = 2; break; // ∘ U+2218
                case ast::BinOp::Pow:      break; // handled above
            }
            return paren(lp < cur_prec, ts_expr(*n.lhs))
                   + op_str
                   + paren(rp <= cur_prec, ts_expr(*n.rhs));
        }
        return "";
    }, e.node);
}

// ── Proposition ───────────────────────────────────────────────────────────────

std::string ts_prop(const ast::Prop& p) {
    return std::visit([](const auto& n) -> std::string {
        using T = std::decay_t<decltype(n)>;

        if constexpr (std::is_same_v<T, ast::Atomic>) {
            return n.name;
        }
        else if constexpr (std::is_same_v<T, ast::PropFalse>) {
            return "\xe2\x8a\xa5";  // ⊥ U+22A5
        }
        else if constexpr (std::is_same_v<T, ast::PropNot>) {
            // Grammar: negation = "¬" atomic_prop.  Operand must be atomic.
            return "\xc2\xac"  // ¬ U+00AC
                   + paren(!is_prop_atom(n.inner->node), ts_prop(*n.inner));
        }
        else if constexpr (std::is_same_v<T, ast::PropAnd>) {
            // Left-associative (prec 4).
            //   lhs: parens if prec < 4   (Or=3, Impl=2, Quant=0)
            //   rhs: parens if prec ≤ 4   (same prec or lower, incl. And=4)
            const int lp = prop_prec(n.lhs->node);
            const int rp = prop_prec(n.rhs->node);
            return paren(lp < 4, ts_prop(*n.lhs))
                   + " \xe2\x88\xa7 "   // ∧ U+2227
                   + paren(rp <= 4, ts_prop(*n.rhs));
        }
        else if constexpr (std::is_same_v<T, ast::PropOr>) {
            // Left-associative (prec 3).
            //   lhs: parens if prec < 3   (Impl=2, Quant=0)
            //   rhs: parens if prec ≤ 3   (Or=3, Impl=2, Quant=0)
            const int lp = prop_prec(n.lhs->node);
            const int rp = prop_prec(n.rhs->node);
            return paren(lp < 3, ts_prop(*n.lhs))
                   + " \xe2\x88\xa8 "   // ∨ U+2228
                   + paren(rp <= 3, ts_prop(*n.rhs));
        }
        else if constexpr (std::is_same_v<T, ast::PropImpl>) {
            // Right-associative (prec 2).
            //   lhs: parens if prec ≤ 2   (Impl=2 and Quant=0 need parens as lhs)
            //   rhs: no extra parens — parseImplication handles all forms including quantifiers
            const int lp = prop_prec(n.lhs->node);
            return paren(lp <= 2, ts_prop(*n.lhs))
                   + " \xe2\x86\x92 "   // → U+2192
                   + ts_prop(*n.rhs);
        }
        else if constexpr (std::is_same_v<T, ast::PropForall>) {
            std::string s = "\xe2\x88\x80 " + n.var;  // ∀ U+2200
            if (n.type) s += " : " + to_string(*n.type);
            return s + ", " + ts_prop(*n.body);
        }
        else if constexpr (std::is_same_v<T, ast::PropExists>) {
            std::string s = "\xe2\x88\x83 " + n.var;  // ∃ U+2203
            if (n.type) s += " : " + to_string(*n.type);
            return s + ", " + ts_prop(*n.body);
        }
        else if constexpr (std::is_same_v<T, ast::PropRel>) {
            return ts_expr(*n.lhs) + rel_op_str(n.op) + ts_expr(*n.rhs);
        }
        else if constexpr (std::is_same_v<T, ast::PropPred>) {
            return n.name + "(" + ts_args(n.args) + ")";
        }
        return "";
    }, p.node);
}

} // namespace

// ── Public API ────────────────────────────────────────────────────────────────

std::string to_string(const ast::Expr& e) { return ts_expr(e); }
std::string to_string(const ast::Prop& p) { return ts_prop(p); }

} // namespace forall::pretty
