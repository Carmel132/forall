#include <forall/parser/parser.hpp>
#include <forall/pretty/to_string.hpp>

namespace forall::parser {

Parser::Parser(std::span<const lexer::Token> tokens, diag::DiagnosticEngine& diag)
    : tokens_{tokens}, diag_{diag} {}

// ── Token stream helpers ───────────────────────────────────────────────────────

const lexer::Token& Parser::peek() const noexcept { return tokens_[pos_]; }

const lexer::Token& Parser::advance() noexcept {
    if (!isAtEnd()) ++pos_;
    return tokens_[pos_ - 1];
}

bool Parser::check(lexer::TokenKind kind) const noexcept { return peek().kind == kind; }

bool Parser::isAtEnd() const noexcept { return check(lexer::TokenKind::Eof); }

bool Parser::expect(lexer::TokenKind kind, std::string_view msg) {
    if (check(kind)) { advance(); return true; }
    diag_.emit({diag::Severity::Error, peek().loc, std::string{msg}});
    return false;
}

// Consume the word "a" used as an article in "be a Prop" — it is not a keyword
// so it arrives as an Identifier with lexeme "a".
void Parser::consumeArticle() {
    if (check(lexer::TokenKind::Identifier) && peek().lexeme == "a")
        advance();
}

// ── Expression parsing ─────────────────────────────────────────────────────────
//
// Grammar (see docs/grammar.ebnf):
//   expr     = lambda | condExpr | exprMul { ("+" | "-") exprMul }
//   lambda   = ("fun" | "λ") id [":" type] ("=>" | ",") expr
//   condExpr = "if" prop "then" expr "else" expr
//   exprMul  = exprUnary { ("*" | "/" | "div" | "mod")    exprUnary }
//   exprUnary = ["-"] exprPow
//   exprPow  = exprAtom  [ "^" exprUnary ]           (right-associative)
//   exprAtom = base { "[" expr "]" }                  (postfix subscript, left-assoc)
//   base     = number
//            | identifier ["(" argList ")"]
//            | "|" expr "|"
//            | "(" expr ")"                            (grouping)
//            | "(" expr "," expr {"," expr} ")"        (tuple)

ast::Expr Parser::parseExpr() {
    using K = lexer::TokenKind;
    if (check(K::KwFun) || check(K::Lambda))
        return parseLambda();
    if (check(K::KwIf))
        return parseCondExpr();
    if (check(K::KwSum) || check(K::Sigma) || check(K::KwProd) || check(K::Pi))
        return parseAggregate();
    const auto loc = peek().loc;
    auto lhs = parseExprMul();
    while (check(lexer::TokenKind::Plus)       || check(lexer::TokenKind::Minus)
        || check(lexer::TokenKind::KwUnion)    || check(lexer::TokenKind::CupSym)
        || check(lexer::TokenKind::KwSetMinus) || check(lexer::TokenKind::Backslash))
    {
        ast::BinOp op;
        switch (peek().kind) {
            case lexer::TokenKind::Plus:        op = ast::BinOp::Add;      break;
            case lexer::TokenKind::Minus:       op = ast::BinOp::Sub;      break;
            case lexer::TokenKind::KwUnion:
            case lexer::TokenKind::CupSym:      op = ast::BinOp::Union;    break;
            default:                            op = ast::BinOp::SetMinus; break; // setminus / backslash
        }
        advance();
        auto rhs = parseExprMul();
        lhs = {loc, ast::ExprBinary{op, ast::make_expr(std::move(lhs)),
                                        ast::make_expr(std::move(rhs))}};
    }
    mark_end(lhs);
    return lhs;
}

ast::Expr Parser::parseExprMul() {
    const auto loc = peek().loc;
    auto lhs = parseExprUnary();
    while (check(lexer::TokenKind::Star)      || check(lexer::TokenKind::Slash)  ||
           check(lexer::TokenKind::KwDiv)     || check(lexer::TokenKind::KwMod)  ||
           check(lexer::TokenKind::KwCompose) || check(lexer::TokenKind::Circ)   ||
           check(lexer::TokenKind::KwInter)   || check(lexer::TokenKind::CapSym))
    {
        ast::BinOp op;
        switch (peek().kind) {
            case lexer::TokenKind::Star:      op = ast::BinOp::Mul;     break;
            case lexer::TokenKind::Slash:     op = ast::BinOp::Div;     break;
            case lexer::TokenKind::KwDiv:     op = ast::BinOp::IDiv;    break;
            case lexer::TokenKind::KwMod:     op = ast::BinOp::Mod;     break;
            case lexer::TokenKind::KwInter:
            case lexer::TokenKind::CapSym:    op = ast::BinOp::Inter;   break; // inter / ∩
            default:                          op = ast::BinOp::Compose; break; // compose / ∘
        }
        advance();
        auto rhs = parseExprUnary();
        lhs = {loc, ast::ExprBinary{op, ast::make_expr(std::move(lhs)),
                                        ast::make_expr(std::move(rhs))}};
    }
    mark_end(lhs);
    return lhs;
}

ast::Expr Parser::parseExprUnary() {
    if (check(lexer::TokenKind::Minus)) {
        const auto loc = peek().loc;
        advance();
        auto operand = parseExprPow();
        ast::Expr e{loc, ast::ExprUnary{ast::UnaryOp::Neg, ast::make_expr(std::move(operand))}};
        mark_end(e); return e;
    }
    if (check(lexer::TokenKind::KwInv)) {
        const auto loc = peek().loc;
        advance();
        auto operand = parseExprPow(); // inv applies to the immediately following atom/pow
        std::vector<ast::ExprPtr> args{ast::make_expr(std::move(operand))};
        ast::Expr e{loc, ast::ExprCall{"inv", std::move(args)}};
        mark_end(e); return e;
    }
    if (check(lexer::TokenKind::KwCompl)) {
        const auto loc = peek().loc;
        advance();
        auto operand = parseExprPow(); // compl applies to the immediately following atom/pow
        std::vector<ast::ExprPtr> args{ast::make_expr(std::move(operand))};
        ast::Expr e{loc, ast::ExprCall{"compl", std::move(args)}};
        mark_end(e); return e;
    }
    return parseExprPow();
}

// Right-associative: x ^ y ^ z  =  x ^ (y ^ z)
// RHS calls parseExprUnary so that -x ^ 2  =  -(x ^ 2).
ast::Expr Parser::parseExprPow() {
    const auto loc = peek().loc;
    auto base = parseExprAtom();
    if (check(lexer::TokenKind::Caret)) {
        advance();
        auto exp = parseExprUnary(); // right-recursive via unary
        ast::Expr e{loc, ast::ExprBinary{ast::BinOp::Pow, ast::make_expr(std::move(base)),
                                                            ast::make_expr(std::move(exp))}};
        mark_end(e); return e;
    }
    return base;
}

ast::Expr Parser::parseExprAtom() {
    const auto loc = peek().loc;
    ast::Expr base{loc, ast::ExprLit{"0"}}; // overwritten below

    // Number literal
    if (check(lexer::TokenKind::Number)) {
        base = {loc, ast::ExprLit{std::string{advance().lexeme}}};
    }
    // ⌊ expr ⌋  →  ExprCall{"floor", [expr]}   (desugar at parse time)
    else if (check(lexer::TokenKind::LFloor)) {
        advance();
        auto inner = parseExpr();
        expect(lexer::TokenKind::RFloor, "expected closing floor bracket '\xe2\x8c\x8b'");
        std::vector<ast::ExprPtr> args{ast::make_expr(std::move(inner))};
        base = {loc, ast::ExprCall{"floor", std::move(args)}};
    }
    // ⌈ expr ⌉  →  ExprCall{"ceil", [expr]}    (desugar at parse time)
    else if (check(lexer::TokenKind::LCeil)) {
        advance();
        auto inner = parseExpr();
        expect(lexer::TokenKind::RCeil, "expected closing ceiling bracket '\xe2\x8c\x89'");
        std::vector<ast::ExprPtr> args{ast::make_expr(std::move(inner))};
        base = {loc, ast::ExprCall{"ceil", std::move(args)}};
    }
    // Absolute value  |expr|
    else if (check(lexer::TokenKind::Pipe)) {
        advance();
        auto inner = parseExpr();
        expect(lexer::TokenKind::Pipe, "expected closing '|' for absolute value");
        base = {loc, ast::ExprAbs{ast::make_expr(std::move(inner))}};
    }
    // Grouped expression  (expr)  or tuple  (expr, expr, ...)
    else if (check(lexer::TokenKind::LParen)) {
        advance();
        auto first = parseExpr();
        if (check(lexer::TokenKind::RParen)) {
            advance();
            base = std::move(first); // grouping — preserve inner expression's location
        } else {
            // Tuple: collect the rest of the elements
            std::vector<ast::ExprPtr> elements;
            elements.push_back(ast::make_expr(std::move(first)));
            while (check(lexer::TokenKind::Comma)) {
                advance();
                elements.push_back(ast::make_expr(parseExpr()));
            }
            expect(lexer::TokenKind::RParen, "expected ')' to close tuple");
            base = {loc, ast::ExprTuple{std::move(elements)}};
        }
    }
    // Identifier: variable or function call  f(x, y)
    else if (check(lexer::TokenKind::Identifier)) {
        std::string name{advance().lexeme};
        if (check(lexer::TokenKind::LParen)) {
            advance();
            auto args = parseArgList();
            expect(lexer::TokenKind::RParen, "expected ')' after argument list");
            base = {loc, ast::ExprCall{std::move(name), std::move(args)}};
        } else {
            base = {loc, ast::ExprVar{std::move(name)}};
        }
    }
    // Set literal  {a, b, c}  /  {} (empty)
    // Set comprehension  {x : T | P}  /  {x | P}
    else if (check(lexer::TokenKind::LBrace)) {
        base = parseSetExpr();
    }
    else {
        diag_.emit({diag::Severity::Error, loc,
                    "expected expression; got '" + peek().lexeme + "'"});
        advance();
        ast::Expr sentinel{loc, ast::ExprLit{"0"}};
        mark_end(sentinel); return sentinel; // error sentinel — skip indexing
    }

    // Postfix operators (left-associative, tightest binding):
    //   base[index]  →  ExprIndex
    //   base!        →  ExprCall{"factorial", [base]}
    while (check(lexer::TokenKind::LBracket) || check(lexer::TokenKind::Bang)) {
        if (check(lexer::TokenKind::LBracket)) {
            advance();
            auto idx = parseExpr();
            expect(lexer::TokenKind::RBracket, "expected ']' after index expression");
            base = {loc, ast::ExprIndex{ast::make_expr(std::move(base)),
                                        ast::make_expr(std::move(idx))}};
        } else { // Bang — factorial
            advance();
            std::vector<ast::ExprPtr> args{ast::make_expr(std::move(base))};
            base = {loc, ast::ExprCall{"factorial", std::move(args)}};
        }
    }

    mark_end(base);
    return base;
}

// parseSetExpr — called from parseExprAtom when "{" is seen.
// Disambiguates between:
//   {}                        empty set literal
//   {expr, ...}               set literal
//   {id : type | prop}        set comprehension with type annotation
//   {id | prop}               set comprehension without type
// Lookahead: after "{", if identifier is followed by ":" or "|" → comprehension.
ast::Expr Parser::parseSetExpr() {
    const auto loc = peek().loc;
    advance(); // consume {

    if (check(lexer::TokenKind::RBrace)) {
        advance();
        ast::Expr e{loc, ast::ExprSetLit{}}; mark_end(e); return e;
    }

    // Two-token lookahead: {id : type | P} or {id | P}
    if (check(lexer::TokenKind::Identifier) && pos_ + 1 < tokens_.size()) {
        const auto next_kind = tokens_[pos_ + 1].kind;
        if (next_kind == lexer::TokenKind::Colon || next_kind == lexer::TokenKind::Pipe) {
            std::string var = std::string{advance().lexeme};
            std::optional<ast::TypeNode> type;
            if (check(lexer::TokenKind::Colon)) {
                advance();
                if (check(lexer::TokenKind::Identifier) || check(lexer::TokenKind::LParen))
                    type = parseType();
                else
                    diag_.emit({diag::Severity::Error, peek().loc,
                                "expected type name after ':' in set comprehension"});
            }
            expect(lexer::TokenKind::Pipe, "expected '|' in set comprehension");
            auto pred = parseProp();
            expect(lexer::TokenKind::RBrace, "expected '}' to close set comprehension");
            ast::Expr e{loc, ast::ExprSetCompr{std::move(var), std::move(type),
                                               ast::make_prop(std::move(pred))}};
            mark_end(e); return e;
        }
    }

    // Set literal: {expr, expr, ...}
    std::vector<ast::ExprPtr> elements;
    elements.push_back(ast::make_expr(parseExpr()));
    while (check(lexer::TokenKind::Comma)) {
        advance();
        elements.push_back(ast::make_expr(parseExpr()));
    }
    expect(lexer::TokenKind::RBrace, "expected '}' to close set literal");
    ast::Expr e{loc, ast::ExprSetLit{std::move(elements)}};
    mark_end(e); return e;
}

// lambda = ("fun" | "λ") id [":" type] ("=>" | ",") expr
// Body extends right as far as possible (same rule as quantifier body).
ast::Expr Parser::parseLambda() {
    const auto loc = peek().loc;
    advance(); // consume "fun" or "λ"

    std::string var;
    if (check(lexer::TokenKind::Identifier))
        var = std::string{advance().lexeme};
    else
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected parameter name after 'fun'"});

    std::optional<ast::TypeNode> type;
    if (check(lexer::TokenKind::Colon)) {
        advance();
        if (check(lexer::TokenKind::Identifier) || check(lexer::TokenKind::LParen))
            type = parseType();
        else
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected type name after ':' in lambda"});
    }

    // Accept both "=>" (primary) and "," (Unicode λ convention) as the separator.
    if (check(lexer::TokenKind::FatArrow) || check(lexer::TokenKind::Comma))
        advance();
    else
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected '=>' or ',' after lambda parameter"});

    auto body = parseExpr(); // body extends right as far as possible
    ast::Expr e{loc, ast::ExprLambda{std::move(var), std::move(type),
                                     ast::make_expr(std::move(body))}};
    mark_end(e); return e;
}

// condExpr = "if" prop "then" expr "else" expr
// The condition is a full proposition (including implications and quantifiers).
// Note: "if P then Q" (no else) is the proposition-level implication form handled
// by parseImplication(); this function only fires from the expression layer.
ast::Expr Parser::parseCondExpr() {
    const auto loc = peek().loc;
    advance(); // consume "if"

    auto cond  = parseProp(); // full proposition as condition
    expect(lexer::TokenKind::KwThen, "expected 'then' after condition");
    auto then_ = parseExpr(); // then-branch extends right until "else"
    expect(lexer::TokenKind::KwElse, "expected 'else' after then-branch");
    auto else_ = parseExpr(); // else-branch extends right

    ast::Expr e{loc, ast::ExprIf{ast::make_prop(std::move(cond)),
                                 ast::make_expr(std::move(then_)),
                                 ast::make_expr(std::move(else_))}};
    mark_end(e); return e;
}

static std::optional<ast::RelOp> as_rel_op(lexer::TokenKind k); // defined in prop section below

// aggregate = ("sum"|"∑"|"prod"|"∏") aggBinder "," expr
// aggBinder = identifier ":" type           (typed binder)
//           | identifier rel expr           (bounded binder: sum i < n, f i)
// Body extends right as far as possible (same rule as lambda body).
ast::Expr Parser::parseAggregate() {
    const auto loc = peek().loc;
    const bool is_sum = check(lexer::TokenKind::KwSum) || check(lexer::TokenKind::Sigma);
    advance(); // consume "sum"/"prod"/∑/∏

    std::string var;
    if (check(lexer::TokenKind::Identifier))
        var = std::string{advance().lexeme};
    else
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected variable name after aggregate operator"});

    std::optional<ast::TypeNode> type;
    std::optional<ast::RelOp>   rel;
    std::optional<ast::ExprPtr> bound;

    if (check(lexer::TokenKind::Colon)) {
        advance(); // typed binder: sum i : T
        if (check(lexer::TokenKind::Identifier) || check(lexer::TokenKind::LParen))
            type = parseType();
        else
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected type name after ':' in aggregate binder"});
    } else if (auto r = as_rel_op(peek().kind); r.has_value()) {
        advance(); // bounded binder: sum i < n  (bound expr stops at comma)
        rel   = r;
        bound = ast::make_expr(parseExpr());
    } else {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected ':' or relational operator in aggregate binder"});
    }

    expect(lexer::TokenKind::Comma, "expected ',' after aggregate binder");
    auto body = parseExpr(); // body extends right as far as possible

    const ast::AggOp op = is_sum ? ast::AggOp::Sum : ast::AggOp::Prod;
    ast::Expr e{loc, ast::ExprAgg{op, std::move(var), std::move(type), rel, std::move(bound),
                                   ast::make_expr(std::move(body))}};
    mark_end(e); return e;
}

// argList = expr { "," expr }
std::vector<ast::ExprPtr> Parser::parseArgList() {
    std::vector<ast::ExprPtr> args;
    if (check(lexer::TokenKind::RParen)) return args; // empty arg list
    args.push_back(ast::make_expr(parseExpr()));
    while (check(lexer::TokenKind::Comma)) {
        advance();
        args.push_back(ast::make_expr(parseExpr()));
    }
    return args;
}

// ── Proposition parsing ────────────────────────────────────────────────────────
//
// Grammar (from docs/grammar.ebnf):
//   prop        = quantifier | biconditional
//   biconditional = implication [ iff biconditional ]
//   implication = "if" prop "then" prop | disjunction [ "->" implication ]
//   disjunction = conjunction { "or"  conjunction }
//   conjunction = negation    { "and" negation    }
//   negation    = "not" atomic_prop | atomic_prop
//   atomic_prop = "false" | "(" prop ")" | expr [rel expr]

ast::Prop Parser::parseProp() {
    using K = lexer::TokenKind;
    if (check(K::Forall) || check(K::KwFor) || check(K::Exists) || check(K::KwThere))
        return parseQuantifier();
    return parseBiconditional();
}

// (∀ | "for" "all" | ∃ | "there" "exists") <var> [ ":" <type> ] "," prop
ast::Prop Parser::parseQuantifier() {
    const auto loc = peek().loc;
    bool is_forall;

    if (check(lexer::TokenKind::Forall)) {
        is_forall = true;
        advance();
    } else if (check(lexer::TokenKind::Exists)) {
        is_forall = false;
        advance();
    } else if (check(lexer::TokenKind::KwFor)) {
        advance();
        expect(lexer::TokenKind::KwAll, "expected 'all' after 'for'");
        is_forall = true;
    } else { // KwThere
        advance();
        expect(lexer::TokenKind::Exists, "expected 'exists' after 'there'");
        is_forall = false;
    }

    // Collect one or more variable names (space-separated or "and"-separated).
    // E.g. "∀ x y z : Nat, P"  or  "∀ x and y : Nat, P"
    std::vector<std::string> vars;
    if (check(lexer::TokenKind::Identifier))
        vars.push_back(advance().lexeme);
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected variable name after quantifier"});

    // PB3: bounded binder — "∀ i < n, P(i)" desugars to "∀ i : Nat, i < n → P(i)".
    // Only valid for a single variable; checked before the multi-var loop.
    if (vars.size() == 1) {
        if (auto rel = as_rel_op(peek().kind); rel.has_value()) {
            advance(); // consume relational operator
            auto bound = parseExpr();
            expect(lexer::TokenKind::Comma, "expected ',' after bounded binder");
            auto body = parseProp();
            // Desugar: wrap body as "var rel bound → body"
            const std::string& var = vars[0];
            auto var_expr = ast::make_expr({loc, ast::ExprVar{var}});
            auto bound_expr = ast::make_expr(std::move(bound));
            auto guard = ast::make_prop({loc, ast::PropRel{var_expr, bound_expr, *rel}});
            auto impl_body = ast::make_prop(
                {loc, ast::PropImpl{std::move(guard), ast::make_prop(std::move(body))}});
            ast::TypeNode nat_type = ast::type_nat();
            ast::Prop p{loc, is_forall
                ? ast::PropNode{ast::PropForall{var, std::move(nat_type), std::move(impl_body)}}
                : ast::PropNode{ast::PropExists{var, std::move(nat_type), std::move(impl_body)}}};
            mark_end(p); return p;
        }
    }

    // Additional variables: either a bare identifier (space-separated) or "and <id>".
    while (true) {
        if (check(lexer::TokenKind::And) &&
            pos_ + 1 < tokens_.size() &&
            tokens_[pos_ + 1].kind == lexer::TokenKind::Identifier) {
            advance(); // consume "and"
            vars.push_back(advance().lexeme);
        } else if (check(lexer::TokenKind::Identifier)) {
            vars.push_back(advance().lexeme);
        } else {
            break;
        }
    }

    std::optional<ast::TypeNode> type;
    if (check(lexer::TokenKind::Colon)) {
        advance();
        if (check(lexer::TokenKind::Identifier) || check(lexer::TokenKind::LParen))
            type = parseType();
        else
            diag_.emit({diag::Severity::Error, peek().loc, "expected type name after ':'"});
    }

    expect(lexer::TokenKind::Comma, "expected ',' after quantifier binder");
    auto body = parseProp();

    // Build nested quantifiers from right to left:  ∀ x y : T, P  →  ∀ x : T, ∀ y : T, P
    for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
        auto type_copy = type; // each binder gets a copy of the type
        if (is_forall)
            body = {loc, ast::PropForall{*it, std::move(type_copy), ast::make_prop(std::move(body))}};
        else
            body = {loc, ast::PropExists{*it, std::move(type_copy), ast::make_prop(std::move(body))}};
    }
    mark_end(body); return body;
}

// A ↔ B  →  (A→B) ∧ (B→A)   (right-associative, desugared at parse time)
ast::Prop Parser::parseBiconditional() {
    const auto loc = peek().loc;
    auto lhs = parseImplication();
    if (check(lexer::TokenKind::Iff)) {
        advance();
        auto rhs = parseImplication();
        // Share both sub-props between A→B and B→A without extra copies.
        auto lp = ast::make_prop(lhs);
        auto rp = ast::make_prop(rhs);
        auto ab = ast::make_prop({loc, ast::PropImpl{lp, rp}});
        auto ba = ast::make_prop({loc, ast::PropImpl{rp, lp}});
        ast::Prop p{loc, ast::PropAnd{std::move(ab), std::move(ba)}};
        mark_end(p); return p;
    }
    return lhs;
}

ast::Prop Parser::parseImplication() {
    // Quantifiers bind loosely and may appear as the RHS of an implication or biconditional.
    // E.g. "P -> for all x, Q" parses as P -> (for all x, Q).
    {
        using K = lexer::TokenKind;
        if (check(K::Forall) || check(K::KwFor) || check(K::Exists) || check(K::KwThere))
            return parseQuantifier();
    }

    // "if" prop "then" prop
    if (check(lexer::TokenKind::KwIf)) {
        const auto loc = peek().loc;
        advance();
        auto lhs = parseProp();
        expect(lexer::TokenKind::KwThen, "expected 'then' after 'if <prop>'");
        auto rhs = parseProp();
        ast::Prop p{loc, ast::PropImpl{ast::make_prop(std::move(lhs)),
                                       ast::make_prop(std::move(rhs))}};
        mark_end(p); return p;
    }

    // disjunction [ "implies" / → disjunction ]
    const auto loc = peek().loc;
    auto lhs = parseDisjunction();
    if (check(lexer::TokenKind::Arrow) || check(lexer::TokenKind::KwImplies)) {
        advance();
        auto rhs = parseImplication(); // right-associative
        ast::Prop p{loc, ast::PropImpl{ast::make_prop(std::move(lhs)),
                                       ast::make_prop(std::move(rhs))}};
        mark_end(p); return p;
    }
    return lhs;
}

ast::Prop Parser::parseDisjunction() {
    const auto loc = peek().loc;
    auto lhs = parseConjunction();
    while (check(lexer::TokenKind::Or)) {
        advance();
        auto rhs = parseConjunction();
        lhs = {loc, ast::PropOr{ast::make_prop(std::move(lhs)),
                                ast::make_prop(std::move(rhs))}};
    }
    mark_end(lhs);
    return lhs;
}

ast::Prop Parser::parseConjunction() {
    const auto loc = peek().loc;
    auto lhs = parseNegation();
    while (check(lexer::TokenKind::And)) {
        advance();
        auto rhs = parseNegation();
        lhs = {loc, ast::PropAnd{ast::make_prop(std::move(lhs)),
                                 ast::make_prop(std::move(rhs))}};
    }
    mark_end(lhs);
    return lhs;
}

ast::Prop Parser::parseNegation() {
    if (check(lexer::TokenKind::Not)) {
        const auto loc = peek().loc;
        advance();
        auto inner = parseAtomicProp();
        ast::Prop p{loc, ast::PropNot{ast::make_prop(std::move(inner))}};
        mark_end(p); return p;
    }
    return parseAtomicProp();
}

// Map a token to a relational operator, or return nullopt.
static std::optional<ast::RelOp> as_rel_op(lexer::TokenKind k) {
    switch (k) {
        case lexer::TokenKind::Less:      return ast::RelOp::Lt;
        case lexer::TokenKind::Greater:   return ast::RelOp::Gt;
        case lexer::TokenKind::LessEq:    return ast::RelOp::LtEq;
        case lexer::TokenKind::GreaterEq: return ast::RelOp::GtEq;
        case lexer::TokenKind::Equals:    return ast::RelOp::Eq;
        case lexer::TokenKind::NotEq:     return ast::RelOp::NotEq;
        default:                          return std::nullopt;
    }
}

ast::Prop Parser::parseAtomicProp() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;

    // "false" / ⊥
    if (check(lexer::TokenKind::KwFalse)) {
        advance();
        ast::Prop p{loc, ast::PropFalse{}}; mark_end(p); return p;
    }

    // "true" / ⊤
    if (check(lexer::TokenKind::KwTrue)) {
        advance();
        ast::Prop p{loc, ast::PropTrue{}}; mark_end(p); return p;
    }

    // "(" ... ")"
    // Ambiguity: "(expr) [arith-op expr]* rel expr" vs "(prop)".
    //
    // Scan the tokens strictly inside the outer parentheses (depth 1 relative
    // to the opening '(').  If any propositional token appears at that depth,
    // the content is a proposition — take parseProp().  Otherwise, the parens
    // are arithmetic grouping; fall through to parseExpr() so the full
    // "(expr) [+/-/…] expr" expression becomes the LHS of a PropRel.
    //
    // "Propositional token" = relational operator OR logical connective
    // (∧ and, ∨ or, → implies ->, ¬ not, ↔ iff, ∀ for all, ∃ there exists).
    if (check(lexer::TokenKind::LParen)) {
        auto is_prop_token = [](lexer::TokenKind k) {
            switch (k) {
                // Relational operators
                case lexer::TokenKind::Less:
                case lexer::TokenKind::Greater:
                case lexer::TokenKind::LessEq:
                case lexer::TokenKind::GreaterEq:
                case lexer::TokenKind::Equals:
                case lexer::TokenKind::NotEq:
                case lexer::TokenKind::KwIn:
                case lexer::TokenKind::MemberOf:
                case lexer::TokenKind::NotMemberOf:
                case lexer::TokenKind::KwSubseteq:
                case lexer::TokenKind::SubseteqSym:
                case lexer::TokenKind::KwSubset:
                case lexer::TokenKind::SubsetSym:
                case lexer::TokenKind::KwSupseteq:
                case lexer::TokenKind::SuperseteqSym:
                // Logical connectives
                case lexer::TokenKind::And:         // ∧ / "and"
                case lexer::TokenKind::Or:          // ∨ / "or"
                case lexer::TokenKind::Arrow:       // → / "->"
                case lexer::TokenKind::KwImplies:   // "implies"
                case lexer::TokenKind::Iff:         // ↔ / "iff"
                case lexer::TokenKind::Forall:      // ∀ / "for all"
                case lexer::TokenKind::KwFor:       // "for" (part of "for all")
                case lexer::TokenKind::Exists:      // ∃ / "there exists"
                case lexer::TokenKind::KwThere:     // "there" (part of "there exists")
                case lexer::TokenKind::KwFalse:     // "false" / ⊥
                case lexer::TokenKind::KwTrue:      // "true"  / ⊤
                case lexer::TokenKind::Not:         // ¬ / "not"
                    return true;
                default:
                    return false;
            }
        };
        bool prop_inside = false;
        int depth = 0;
        for (std::size_t i = pos_; i < tokens_.size(); ++i) {
            auto k = tokens_[i].kind;
            if (k == K::LParen) { ++depth; continue; }
            if (k == K::RParen) { --depth; if (depth == 0) break; continue; }
            if (depth == 1 && is_prop_token(k)) { prop_inside = true; break; }
            // "not in" two-token form
            if (depth == 1 && k == K::Not && i + 1 < tokens_.size()
                && tokens_[i + 1].kind == K::KwIn) { prop_inside = true; break; }
        }

        if (prop_inside) {
            // Proposition grouping.
            advance(); // consume '('
            auto inner = parseProp();
            expect(lexer::TokenKind::RParen, "expected ')'");
            mark_end(inner);
            return inner;
        }
        // Arithmetic grouping: fall through to parseExpr() below.
    }

    // All other cases start an expression.  After parsing the lhs expression:
    //   • Followed by a relational operator → PropRel
    //   • Expression is a bare identifier   → Atomic (propositional variable)
    //   • Expression is a function call     → PropPred (predicate application)
    //   • Otherwise                         → error (arithmetic needs a rel op)
    auto lhs = parseExpr();

    auto rel = as_rel_op(peek().kind);
    if (rel) {
        advance();
        auto rhs = parseExpr();
        ast::Prop p{loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                      ast::make_expr(std::move(rhs)), *rel}};
        mark_end(p); return p;
    }

    // Set membership: x in S / x ∈ S
    if (check(K::KwIn) || check(K::MemberOf)) {
        advance();
        auto rhs = parseExpr();
        ast::Prop p{loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                      ast::make_expr(std::move(rhs)), ast::RelOp::In}};
        mark_end(p); return p;
    }
    // x not in S / x ∉ S
    if (check(K::NotMemberOf)) {
        advance();
        auto rhs = parseExpr();
        ast::Prop p{loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                      ast::make_expr(std::move(rhs)), ast::RelOp::NotIn}};
        mark_end(p); return p;
    }
    if (check(K::Not) && pos_ + 1 < tokens_.size()
        && tokens_[pos_ + 1].kind == K::KwIn) {
        advance(); advance(); // consume "not" then "in"
        auto rhs = parseExpr();
        ast::Prop p{loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                      ast::make_expr(std::move(rhs)), ast::RelOp::NotIn}};
        mark_end(p); return p;
    }
    // Subset relations
    if (check(K::KwSubseteq) || check(K::SubseteqSym)) {
        advance();
        auto rhs = parseExpr();
        ast::Prop p{loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                      ast::make_expr(std::move(rhs)), ast::RelOp::SubsetEq}};
        mark_end(p); return p;
    }
    if (check(K::KwSubset) || check(K::SubsetSym)) {
        advance();
        auto rhs = parseExpr();
        ast::Prop p{loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                      ast::make_expr(std::move(rhs)), ast::RelOp::Subset}};
        mark_end(p); return p;
    }
    if (check(K::KwSupseteq) || check(K::SuperseteqSym)) {
        advance();
        auto rhs = parseExpr();
        ast::Prop p{loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                      ast::make_expr(std::move(rhs)), ast::RelOp::SupersetEq}};
        mark_end(p); return p;
    }

    // Convert a no-rel expression to a propositional atom.
    if (const auto* v = std::get_if<ast::ExprVar>(&lhs.node)) {
        ast::Prop p{loc, ast::Atomic{v->name}}; mark_end(p); return p;
    }

    if (const auto* c = std::get_if<ast::ExprCall>(&lhs.node)) {
        ast::Prop p{loc, ast::PropPred{c->name, c->args}}; mark_end(p); return p;
    }

    diag_.emit({diag::Severity::Error, loc,
                "arithmetic expression `" + forall::pretty::to_string(lhs)
                + "` in proposition context requires a relational operator"});
    ast::Prop p{loc, ast::PropFalse{}}; mark_end(p); return p;
}

// ── Proof step parsing ─────────────────────────────────────────────────────────

// justification = ref { ("and" | "with") ref }
//               | "decide"
//               | "norm_num"
//               | "ring"
//
// "by decide"   — evaluates closed arithmetic; sentinel "__decide__"
// "by norm_num" — polynomial ring equality; sentinel "__norm_num__"
// "by ring"     — polynomial identity over commutative ring; sentinel "__ring__"
std::vector<std::string> Parser::parseJustification() {
    std::vector<std::string> refs;
    if (check(lexer::TokenKind::KwDecide)) {
        advance();
        refs.push_back("__decide__");
        return refs;
    }
    if (check(lexer::TokenKind::KwNormNum)) {
        advance();
        refs.push_back("__norm_num__");
        return refs;
    }
    if (check(lexer::TokenKind::KwRing)) {
        advance();
        refs.push_back("__ring__");
        return refs;
    }
    if (check(lexer::TokenKind::KwLinarith)) {
        advance();
        refs.push_back("__linarith__");
        return refs;
    }
    if (check(lexer::TokenKind::KwSimp)) {
        advance();
        refs.push_back("__simp__");
        return refs;
    }
    // "contra" is context-sensitive — only a tactic when it appears as an identifier
    // in a justification context (not as a theorem/hypothesis name).
    if (check(lexer::TokenKind::Identifier) && peek().lexeme == "contra") {
        advance();
        refs.push_back("__contra__");
        return refs;
    }
    if (!check(lexer::TokenKind::Identifier)) return refs;
    refs.push_back(std::string{advance().lexeme});
    while (check(lexer::TokenKind::And) || check(lexer::TokenKind::KwWith)) {
        advance();
        if (check(lexer::TokenKind::Identifier))
            refs.push_back(std::string{advance().lexeme});
    }
    return refs;
}

// Parse a type annotation starting from the current identifier token.
// Caller must guard with check(Identifier) before calling.
// Handles right-associative function types: Nat -> Real -> Prop.
ast::TypeNode Parser::parseType() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;

    // PB4: Tuple type "(Nat, Int)"  — TypeTuple with two or more elements.
    if (check(K::LParen)) {
        advance(); // consume '('
        std::vector<ast::TypeNode> elems;
        if (!check(K::Identifier)) {
            diag_.emit({diag::Severity::Error, peek().loc, "expected type inside '('"});
        } else {
            elems.push_back(parseType());
            while (check(K::Comma)) {
                advance();
                if (!check(K::Identifier)) {
                    diag_.emit({diag::Severity::Error, peek().loc, "expected type after ','"});
                    break;
                }
                elems.push_back(parseType());
            }
        }
        expect(K::RParen, "expected ')' after tuple type");
        if (elems.size() == 1)
            return std::move(elems[0]); // "(T)" == T
        return ast::type_tuple(std::move(elems));
    }

    const auto name = advance().lexeme;
    ast::TypeNode base;
    if (name == "Nat")       base = ast::TypeNode{ast::TypeNat{}};
    else if (name == "Int")  base = ast::TypeNode{ast::TypeInt{}};
    else if (name == "Rat")  base = ast::TypeNode{ast::TypeRat{}};
    else if (name == "Real") base = ast::TypeNode{ast::TypeReal{}};
    else if (name == "Prop") base = ast::TypeNode{ast::TypeProp{}};
    else if (name == "Set") {
        // Set T — element type is the next type (parsed recursively).
        if (!check(K::Identifier)) {
            diag_.emit({diag::Severity::Error, loc,
                        "expected element type after 'Set'"});
            return ast::TypeNode{ast::TypeUser{"Set"}};
        }
        auto elem = parseType();
        base = ast::TypeNode{ast::TypeSet{std::make_shared<ast::TypeNode>(std::move(elem))}};
    }
    else                     base = ast::TypeNode{ast::TypeUser{name}};

    // Right-associative function type: T -> U  (same token as implication arrow,
    // but used here in a type-annotation context so there is no ambiguity).
    if (check(K::Arrow)) {
        advance(); // consume ->
        if (!check(K::Identifier)) {
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected type after '->'"});
            return base;
        }
        auto codomain = parseType();
        return ast::type_fun(std::move(base), std::move(codomain));
    }
    return base;
}

// let <name> be [a] <type>
// let <name> = <expr>
ast::Step Parser::parseLetStep() {
    const auto loc = peek().loc;
    advance(); // consume "let"
    std::string var;
    if (check(lexer::TokenKind::Identifier))
        var = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected variable name after 'let'"});

    // let x = expr  — term-level definition
    if (check(lexer::TokenKind::Equals)) {
        advance(); // consume "="
        auto expr = parseExpr();
        return {loc, ast::LetStep{std::move(var), std::nullopt,
                                  ast::make_expr(std::move(expr))}};
    }

    // let x be [a] T  — type annotation (original form)
    std::optional<ast::TypeNode> type;
    if (check(lexer::TokenKind::KwBe)) {
        advance();
        consumeArticle();
        if (check(lexer::TokenKind::Identifier) || check(lexer::TokenKind::LParen))
            type = parseType();
    }
    return {loc, ast::LetStep{std::move(var), std::move(type), std::nullopt}};
}

// take <var> [: <type>]
// Introduces a fresh term variable for ∀-intro.
ast::Step Parser::parseTakeStep() {
    const auto loc = peek().loc;
    advance(); // consume "take"
    std::string var;
    if (check(lexer::TokenKind::Identifier))
        var = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected variable name after 'take'"});

    std::optional<ast::TypeNode> type;
    if (check(lexer::TokenKind::Colon)) {
        advance(); // consume ':'
        if (check(lexer::TokenKind::Identifier) || check(lexer::TokenKind::LParen))
            type = parseType();
        else
            diag_.emit({diag::Severity::Error, peek().loc, "expected type name after ':'"});
    }
    return {loc, ast::TakeStep{std::move(var), std::move(type)}};
}

// obtain <name> from <ref>
//   case <var> [: <type>] , <hyp_name> : <hyp_prop> => <steps...> [ "done" ]
ast::Step Parser::parseObtainStep() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "obtain"

    std::string name;
    if (check(K::Identifier))
        name = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected result name after 'obtain'"});

    expect(K::KwFrom, "expected 'from' after result name");

    std::string exists_ref;
    if (check(K::Identifier))
        exists_ref = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected hypothesis name after 'from'"});

    expect(K::KwCase, "expected 'case' to start the obtain arm");

    std::string var;
    if (check(K::Identifier))
        var = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected variable name in 'case'"});

    std::optional<ast::TypeNode> type;
    if (check(K::Colon)) {
        advance(); // consume ':'
        if (check(K::Identifier) || check(K::LParen))
            type = parseType();
        else
            diag_.emit({diag::Severity::Error, peek().loc, "expected type name after ':'"});
    }

    expect(K::Comma, "expected ',' separating variable from hypothesis name");

    std::string hyp_name;
    if (check(K::Identifier))
        hyp_name = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected hypothesis name"});

    expect(K::Colon, "expected ':' before hypothesis proposition");
    auto hyp_prop = parseProp();
    expect(K::FatArrow, "expected '=>' after hypothesis proposition");

    std::vector<std::unique_ptr<ast::Step>> steps;
    while (!isAtEnd()
           && !check(K::KwEnd)
           && !check(K::KwDone))
        steps.push_back(std::make_unique<ast::Step>(parseStep()));
    if (check(K::KwDone))
        advance(); // consume optional "done" terminator

    return {loc, ast::ObtainStep{
        std::move(name), std::move(exists_ref),
        std::move(var), std::move(type),
        std::move(hyp_name), std::move(hyp_prop),
        std::move(steps)
    }};
}

// suppose [for contradiction :] [name :] prop
ast::Step Parser::parseSupposeStep() {
    const auto loc = peek().loc;
    advance(); // consume "suppose"

    bool for_contradiction = false;
    if (check(lexer::TokenKind::KwFor)) {
        advance();
        if (!expect(lexer::TokenKind::KwContradiction, "expected 'contradiction' after 'for'"))
            return {loc, ast::SupposeStep{}};
        // Accept ":" or "that" (English: "suppose for contradiction that P")
        if (check(lexer::TokenKind::Identifier) && peek().lexeme == "that")
            advance();
        else
            expect(lexer::TokenKind::Colon, "expected ':' or 'that' after 'contradiction'");
        for_contradiction = true;
    }

    // Optional "name :" label
    std::optional<std::string> name;
    if (check(lexer::TokenKind::Identifier) && pos_ + 1 < tokens_.size()
        && tokens_[pos_ + 1].kind == lexer::TokenKind::Colon)
    {
        name = std::string{advance().lexeme};
        advance(); // consume ':'
    }

    auto prop = parseProp();
    return {loc, ast::SupposeStep{for_contradiction, std::move(name), std::move(prop)}};
}

// have <name> : <prop> by <justification> [at <expr>]
// <name> may be "_" for an anonymous step; the checker assigns a fresh internal name.
ast::Step Parser::parseHaveStep() {
    const auto loc = peek().loc;
    advance(); // consume "have"

    std::string name;
    if (check(lexer::TokenKind::Identifier)) {
        name = advance().lexeme; // includes "_"
    } else {
        diag_.emit({diag::Severity::Error, peek().loc, "expected hypothesis name after 'have'"});
    }

    expect(lexer::TokenKind::Colon, "expected ':' after hypothesis name");
    auto prop = parseProp();
    // Accept "from" as a natural alias for "by": "have h : P from premise"
    if (check(lexer::TokenKind::KwFrom))
        advance();
    else
        expect(lexer::TokenKind::KwBy, "expected 'by' or 'from' after proposition");
    auto refs = parseJustification();
    std::optional<ast::ExprPtr> witness;
    if (check(lexer::TokenKind::KwAt)) {
        advance();
        witness = ast::make_expr(parseExpr());
    }
    return {loc, ast::HaveStep{std::move(name), std::move(prop), std::move(refs), std::move(witness)}};
}

// then [<prop>] [(by | from) <justification> [at <expr>]]
// RL4: if no proposition follows "then", emits a "__qed__" sentinel;
// the checker substitutes decl.statement as the goal.
ast::Step Parser::parseThenStep() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "then"

    // Detect bare "then" (no prop): next token is "by"/"from", a proof terminator,
    // a step keyword, or EOF.  In those cases use the __qed__ sentinel.
    // Note: "therefore"/"thus" map to KwThen at the lexer level.
    auto is_bare_then = [&]() {
        switch (peek().kind) {
            case K::KwBy: case K::KwFrom:
            case K::KwEnd: case K::Eof:
            case K::KwHave: case K::KwThen: case K::KwSuppose:
            case K::KwContradiction: case K::KwCases: case K::KwLet:
            case K::KwTake: case K::KwObtain: case K::KwInduction:
            case K::KwShow: case K::KwExact: case K::KwRewrite:
                return true;
            default:
                return false;
        }
    };

    std::vector<std::string> refs;
    std::optional<ast::ExprPtr> witness;

    if (is_bare_then()) {
        // Goal-close form (RL4): defer prop to checker via sentinel.
        ast::Prop dummy{loc, ast::PropFalse{}};
        refs.push_back("__qed__");
        if (check(K::KwBy) || check(K::KwFrom)) {
            advance();
            auto extra = parseJustification();
            refs.insert(refs.end(), extra.begin(), extra.end());
        }
        return {loc, ast::ThenStep{std::move(dummy), std::move(refs), std::nullopt}};
    }

    auto prop = parseProp();
    if (check(K::KwBy) || check(K::KwFrom)) {
        advance();
        refs = parseJustification();
        if (check(K::KwAt)) {
            advance();
            witness = ast::make_expr(parseExpr());
        }
    }
    return {loc, ast::ThenStep{std::move(prop), std::move(refs), std::move(witness)}};
}

// contradiction (":" | "from") <justification>
ast::Step Parser::parseContradictionStep() {
    const auto loc = peek().loc;
    advance(); // consume "contradiction"
    if (check(lexer::TokenKind::KwFrom))
        advance(); // accept "from" as natural alias for ":"
    else
        expect(lexer::TokenKind::Colon, "expected ':' or 'from' after 'contradiction'");
    auto refs = parseJustification();
    return {loc, ast::ContradictionStep{std::move(refs)}};
}

// cases <name> : <ref>
//   case <arm_name> : <prop> => { step }
//   case <arm_name> : <prop> => { step }
//
// Each arm's step list runs until the next 'case' or 'end'/'qed'.
// This means 'cases' must be the last step before the proof terminator.
ast::Step Parser::parseCasesStep() {
    const auto loc = peek().loc;
    advance(); // consume "cases"

    // Grammar: "cases [<name> :] <ref>"
    // If an identifier is followed by ':', it is the result label; otherwise
    // the identifier is the disjunct ref and the result is unnamed (RL5).
    std::string name;
    std::string disjunct_ref;

    if (check(lexer::TokenKind::Identifier)) {
        const std::string first = std::string{peek().lexeme};
        if (pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == lexer::TokenKind::Colon)
        {
            // Old form: cases <name> : <ref>
            advance();           // consume name
            advance();           // consume ':'
            name = first;
            if (check(lexer::TokenKind::Identifier))
                disjunct_ref = advance().lexeme;
            else
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected hypothesis ref after 'cases <name>:'"});
        } else {
            // New form: cases <ref>  — result label is auto-generated
            advance();           // consume ref
            disjunct_ref = first;
            // name left empty; checker will fill it
        }
    } else {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected hypothesis ref after 'cases'"});
    }

    std::vector<ast::CaseArm> arms;
    while (check(lexer::TokenKind::KwCase)) {
        advance(); // consume "case"

        std::string arm_name;
        if (check(lexer::TokenKind::Identifier))
            arm_name = advance().lexeme;
        else
            diag_.emit({diag::Severity::Error, peek().loc, "expected arm name after 'case'"});

        expect(lexer::TokenKind::Colon,    "expected ':' after arm name");
        auto arm_prop = parseProp();
        expect(lexer::TokenKind::FatArrow, "expected '=>' after arm proposition");

        std::vector<std::unique_ptr<ast::Step>> arm_steps;
        while (!isAtEnd()
               && !check(lexer::TokenKind::KwCase)
               && !check(lexer::TokenKind::KwEnd)
               && !check(lexer::TokenKind::KwDone))
            arm_steps.push_back(std::make_unique<ast::Step>(parseStep()));
        if (check(lexer::TokenKind::KwDone))
            advance(); // consume optional per-arm "done" terminator

        arms.push_back(ast::CaseArm{std::move(arm_name), std::move(arm_prop), std::move(arm_steps)});
    }

    return {loc, ast::CasesStep{std::move(name), std::move(disjunct_ref), std::move(arms)}};
}

// induction <result_name> on <var>
//   base:
//     <base_steps...>
//   inductive:
//     <inductive_steps...>
//
// Sub-blocks terminate at `base` / `inductive` / `end` / `qed` / EOF.
// The induction step may appear anywhere in a proof (does not need to be last).
ast::Step Parser::parseInductionStep() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "induction"

    std::string name;
    if (check(K::Identifier))
        name = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected result name after 'induction'"});

    expect(K::KwOn, "expected 'on' after induction result name");

    std::string var;
    if (check(K::Identifier))
        var = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected variable name after 'induction <name> on'"});

    expect(K::Colon, "expected ':' after induction variable to introduce predicate P(n)");
    auto body = parseProp();

    // "base" and "inductive" are lexed as identifiers (context-sensitive).
    auto is_ident = [&](std::string_view s) {
        return check(K::Identifier) && peek().lexeme == s;
    };

    // Helper: is the current token a block terminator for induction sub-blocks?
    auto is_block_end = [&]() {
        return isAtEnd()
            || is_ident("base") || is_ident("inductive")
            || check(K::KwEnd);
    };

    // base: block
    if (!is_ident("base")) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected 'base:' after induction header"});
    } else {
        advance(); // consume "base"
    }
    expect(K::Colon, "expected ':' after 'base'");
    std::vector<std::unique_ptr<ast::Step>> base_steps;
    while (!is_block_end())
        base_steps.push_back(std::make_unique<ast::Step>(parseStep()));

    // inductive: block
    if (!is_ident("inductive")) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected 'inductive:' after base block"});
    } else {
        advance(); // consume "inductive"
    }
    expect(K::Colon, "expected ':' after 'inductive'");
    std::vector<std::unique_ptr<ast::Step>> ind_steps;
    while (!is_block_end())
        ind_steps.push_back(std::make_unique<ast::Step>(parseStep()));

    return {loc, ast::InductionStep{std::move(name), std::move(var), std::move(body),
                                    std::move(base_steps), std::move(ind_steps)}};
}

ast::Step Parser::parseStep() {
    using K = lexer::TokenKind;
    if (check(K::KwLet))          return parseLetStep();
    if (check(K::KwTake))         return parseTakeStep();
    if (check(K::KwObtain))       return parseObtainStep();
    if (check(K::KwSuppose))      return parseSupposeStep();
    // "we have" — two-token phrase aliasing "have"
    if (check(K::Identifier) && peek().lexeme == "we"
            && pos_ + 1 < tokens_.size() && tokens_[pos_ + 1].kind == K::KwHave)
        { advance(); return parseHaveStep(); }
    if (check(K::KwHave))         return parseHaveStep();
    if (check(K::KwThen))         return parseThenStep();
    if (check(K::KwContradiction)) return parseContradictionStep();
    if (check(K::KwCases))        return parseCasesStep();
    if (check(K::KwInduction))    return parseInductionStep();

    // rewrite [←/<-] h — equality rewriting step (MS1)
    if (check(K::KwRewrite)) {
        const auto loc = peek().loc;
        advance(); // consume "rewrite"
        // Optional reverse marker: ← (U+2190, lexed as some token) or literal "<-"
        // We check for the Arrow token used in "<-" direction — but Arrow is "→"/"->".
        // For simplicity, accept the identifier "←" or the lexeme "<-" as a reverse flag.
        // Actually use: check for a bare '<' followed by '-' identifier, or accept
        // the identifier token with lexeme "←".
        bool rev = false;
        if (check(K::Identifier) && peek().lexeme == "\xe2\x86\x90") {
            rev = true; advance(); // ← U+2190
        }
        std::string ref;
        if (check(K::Identifier))
            ref = advance().lexeme;
        else
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected hypothesis name after 'rewrite'"});
        return {loc, ast::RewriteStep{std::move(ref), rev}};
    }

    // apply h — backward implication application step (MS2)
    // "apply" is context-sensitive: only a step keyword when it appears alone
    // as an identifier (not as a function call "apply(...)").
    if (check(K::Identifier) && peek().lexeme == "apply"
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Identifier) {
        const auto loc = peek().loc;
        advance(); // consume "apply"
        std::string ref = advance().lexeme;
        return {loc, ast::ApplyStep{std::move(ref)}};
    }

    // suffices h : P — MS5: reduce goal to proving P, auto-searching for P → goal.
    // "suffices" is context-sensitive (not a reserved keyword).
    // Syntax: suffices <name> : <prop>
    // Semantics: look for <name> : P → current_goal already in scope and apply it.
    // This is essentially `apply <name>` where the user has already proved P → goal.
    if (check(K::Identifier) && peek().lexeme == "suffices"
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Identifier) {
        const auto loc = peek().loc;
        advance(); // consume "suffices"
        std::string name;
        if (check(K::Identifier))
            name = advance().lexeme;
        // Consume optional ": P" (the prop is informational, not used by checker)
        if (check(K::Colon)) {
            advance();
            parseProp(); // parse and discard — checker uses h's type
        }
        // Desugar to ApplyStep: the checker will verify h : P → current_goal
        return {loc, ast::ApplyStep{std::move(name)}};
    }

    // show P — goal annotation step (MS4)
    if (check(K::KwShow)) {
        const auto loc = peek().loc;
        advance(); // consume "show"
        auto prop = parseProp();
        return {loc, ast::ShowStep{std::move(prop)}};
    }

    // exact h — close goal directly via a named hypothesis (MS3)
    if (check(K::KwExact)) {
        const auto loc = peek().loc;
        advance(); // consume "exact"
        std::string ref;
        if (check(K::Identifier))
            ref = advance().lexeme;
        else
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected hypothesis name after 'exact'"});
        return {loc, ast::ExactStep{std::move(ref)}};
    }

    const auto loc = peek().loc;
    diag_.emit({diag::Severity::Error, loc,
                "expected proof step; got '" + peek().lexeme + "'"});
    advance();
    return {loc, ast::LetStep{}}; // silently skipped by the checker
}

ast::ProofBlock Parser::parseProofBlock() {
    ast::ProofBlock block;
    advance(); // consume "proof"
    while (!isAtEnd() && !check(lexer::TokenKind::KwEnd))
        block.steps.push_back(parseStep());
    expect(lexer::TokenKind::KwEnd, "expected 'end' to close proof block");
    return block;
}

// ── Declaration parsing ────────────────────────────────────────────────────────

// definition <name> { "(" <var> ":" <type> ")" } ":" <prop>
std::optional<ast::DeclPtr> Parser::parseDefinition() {
    const auto loc = peek().loc;
    advance(); // consume "definition"

    if (!check(lexer::TokenKind::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected definition name"});
        return std::nullopt;
    }
    std::string name{advance().lexeme};

    // Parse optional parameter list: { "(" id ":" type ")" }
    std::vector<ast::Param> params;
    while (check(lexer::TokenKind::LParen)) {
        advance(); // (
        std::string pname;
        if (check(lexer::TokenKind::Identifier))
            pname = advance().lexeme;
        else
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected parameter name"});
        expect(lexer::TokenKind::Colon, "expected ':' in definition parameter");
        ast::TypeNode ptype{ast::TypeUser{"?"}};
        if (check(lexer::TokenKind::Identifier) || check(lexer::TokenKind::LParen))
            ptype = parseType();
        expect(lexer::TokenKind::RParen, "expected ')' to close parameter");
        params.push_back({std::move(pname), std::move(ptype)});
    }

    expect(lexer::TokenKind::Colon, "expected ':' after definition name");
    auto prop = parseProp();
    auto decl = std::make_unique<ast::Decl>(ast::DeclKind::Definition, std::move(name), loc,
                                            std::move(prop), std::nullopt);
    decl->params = std::move(params);
    return decl;
}

std::optional<ast::DeclPtr> Parser::parseAxiom() {
    const auto loc = peek().loc;
    advance(); // consume "axiom"

    if (!check(lexer::TokenKind::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected axiom name"});
        return std::nullopt;
    }
    std::string name{advance().lexeme};
    expect(lexer::TokenKind::Colon, "expected ':' after axiom name");
    auto prop = parseProp();
    return std::make_unique<ast::Decl>(ast::DeclKind::Axiom, std::move(name), loc,
                                       std::move(prop), std::nullopt);
}

std::optional<ast::DeclPtr> Parser::parseTheorem(ast::DeclKind kind) {
    const auto loc = peek().loc;
    advance(); // consume "theorem" or "lemma"

    if (!check(lexer::TokenKind::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected theorem name"});
        return std::nullopt;
    }
    std::string name{advance().lexeme};
    expect(lexer::TokenKind::Colon, "expected ':' after theorem name");
    auto prop = parseProp();

    std::optional<ast::ProofBlock> proof;
    if (check(lexer::TokenKind::KwProof))
        proof = parseProofBlock();

    return std::make_unique<ast::Decl>(kind, std::move(name), loc,
                                       std::move(prop), std::move(proof));
}

std::optional<ast::DeclPtr> Parser::parseImport() {
    const auto loc = peek().loc;
    advance(); // consume "import"

    if (!check(lexer::TokenKind::StringLit)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected string literal after 'import'"});
        return std::nullopt;
    }

    std::string raw = advance().lexeme; // includes surrounding quotes
    // Strip quotes: "file.forall" → file.forall
    if (raw.size() >= 2 && raw.front() == '"' && raw.back() == '"')
        raw = raw.substr(1, raw.size() - 2);

    return std::make_unique<ast::Decl>(ast::DeclKind::Import, std::move(raw), loc,
                                       ast::Prop{loc, ast::PropFalse{}}, std::nullopt);
}

// instance <TypeName> : <ClassName>
// e.g.  instance Real : Field
std::optional<ast::DeclPtr> Parser::parseInstance() {
    const auto loc = peek().loc;
    advance(); // consume "instance"

    if (!check(lexer::TokenKind::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected type name after 'instance'"});
        return std::nullopt;
    }
    std::string type_name = peek().lexeme;
    advance();

    if (!expect(lexer::TokenKind::Colon, "expected ':' after type name in instance declaration"))
        return std::nullopt;

    if (!check(lexer::TokenKind::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected class name after ':' in instance declaration"});
        return std::nullopt;
    }
    std::string class_name = peek().lexeme;
    advance();

    auto decl = std::make_unique<ast::Decl>(
        ast::DeclKind::Instance, type_name, loc,
        ast::Prop{loc, ast::PropFalse{}}, std::nullopt);
    decl->instance_class = std::move(class_name);
    return decl;
}

std::optional<ast::DeclPtr> Parser::parseDeclaration() {
    using K = lexer::TokenKind;
    if (check(K::KwAxiom))      return parseAxiom();
    if (check(K::KwDefinition)) return parseDefinition();
    if (check(K::KwTheorem))    return parseTheorem(ast::DeclKind::Theorem);
    if (check(K::KwLemma))      return parseTheorem(ast::DeclKind::Lemma);
    if (check(K::KwImport))     return parseImport();
    if (check(K::KwInstance))   return parseInstance();

    diag_.emit({diag::Severity::Error, peek().loc,
                "expected 'axiom', 'definition', 'theorem', 'lemma', or 'instance'; got '"
                + peek().lexeme + "'"});
    advance();
    return std::nullopt;
}

void Parser::syncToDeclaration() {
    using K = lexer::TokenKind;
    while (!isAtEnd()
           && !check(K::KwAxiom) && !check(K::KwDefinition)
           && !check(K::KwTheorem) && !check(K::KwLemma)
           && !check(K::KwImport) && !check(K::KwInstance)) {
        advance();
    }
}

ast::Module Parser::parse() {
    ast::Module mod;
    while (!isAtEnd()) {
        if (auto decl = parseDeclaration())
            mod.decls.push_back(std::move(*decl));
        else
            syncToDeclaration();
    }
    return mod;
}

} // namespace forall::parser
