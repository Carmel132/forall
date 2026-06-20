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
    //   base.field   →  ExprField
    while (check(lexer::TokenKind::LBracket) || check(lexer::TokenKind::Bang)
           || check(lexer::TokenKind::Dot)) {
        if (check(lexer::TokenKind::LBracket)) {
            advance();
            auto idx = parseExpr();
            expect(lexer::TokenKind::RBracket, "expected ']' after index expression");
            base = {loc, ast::ExprIndex{ast::make_expr(std::move(base)),
                                        ast::make_expr(std::move(idx))}};
        } else if (check(lexer::TokenKind::Dot)) {
            advance(); // consume '.'
            std::string field_name;
            // Accept any word token as a field name (identifiers and keywords)
            if (check(lexer::TokenKind::Identifier)) {
                field_name = advance().lexeme;
            } else if (peek().kind != lexer::TokenKind::Eof
                       && peek().kind != lexer::TokenKind::Error) {
                // Accept keyword tokens as field names (e.g. "mul", "inv")
                const auto& lex = peek().lexeme;
                bool is_word = !lex.empty();
                for (char c : lex)
                    if (!std::isalnum(static_cast<unsigned char>(c)) && c != '_')
                        { is_word = false; break; }
                if (is_word) {
                    field_name = lex;
                    advance();
                } else {
                    diag_.emit({diag::Severity::Error, peek().loc,
                                "expected field name after '.'"});
                }
            } else {
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected field name after '.'"});
            }
            base = {loc, ast::ExprField{ast::make_expr(std::move(base)),
                                        std::move(field_name)}};
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

    // Bounded binder — desugars to an implication/conjunction guard.
    // Only valid for a single variable; checked before the multi-var loop.
    //   ∀ i < n,    P(i)  →  ∀ i : Nat, i < n → P(i)
    //   ∃ n >= N,   P(n)  →  ∃ n : Nat, n >= N ∧ P(n)
    //   ∀ x ∈ S,   P(x)  →  ∀ x,       x ∈ S → P(x)
    //   ∃ x ∈ S,   P(x)  →  ∃ x,       x ∈ S ∧ P(x)
    if (vars.size() == 1) {
        const bool is_in_binder = check(lexer::TokenKind::KwIn)
                                || check(lexer::TokenKind::MemberOf);
        if (auto rel = as_rel_op(peek().kind); rel.has_value() || is_in_binder) {
            ast::RelOp binder_rel;
            if (is_in_binder) {
                binder_rel = ast::RelOp::In;
            } else {
                binder_rel = *rel;
            }
            advance(); // consume relational operator or 'in'
            auto bound = parseExpr();
            expect(lexer::TokenKind::Comma, "expected ',' after bounded binder");
            auto body = parseProp();
            const std::string& var = vars[0];
            auto var_expr  = ast::make_expr({loc, ast::ExprVar{var}});
            auto bound_expr = ast::make_expr(std::move(bound));
            auto guard = ast::make_prop({loc, ast::PropRel{var_expr, bound_expr, binder_rel}});
            // ∀: guard → body;  ∃: guard ∧ body
            auto guarded_body = is_forall
                ? ast::make_prop({loc, ast::PropImpl{std::move(guard), ast::make_prop(std::move(body))}})
                : ast::make_prop({loc, ast::PropAnd {std::move(guard), ast::make_prop(std::move(body))}});
            // Type annotation: Nat for order-comparison binders; nullopt for ∈ (element type unknown at parse time).
            std::optional<ast::TypeNode> binder_type = is_in_binder
                ? std::nullopt
                : std::optional<ast::TypeNode>{ast::type_nat()};
            ast::Prop p{loc, is_forall
                ? ast::PropNode{ast::PropForall{var, std::move(binder_type), std::move(guarded_body)}}
                : ast::PropNode{ast::PropExists{var, std::move(binder_type), std::move(guarded_body)}}};
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
// "by definition of X" / "by axiom of X" / "by lemma X" / "by theorem X"
//       — qualifier words discarded; only X matters
// "by hypothesis" / "by assumption" → sentinels "__hypothesis__" / "__assumption__"
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
    if (check(lexer::TokenKind::KwOmega)) {
        advance();
        refs.push_back("__omega__");
        return refs;
    }
    if (check(lexer::TokenKind::KwNlinarith)) {
        advance();
        refs.push_back("__nlinarith__");
        return refs;
    }
    if (check(lexer::TokenKind::KwSimp)) {
        advance();
        refs.push_back("__simp__");
        // Optional lemma set: simp [h1, h2, ...]
        if (check(lexer::TokenKind::LBracket)) {
            advance(); // consume '['
            while (!isAtEnd() && !check(lexer::TokenKind::RBracket)) {
                if (check(lexer::TokenKind::Identifier))
                    refs.push_back(std::string{advance().lexeme});
                if (check(lexer::TokenKind::Comma))
                    advance();
            }
            if (check(lexer::TokenKind::RBracket))
                advance(); // consume ']'
        }
        return refs;
    }
    if (check(lexer::TokenKind::KwFieldSimp)) {
        advance();
        refs.push_back("__field_simp__");
        return refs;
    }
    if (check(lexer::TokenKind::KwPositivity)) {
        advance();
        refs.push_back("__positivity__");
        return refs;
    }
    if (check(lexer::TokenKind::KwGcongr)) {
        advance();
        refs.push_back("__gcongr__");
        return refs;
    }
    // "refl" / "symm" / "trans" / "congr" — equality tactics; context-sensitive identifiers
    if (check(lexer::TokenKind::Identifier) && peek().lexeme == "refl") {
        advance();
        refs.push_back("__refl__");
        return refs;
    }
    if (check(lexer::TokenKind::Identifier) && peek().lexeme == "funext") {
        advance();
        refs.push_back("__funext__");
        if (check(lexer::TokenKind::Identifier))
            refs.push_back(std::string{advance().lexeme});
        return refs;
    }
    if (check(lexer::TokenKind::Identifier) && peek().lexeme == "symm") {
        advance();
        refs.push_back("__symm__");
        if (check(lexer::TokenKind::Identifier))
            refs.push_back(std::string{advance().lexeme});
        return refs;
    }
    if (check(lexer::TokenKind::Identifier) && peek().lexeme == "trans") {
        advance();
        refs.push_back("__trans__");
        if (check(lexer::TokenKind::Identifier)) refs.push_back(std::string{advance().lexeme});
        if (check(lexer::TokenKind::And) || check(lexer::TokenKind::KwWith)) advance();
        if (check(lexer::TokenKind::Identifier)) refs.push_back(std::string{advance().lexeme});
        return refs;
    }
    if (check(lexer::TokenKind::Identifier) && peek().lexeme == "congr") {
        advance();
        refs.push_back("__congr__");
        if (check(lexer::TokenKind::Identifier))
            refs.push_back(std::string{advance().lexeme});
        return refs;
    }
    // "eq_subst h_eq h_pb" — substitution of equals: P(a) from a=b and P(b)
    if (check(lexer::TokenKind::Identifier) && peek().lexeme == "eq_subst") {
        advance();
        refs.push_back("__eq_subst__");
        if (check(lexer::TokenKind::Identifier)) refs.push_back(std::string{advance().lexeme});
        if (check(lexer::TokenKind::And) || check(lexer::TokenKind::KwWith)) advance();
        if (check(lexer::TokenKind::Identifier)) refs.push_back(std::string{advance().lexeme});
        return refs;
    }
    // "exact h" — cite hypothesis h exactly; goal must match h's proposition.
    if (check(lexer::TokenKind::KwExact)) {
        advance(); // consume "exact"
        refs.push_back("__exact__");
        if (check(lexer::TokenKind::Identifier))
            refs.push_back(std::string{advance().lexeme});
        return refs;
    }
    // "contra" is context-sensitive — only a tactic when it appears as an identifier
    // in a justification context (not as a theorem/hypothesis name).
    if (check(lexer::TokenKind::Identifier) && peek().lexeme == "contra") {
        advance();
        refs.push_back("__contra__");
        return refs;
    }
    // "contrapositive" — prove A → B by showing ¬B → ¬A
    if (check(lexer::TokenKind::Identifier) && peek().lexeme == "contrapositive") {
        advance();
        refs.push_back("__contrapositive__");
        return refs;
    }
    // "by hypothesis" / "by assumption" — resolve to the unique active assumption
    if (check(lexer::TokenKind::Identifier)
            && (peek().lexeme == "hypothesis" || peek().lexeme == "assumption")) {
        std::string sentinel = (peek().lexeme == "hypothesis")
                               ? "__hypothesis__" : "__assumption__";
        advance();
        refs.push_back(std::move(sentinel));
        return refs;
    }
    // Qualifiers like "by definition of X" / "by axiom of X" are keyword tokens,
    // so we cannot early-return if the token is not an Identifier — check below.
    {
        // optional qualifier words before the ref name.
        // "definition of" — 2 tokens to discard; "definition" is KwDefinition
        // "axiom of"      — 2 tokens to discard; "axiom" is KwAxiom
        // "lemma"         — 1 token to discard; "lemma" is KwLemma
        // "theorem"       — 1 token to discard; "theorem" is KwTheorem
        // These are keyword tokens (not Identifiers), so we check token kind.
        auto skip_nl6_qualifier = [&]() {
            using K2 = lexer::TokenKind;
            // "definition of" or "axiom of" — 2 tokens
            if ((check(K2::KwDefinition) || check(K2::KwAxiom))
                    && pos_ + 1 < tokens_.size()
                    && tokens_[pos_ + 1].kind == K2::Identifier
                    && tokens_[pos_ + 1].lexeme == "of") {
                advance(); // consume "definition"/"axiom"
                advance(); // consume "of"
            }
            // "lemma" — 1 token, only if followed by an identifier (the ref name)
            else if (check(K2::KwLemma)
                    && pos_ + 1 < tokens_.size()
                    && tokens_[pos_ + 1].kind == K2::Identifier) {
                advance(); // consume "lemma"
            }
            // "theorem" — 1 token, only if followed by an identifier (the ref name)
            else if (check(K2::KwTheorem)
                    && pos_ + 1 < tokens_.size()
                    && tokens_[pos_ + 1].kind == K2::Identifier) {
                advance(); // consume "theorem"
            }
        };

        // Parse a single reference, which may be dotted: "M.my_axiom".
        auto parse_one_ref = [&]() -> std::string {
            std::string name{advance().lexeme}; // consume the identifier
            // if followed by '.' and another identifier, join as "X.y".
            if (check(lexer::TokenKind::Dot)
                    && pos_ + 1 < tokens_.size()
                    && tokens_[pos_ + 1].kind == lexer::TokenKind::Identifier) {
                advance(); // consume '.'
                name += '.';
                name += std::string{advance().lexeme}; // consume field name
            }
            return name;
        };

        // Helper: emit the right ref string for the current identifier token,
        // handling the "it" sentinel before falling through to parse_one_ref.
        auto parse_one_ref_or_sentinel = [&]() {
            if (check(lexer::TokenKind::Identifier) && peek().lexeme == "it") {
                advance();
                refs.push_back("__it__");
            } else if (check(lexer::TokenKind::Identifier)) {
                refs.push_back(parse_one_ref());
            }
        };

        skip_nl6_qualifier();
        if (!check(lexer::TokenKind::Identifier)) return refs;
        parse_one_ref_or_sentinel();
        while (check(lexer::TokenKind::And) || check(lexer::TokenKind::KwWith)) {
            advance();
            skip_nl6_qualifier();
            parse_one_ref_or_sentinel();
        }
    }
    return refs;
}

// Parse a type annotation starting from the current identifier token.
// Caller must guard with check(Identifier) before calling.
// Handles right-associative function types: Nat -> Real -> Prop.
ast::TypeNode Parser::parseType() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;

    // Tuple type "(Nat, Int)"  — TypeTuple with two or more elements.
    // Pi type "(x : A) -> B"  — TypePi, distinguished from tuple by ':' inside.
    if (check(K::LParen)) {
        // Lookahead: if we see '(' identifier ':' ... ')' '->', this is a Pi type.
        // Discriminant: the ':' at depth 1 immediately after an identifier.
        bool is_pi = false;
        if (pos_ + 2 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Identifier
            && tokens_[pos_ + 2].kind == K::Colon)
        {
            // Scan forward to the matching ')' and check for '->' after it.
            int depth = 0;
            for (std::size_t i = pos_; i < tokens_.size(); ++i) {
                if (tokens_[i].kind == K::LParen) { ++depth; continue; }
                if (tokens_[i].kind == K::RParen) {
                    --depth;
                    if (depth == 0) {
                        // Check if the token after ')' is '->'
                        if (i + 1 < tokens_.size() && tokens_[i + 1].kind == K::Arrow)
                            is_pi = true;
                        break;
                    }
                }
            }
        }

        if (is_pi) {
            advance(); // consume '('
            std::string var_name;
            if (check(K::Identifier))
                var_name = advance().lexeme;
            else
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected variable name in Pi type binder"});
            expect(K::Colon, "expected ':' after variable name in Pi type binder");
            ast::TypeNode domain{ast::TypeUser{"?"}};
            if (check(K::Identifier) || check(K::LParen))
                domain = parseType();
            else
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected domain type in Pi type binder"});
            expect(K::RParen, "expected ')' to close Pi type binder");
            expect(K::Arrow, "expected '->' after Pi type binder");
            ast::TypeNode codomain{ast::TypeUser{"?"}};
            if (check(K::Identifier) || check(K::LParen))
                codomain = parseType();
            else
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected codomain type after '->' in Pi type"});
            return ast::type_pi(std::move(var_name), std::move(domain), std::move(codomain));
        }

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
    else if (name == "Universe") {
        base = ast::TypeNode{ast::TypeUniv{}};
    }
    else if (name == "Type") {
        // Numeric level: "Type 0", "Type 1", ...
        if (check(K::Number) && peek().lexeme.find('.') == std::string::npos) {
            std::size_t pos = 0;
            unsigned long lv = std::stoul(peek().lexeme, &pos);
            if (pos == peek().lexeme.size()) {
                advance();
                base = ast::TypeNode{ast::TypeType{static_cast<unsigned>(lv), ""}};
            } else {
                base = ast::TypeNode{ast::TypeType{std::nullopt, ""}};
            }
        }
        // Universe-variable level: "Type u", "Type u+1" where u is a single
        // lowercase letter (universe variable convention: u, v, w).
        // Restrict to single-character names to avoid consuming field names or
        // type names that appear after "Type" on the following line.
        else if (check(K::Identifier) && peek().lexeme.size() == 1
                 && peek().lexeme[0] >= 'a' && peek().lexeme[0] <= 'z') {
            std::string uvar = peek().lexeme;
            advance();
            // Check for successor: u+1
            if (check(K::Plus)) {
                advance();
                if (check(K::Number) && peek().lexeme == "1") {
                    advance();
                    base = ast::TypeNode{ast::TypeType{std::nullopt, uvar + "+1"}};
                } else {
                    base = ast::TypeNode{ast::TypeType{std::nullopt, uvar}};
                }
            } else {
                base = ast::TypeNode{ast::TypeType{std::nullopt, uvar}};
            }
        }
        // "Type (max u v)"
        else if (check(K::LParen)) {
            // Peek ahead: if next identifier after '(' is "max", parse max expr
            std::size_t saved = pos_;
            advance(); // consume '('
            if (check(K::Identifier) && peek().lexeme == "max") {
                advance(); // consume "max"
                std::string u = check(K::Identifier) ? (advance(), tokens_[pos_-1].lexeme) : "?";
                std::string v = check(K::Identifier) ? (advance(), tokens_[pos_-1].lexeme) : "?";
                if (check(K::RParen)) advance();
                base = ast::TypeNode{ast::TypeType{std::nullopt, "max " + u + " " + v}};
            } else {
                pos_ = saved; // restore: not a max expr, bare "Type"
                base = ast::TypeNode{ast::TypeType{std::nullopt, ""}};
            }
        }
        else {
            base = ast::TypeNode{ast::TypeType{std::nullopt, ""}};
        }
    }
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

    // let x be arbitrary [in T]  → TakeStep{x, T}
    // Detect: KwBe followed by Identifier "arbitrary"
    if (check(lexer::TokenKind::KwBe)
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == lexer::TokenKind::Identifier
            && tokens_[pos_ + 1].lexeme == "arbitrary") {
        advance(); // consume "be"
        advance(); // consume "arbitrary"
        std::optional<ast::TypeNode> type;
        // Optional "in <type>"
        if (check(lexer::TokenKind::KwIn)) {
            advance(); // consume "in"
            if (check(lexer::TokenKind::Identifier) || check(lexer::TokenKind::LParen))
                type = parseType();
            else
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected type name after 'in' in 'let ... be arbitrary in'"});
        }
        return {loc, ast::TakeStep{std::move(var), std::move(type)}};
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

    // Parse one or more hyp bindings: name : prop [, name : prop ...]
    // The list ends when we see '=>'.
    std::vector<ast::ObtainHypBinding> hyp_bindings;
    do {
        std::string hname;
        if (check(K::Identifier))
            hname = advance().lexeme;
        else
            diag_.emit({diag::Severity::Error, peek().loc, "expected hypothesis name"});
        expect(K::Colon, "expected ':' before hypothesis proposition");
        auto hprop = parseProp();
        hyp_bindings.push_back({std::move(hname), std::move(hprop)});
        // Consume comma only if the next token is NOT '=>' (i.e. more bindings follow).
        if (check(K::Comma)
                && pos_ + 1 < tokens_.size()
                && tokens_[pos_ + 1].kind != K::FatArrow)
            advance(); // consume ',' between bindings
        else if (check(K::Comma))
            advance(); // trailing comma before '=>' — also consume
    } while (!isAtEnd() && !check(K::FatArrow) && !check(K::KwEnd));

    expect(K::FatArrow, "expected '=>' after hypothesis bindings");

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
        std::move(hyp_bindings),
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

    // "suppose h1 : P and h2 : Q" → two SupposeSteps.
    // Problem: parseProp() is greedy — "P and hq" would be parsed as PropAnd{P, hq}.
    // Solution: scan ahead to detect "and <Identifier> :" pattern at paren-depth 0.
    // If found at position j, the "and" at j is the multi-suppose separator; parse
    // only up to j (stop at the first top-level "and" that is part of pattern).
    //
    // We implement this by parsing the prop normally, then checking if the result
    // is a conjunction whose RHS is an Atomic{name2} where the next token is ':'.
    // If so, undo: the conjunction was mis-parsed — the 'and' was separator.
    // We restore position to just before the 'and' by saving/restoring pos_.

    auto parse_possibly_limited_prop = [&]() -> ast::Prop {
        if (for_contradiction) return parseProp();
        // Scan for top-level "and Identifier :" at depth 0, which would signal a multi-suppose.
        // We only do this when the name is known (name.has_value()).
        if (!name.has_value()) return parseProp();
        // Look for the pattern: at depth 0, an And/KwAnd token followed by Identifier Colon.
        int depth = 0;
        bool has_nl19 = false;
        for (std::size_t i = pos_; i < tokens_.size(); ++i) {
            const auto k = tokens_[i].kind;
            if (k == lexer::TokenKind::LParen || k == lexer::TokenKind::LBracket
                    || k == lexer::TokenKind::LBrace) { ++depth; continue; }
            if (k == lexer::TokenKind::RParen || k == lexer::TokenKind::RBracket
                    || k == lexer::TokenKind::RBrace) { --depth; continue; }
            if (depth == 0 && k == lexer::TokenKind::And
                    && i + 2 < tokens_.size()
                    && tokens_[i + 1].kind == lexer::TokenKind::Identifier
                    && tokens_[i + 2].kind == lexer::TokenKind::Colon) {
                has_nl19 = true;
                break;
            }
            // Stop scanning at step-terminating tokens
            if (depth == 0 && (k == lexer::TokenKind::KwBy
                    || k == lexer::TokenKind::KwFrom
                    || k == lexer::TokenKind::KwEnd
                    || k == lexer::TokenKind::KwHave
                    || k == lexer::TokenKind::KwThen
                    || k == lexer::TokenKind::Eof))
                break;
        }
        if (!has_nl19) return parseProp();
        // Parse only up to the first top-level 'and' that precedes 'Identifier :'.
        // Use parseDisjunction() instead of parseProp() so we stop before PropImpl/
        // quantifiers and especially before the 'and' conjunction at the top level.
        // Actually parseDisjunction() stops at 'or', but parseProp() via parseBiconditional
        // → parseImplication → parseDisjunction → parseConjunction greedily eats 'and'.
        // The cleanest way: parse only parseNegation() to get a single atomic/negated prop.
        // For the common case, the prop between 'suppose h : ' and ' and h2 :' is atomic.
        // Parse an implication but stop at the top-level 'and':
        // We call parseBiconditional → parseImplication → parseDisjunction → parseConjunction.
        // parseConjunction eats all top-level 'and' tokens. To stop before the multi-suppose 'and', we
        // parse just one parseNegation() (no conjunction loop).
        return parseNegation();
    };

    auto prop = parse_possibly_limited_prop();

    // if we limited to parseNegation(), check if the next token is 'and <Identifier> :'
    if (!for_contradiction && name.has_value()
            && check(lexer::TokenKind::And)
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == lexer::TokenKind::Identifier
            && pos_ + 2 < tokens_.size()
            && tokens_[pos_ + 2].kind == lexer::TokenKind::Colon) {
        advance(); // consume "and"
        std::string name2{advance().lexeme};
        advance(); // consume ':'
        auto prop2 = parseProp(); // second prop can be a full prop
        // Push the second step into the deferred queue.
        deferred_steps_.emplace_back(
            loc, ast::SupposeStep{false, std::move(name2), std::move(prop2)});
    }

    return {loc, ast::SupposeStep{for_contradiction, std::move(name), std::move(prop)}};
}

// have <name> : <prop> by <justification> [at <expr>]
// have <name> : <prop> proof ... end        (inline sub-proof)
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

    // "have h : P proof ... end" — inline sub-proof block
    if (check(lexer::TokenKind::KwProof)) {
        auto block = parseProofBlock();
        auto sub = std::make_unique<ast::ProofBlock>(std::move(block));
        return {loc, ast::HaveStep{std::move(name), std::move(prop), {}, {},
                                   std::move(sub)}};
    }

    // "have h : P calc lhs rel rhs by refs ..." — embedded calc justification
    if (check(lexer::TokenKind::KwCalc)) {
        auto calc_step = parseCalcStep();
        auto sub = std::make_unique<ast::ProofBlock>();
        sub->steps.push_back(std::move(calc_step));
        return {loc, ast::HaveStep{std::move(name), std::move(prop), {}, {},
                                   std::move(sub)}};
    }

    // Accept "from" as a natural alias for "by": "have h : P from premise"
    if (check(lexer::TokenKind::KwFrom))
        advance();
    else
        expect(lexer::TokenKind::KwBy, "expected 'by', 'from', or 'proof' after proposition");
    auto refs = parseJustification();
    std::vector<ast::ExprPtr> witnesses;
    while (check(lexer::TokenKind::KwAt)) {
        advance();
        witnesses.push_back(ast::make_expr(parseExpr()));
    }
    // After the "at" witness chain, allow "and <ref>" clauses for ImplElim arguments:
    // "have h : C by f at a at b and h1 and h2" — f instantiated at a, b, then
    // applied to h1, h2 via ImplElim.
    if (!witnesses.empty()) {
        while (check(lexer::TokenKind::And) || check(lexer::TokenKind::KwWith)) {
            advance();
            if (check(lexer::TokenKind::Identifier))
                refs.push_back(std::string{advance().lexeme});
        }
    }
    return {loc, ast::HaveStep{std::move(name), std::move(prop), std::move(refs),
                               std::move(witnesses), nullptr}};
}

// then [<prop>] [(by | from) <justification> [at <expr>]]
// if no proposition follows "then", emits a "__qed__" sentinel;
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
            case K::KwCalc:
                return true;
            default:
                return false;
        }
    };

    std::vector<std::string> refs;
    std::vector<ast::ExprPtr> witnesses;

    if (is_bare_then()) {
        // Goal-close form: defer prop to checker via sentinel.
        ast::Prop dummy{loc, ast::PropFalse{}};
        refs.push_back("__qed__");
        if (check(K::KwBy) || check(K::KwFrom)) {
            advance();
            auto extra = parseJustification();
            refs.insert(refs.end(), extra.begin(), extra.end());
        }
        return {loc, ast::ThenStep{std::move(dummy), std::move(refs), {}}};
    }

    auto prop = parseProp();
    if (check(K::KwBy) || check(K::KwFrom)) {
        advance();
        refs = parseJustification();
        while (check(K::KwAt)) {
            advance();
            witnesses.push_back(ast::make_expr(parseExpr()));
        }
        // After the "at" witness chain, allow "and <ref>" clauses for ImplElim.
        if (!witnesses.empty()) {
            while (check(K::And) || check(K::KwWith)) {
                advance();
                if (check(K::Identifier))
                    refs.push_back(std::string{advance().lexeme});
            }
        }
    }
    return {loc, ast::ThenStep{std::move(prop), std::move(refs), std::move(witnesses)}};
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
// end cases
//
// Each arm's step list runs until the next 'case', 'end', or 'done'.
// The optional "end cases" terminator (KwEnd + KwCases) explicitly closes the
// cases block so that subsequent steps belong to the outer proof rather than
// the last arm.  Without it, cases must be the last step before end/qed.
ast::Step Parser::parseCasesStep() {
    const auto loc = peek().loc;
    advance(); // consume "cases"

    // Grammar: "cases [<name> :] <ref>"
    // If an identifier is followed by ':', it is the result label; otherwise
    // the identifier is the disjunct ref and the result is unnamed.
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

    // Optional "end cases" terminator: consume both tokens so the outer proof
    // loop can continue parsing steps after the cases block.
    if (check(lexer::TokenKind::KwEnd)
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == lexer::TokenKind::KwCases) {
        advance(); // consume "end"
        advance(); // consume "cases"
    }

    return {loc, ast::CasesStep{std::move(name), std::move(disjunct_ref), std::move(arms)}};
}

// split [<name> :]
//   case left  => <steps...>
//   case right => <steps...>
//
// Decomposes a conjunction goal P ∧ Q into two sub-proofs.
// Arm labels may also be written as parenthesised forms: (->) and (<-).
// The split keyword must be followed by case arms; it may appear anywhere in a proof.
ast::Step Parser::parseSplitStep() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "split"

    // Optional result label: if next is Identifier and after is Colon, consume both.
    std::string name;
    if (check(K::Identifier)) {
        if (pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Colon)
        {
            name = advance().lexeme; // consume label
            advance();               // consume ':'
        }
    }

    // Parse arms.
    // Each arm begins with 'case', then a label (identifier or parenthesised form),
    // then '=>', then step list until next 'case' / 'end' / 'qed' / EOF.
    std::vector<ast::SplitArm> arms;
    while (check(K::KwCase)) {
        advance(); // consume "case"

        // Parse the arm label.  Accept:
        //   - plain Identifier ("left", "right", "forward", "backward", etc.)
        //   - parenthesised form: "(" Arrow ")"  → "(->)"
        //                         "(" KwFrom ")" → "(<-)"  (or "(" "<-" ")")
        std::string label;
        if (check(K::LParen)) {
            advance(); // consume '('
            if (check(K::Arrow)) {
                advance();
                label = "(->) ";
            } else if (check(K::KwFrom)) {
                // "from" is the KwFrom token; use it for the backward direction
                advance();
                label = "(<-) ";
            } else if (check(K::Less)) {
                // raw '<' followed by '-' (lexed separately)
                advance();
                if (check(K::Minus)) { advance(); label = "(<-) "; }
                else                 { label = "(<) "; }
            } else if (check(K::Identifier)) {
                label = "(" + std::string{advance().lexeme} + ") ";
            } else {
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected arm label inside parentheses in 'split' step"});
            }
            // trim the trailing space we added above
            if (!label.empty() && label.back() == ' ')
                label.pop_back();
            expect(K::RParen, "expected ')' to close split arm label");
        } else if (check(K::Identifier)) {
            label = advance().lexeme;
        } else {
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected arm label after 'case' in 'split' step"});
        }

        expect(K::FatArrow, "expected '=>' after split arm label");

        std::vector<std::unique_ptr<ast::Step>> arm_steps;
        while (!isAtEnd()
               && !check(K::KwCase)
               && !check(K::KwEnd)
               && !check(K::KwDone))
            arm_steps.push_back(std::make_unique<ast::Step>(parseStep()));
        if (check(K::KwDone))
            advance(); // consume optional per-arm "done" terminator

        arms.push_back(ast::SplitArm{std::move(label), std::move(arm_steps)});
    }

    return {loc, ast::SplitStep{std::move(name), std::move(arms)}};
}

// induction <result_name> on <var> : <body>
//   base:       <steps...>            -- Nat induction: proves P(0)
//   inductive:  <steps...>            -- Nat induction: proves P(succ(n)), ih in scope
//
// OR for a user-defined inductive type T:
//   induction <result_name> on <var> : <body>
//     case nil:  <steps...>
//     case cons head tail ih:  <steps...>
//
// Dispatches on whether the first sub-block keyword is "base" (Nat) or "case" (structural).
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

    // type_name is set to "Nat" for the Nat path (base/inductive blocks) or left
    // empty for the structural path (case arms); checker fills it in from env.
    std::string type_name;

    expect(K::Colon, "expected ':' after induction variable to introduce predicate P(n)");
    auto body = parseProp();

    auto is_ident = [&](std::string_view s) {
        return check(K::Identifier) && peek().lexeme == s;
    };

    // ── Nat induction: "base:" / "inductive:" ────────────────────────────────
    if (is_ident("base")) {
        auto is_nat_block_end = [&]() {
            return isAtEnd()
                || is_ident("base") || is_ident("inductive")
                || check(K::KwEnd);
        };

        advance(); // consume "base"
        expect(K::Colon, "expected ':' after 'base'");
        std::vector<std::unique_ptr<ast::Step>> base_steps;
        while (!is_nat_block_end())
            base_steps.push_back(std::make_unique<ast::Step>(parseStep()));

        if (!is_ident("inductive")) {
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected 'inductive:' after base block"});
        } else {
            advance(); // consume "inductive"
        }
        expect(K::Colon, "expected ':' after 'inductive'");
        std::vector<std::unique_ptr<ast::Step>> ind_steps;
        while (!is_nat_block_end())
            ind_steps.push_back(std::make_unique<ast::Step>(parseStep()));

        ast::InductionStep s;
        s.name            = std::move(name);
        s.var             = std::move(var);
        s.type_name       = "Nat";
        s.body            = std::move(body);
        s.base_steps      = std::move(base_steps);
        s.inductive_steps = std::move(ind_steps);
        return {loc, std::move(s)};
    }

    // ── Structural induction: "case <ctor> [vars...] [ih_names...] :" ────────
    auto is_arm_end = [&]() {
        return isAtEnd() || check(K::KwCase) || check(K::KwEnd);
    };

    std::vector<ast::InductionArm> arms;
    while (check(K::KwCase)) {
        advance(); // consume "case"

        std::string ctor_name;
        if (check(K::Identifier))
            ctor_name = std::string{advance().lexeme};
        else
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected constructor name after 'case'"});

        // Consume optional variable/IH names until ":"
        // Convention: identifiers before ":" are: first the constructor arg vars,
        // then IH names (prefixed with "ih" by convention — we store all as vars
        // and let the checker separate them by matching against the ctor's is_recursive).
        std::vector<std::string> vars_list;
        std::vector<std::string> ih_names;
        // Collect all identifiers before the colon; checker will split them.
        while (check(K::Identifier)) {
            auto tok = std::string{advance().lexeme};
            // Treat identifiers starting with "ih" (case-insensitive prefix) as IH names;
            // all others as constructor arg vars.
            if (tok.size() >= 2
                    && (tok[0] == 'i' || tok[0] == 'I')
                    && (tok[1] == 'h' || tok[1] == 'H'))
                ih_names.push_back(std::move(tok));
            else
                vars_list.push_back(std::move(tok));
        }
        expect(K::Colon, "expected ':' after constructor name in 'case'");

        // Parse arm steps.  Each arm concludes with a ThenStep; once we see
        // one, stop so the outer "then ... by h" is not consumed into this arm.
        std::vector<std::unique_ptr<ast::Step>> arm_steps;
        bool saw_then = false;
        while (!is_arm_end() && !saw_then) {
            auto step = parseStep();
            if (std::get_if<ast::ThenStep>(&step.node))
                saw_then = true;
            arm_steps.push_back(std::make_unique<ast::Step>(std::move(step)));
        }

        ast::InductionArm arm;
        arm.ctor_name = std::move(ctor_name);
        arm.vars      = std::move(vars_list);
        arm.ih_names  = std::move(ih_names);
        arm.steps     = std::move(arm_steps);
        arms.push_back(std::move(arm));
    }

    if (arms.empty()) {
        diag_.emit({diag::Severity::Error, loc,
                    "induction step requires 'base:' (for Nat) or 'case' arms (for other types)"});
    }

    ast::InductionStep s;
    s.name      = std::move(name);
    s.var       = std::move(var);
    s.type_name = std::move(type_name);
    s.body      = std::move(body);
    s.arms      = std::move(arms);
    return {loc, std::move(s)};
}

// Helper: is the current token a relational operator that can start a calc link?
static bool is_rel_op_token(lexer::TokenKind k) {
    switch (k) {
        case lexer::TokenKind::Less:
        case lexer::TokenKind::Greater:
        case lexer::TokenKind::LessEq:
        case lexer::TokenKind::GreaterEq:
        case lexer::TokenKind::Equals:
        case lexer::TokenKind::NotEq:
            return true;
        default:
            return false;
    }
}

// calc [<name> :] <lhs> <rel> <rhs> by <refs>
//   { <rel> <rhs> by <refs> }
//
// The optional result label is detected by two-token lookahead:
// if the next two tokens are Identifier Colon (and the token after Colon is NOT
// a relational op, which would mean "name : rel" is unlikely), treat the
// identifier as the result label.  To distinguish "calc result : a = b by h"
// from "calc a = b by h", we look for the pattern:
//   KwCalc  Identifier  Colon  <not a rel-op>   → labelled form
//   KwCalc  Identifier  <rel-op>                → unlabelled form (lhs is identifier)
ast::Step Parser::parseCalcStep() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "calc"

    // Optional result label: "calc name :" if the token after "calc" is an
    // Identifier, the token after that is Colon, and the token after Colon is
    // NOT itself a relational operator (which would mean the identifier is the lhs).
    std::string name;
    if (check(K::Identifier)
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Colon
            && pos_ + 2 < tokens_.size()
            && !is_rel_op_token(tokens_[pos_ + 2].kind)) {
        name = std::string{advance().lexeme}; // consume label name
        advance();                            // consume ':'
    }

    // Parse the LHS of the first link.
    auto lhs = parseExpr();

    // Parse the first link: rel rhs by refs
    if (!is_rel_op_token(peek().kind)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected relational operator after calc LHS"});
        return {loc, ast::CalcStep{std::move(name),
                                   ast::make_expr(std::move(lhs)), {}}};
    }

    std::vector<ast::CalcLink> links;

    // Helper: is the current position the start of a continuation link?
    // Accepts either:  rel-op ...      (compact single-line form)
    //              or  _ rel-op ...    (_ = "previous RHS" placeholder)
    auto is_continuation = [&]() {
        if (is_rel_op_token(peek().kind)) return true;
        if (check(K::Identifier) && peek().lexeme == "_"
                && pos_ + 1 < tokens_.size()
                && is_rel_op_token(tokens_[pos_ + 1].kind))
            return true;
        return false;
    };

    // Parse links in a loop
    while (is_continuation()) {
        if (check(K::Identifier) && peek().lexeme == "_")
            advance(); // consume placeholder _ (refers to previous RHS)
        auto rel_opt = as_rel_op(peek().kind);
        advance(); // consume the rel-op token
        auto rhs = parseExpr();
        std::vector<std::string> refs;
        if (check(K::KwBy)) {
            advance();
            refs = parseJustification();
        } else {
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected 'by' after calc link rhs"});
        }
        links.push_back(ast::CalcLink{*rel_opt, ast::make_expr(std::move(rhs)),
                                      std::move(refs)});
    }

    if (links.empty()) {
        diag_.emit({diag::Severity::Error, loc,
                    "'calc' block requires at least one relational link"});
    }

    return {loc, ast::CalcStep{std::move(name),
                               ast::make_expr(std::move(lhs)), std::move(links)}};
}

ast::Step Parser::parseStep() {
    using K = lexer::TokenKind;

    // Drain deferred steps (e.g. from multi-suppose) before parsing new ones.
    if (!deferred_steps_.empty()) {
        auto s = std::move(deferred_steps_.front());
        deferred_steps_.erase(deferred_steps_.begin());
        return s;
    }

    if (check(K::KwLet))          return parseLetStep();
    if (check(K::KwTake))         return parseTakeStep();
    if (check(K::KwObtain))       return parseObtainStep();
    if (check(K::KwSuppose))      return parseSupposeStep();

    // "we have" — two-token phrase aliasing "have"
    // Also handle "we need to show P", "we know X", "we prove that P"
    if (check(K::Identifier) && peek().lexeme == "we") {
        if (pos_ + 1 < tokens_.size() && tokens_[pos_ + 1].kind == K::KwHave) {
            advance(); return parseHaveStep();
        }
        // "we need to show P"
        if (pos_ + 1 < tokens_.size()
                && tokens_[pos_ + 1].kind == K::Identifier
                && tokens_[pos_ + 1].lexeme == "need"
                && pos_ + 2 < tokens_.size()
                && tokens_[pos_ + 2].kind == K::Identifier
                && tokens_[pos_ + 2].lexeme == "to"
                && pos_ + 3 < tokens_.size()
                && (tokens_[pos_ + 3].kind == K::KwShow
                    || (tokens_[pos_ + 3].kind == K::Identifier
                        && tokens_[pos_ + 3].lexeme == "show"))) {
            const auto loc = peek().loc;
            advance(); advance(); advance(); advance(); // consume "we need to show"
            auto prop = parseProp();
            return {loc, ast::ShowStep{std::move(prop)}};
        }
        // "we know X"
        if (pos_ + 1 < tokens_.size()
                && tokens_[pos_ + 1].kind == K::Identifier
                && tokens_[pos_ + 1].lexeme == "know"
                && pos_ + 2 < tokens_.size()
                && tokens_[pos_ + 2].kind == K::Identifier) {
            const auto loc = peek().loc;
            advance(); advance(); // consume "we know"
            std::string ref{advance().lexeme}; // consume the ref name
            // Produce: have _ : ref by ref
            ast::Prop ref_prop{loc, ast::Atomic{ref}};
            return {loc, ast::HaveStep{"_", std::move(ref_prop), {ref}, {}}};
        }
        // "we prove that P"
        if (pos_ + 1 < tokens_.size()
                && tokens_[pos_ + 1].kind == K::Identifier
                && tokens_[pos_ + 1].lexeme == "prove"
                && pos_ + 2 < tokens_.size()
                && tokens_[pos_ + 2].kind == K::Identifier
                && tokens_[pos_ + 2].lexeme == "that") {
            const auto loc = peek().loc;
            advance(); advance(); advance(); // consume "we prove that"
            auto prop = parseProp();
            return {loc, ast::ShowStep{std::move(prop)}};
        }
    }

    if (check(K::KwHave))         return parseHaveStep();
    if (check(K::KwThen))         return parseThenStep();
    // "so P [by refs]" — maps KwSo to a ThenStep
    if (check(K::KwSo)) {
        const auto loc = peek().loc;
        advance(); // consume "so"
        auto prop = parseProp();
        std::vector<std::string> refs;
        if (check(K::KwBy) || check(K::KwFrom)) {
            advance();
            refs = parseJustification();
        }
        return {loc, ast::ThenStep{std::move(prop), std::move(refs), {}}};
    }
    if (check(K::KwContradiction)) return parseContradictionStep();
    if (check(K::KwCases))        return parseCasesStep();
    if (check(K::KwSplit))        return parseSplitStep();
    if (check(K::KwCalc))         return parseCalcStep();
    if (check(K::KwInduction))    return parseInductionStep();
    if (check(K::KwWlog))         return parseWlogStep();

    // rewrite [↔] [←/<-] h — equality or biconditional rewriting step
    if (check(K::KwRewrite)) {
        const auto loc = peek().loc;
        advance(); // consume "rewrite"
        // Parse a comma-separated list of [↔] [←] ref items.
        std::vector<ast::RewriteItem> rewrites;
        do {
            bool iff = false;
            bool rev = false;
            // ↔ / iff prefix: rewrite using a biconditional (propositional rewrite)
            if (check(K::Iff)) {
                iff = true; advance();
            } else if (check(K::Identifier) && peek().lexeme == "iff") {
                iff = true; advance();
            }
            if (check(K::LeftArrow)) {
                rev = true; advance(); // ← U+2190
            } else if (check(K::Less) && pos_ + 1 < tokens_.size()
                       && tokens_[pos_ + 1].kind == K::Minus) {
                rev = true; advance(); advance(); // <- ASCII alternative
            }
            std::string ref;
            if (check(K::Identifier))
                ref = advance().lexeme;
            else
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected hypothesis name after 'rewrite'"});
            rewrites.push_back({std::move(ref), rev, iff});
        } while (check(K::Comma) && (advance(), true));
        return {loc, ast::RewriteStep{std::move(rewrites)}};
    }

    // apply h — backward implication application step
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

    // push neg [at h] — push negations inward
    // "push" is context-sensitive; the two-word sequence "push neg" is the step.
    // Syntax:  push neg           → apply to the current goal
    //          push neg at h      → apply to hypothesis h in scope
    if (check(K::Identifier) && peek().lexeme == "push"
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Identifier
            && tokens_[pos_ + 1].lexeme == "neg") {
        const auto loc = peek().loc;
        advance(); // consume "push"
        advance(); // consume "neg"
        std::optional<std::string> hyp;
        if (check(K::KwAt)) {
            advance(); // consume "at"
            if (check(K::Identifier))
                hyp = advance().lexeme;
            else
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected hypothesis name after 'push neg at'"});
        }
        return {loc, ast::PushNegStep{std::move(hyp)}};
    }

    // suffices to show P [by refs] — goal reduction step (NL22).
    // "suffices to" where next token is "to" (identifier) dispatches to SufficesStep.
    if (check(K::KwSuffices)
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Identifier
            && tokens_[pos_ + 1].lexeme == "to") {
        return parseSufficesStep();
    }

    // suffices h : P — reduce goal to proving P, auto-searching for P → goal.
    // Syntax: suffices <name> : <prop>  (name is an identifier, not "to")
    // Desugars to ApplyStep: the checker verifies h : P → current_goal.
    if ((check(K::Identifier) && peek().lexeme == "suffices"
             || check(K::KwSuffices))
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Identifier
            && tokens_[pos_ + 1].lexeme != "to") {
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

    // show P — goal annotation step
    if (check(K::KwShow)) {
        const auto loc = peek().loc;
        advance(); // consume "show"
        auto prop = parseProp();
        return {loc, ast::ShowStep{std::move(prop)}};
    }

    // exact h — close goal directly via a named hypothesis
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

    // "note that P by refs" / "observe that P by refs" → have _ : P by refs
    if (check(K::Identifier)
            && (peek().lexeme == "note" || peek().lexeme == "observe")
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Identifier
            && tokens_[pos_ + 1].lexeme == "that") {
        const auto loc = peek().loc;
        advance(); advance(); // consume "note"/"observe" and "that"
        auto prop = parseProp();
        std::vector<std::string> refs;
        if (check(K::KwBy) || check(K::KwFrom)) {
            advance();
            refs = parseJustification();
        }
        return {loc, ast::HaveStep{"_", std::move(prop), std::move(refs), {}}};
    }

    // "since h1 and h2, have name : P"
    if (check(K::Identifier) && peek().lexeme == "since") {
        const auto loc = peek().loc;
        advance(); // consume "since"
        // Parse refs until ','
        std::vector<std::string> refs;
        if (check(K::Identifier)) {
            refs.push_back(std::string{advance().lexeme});
            while ((check(K::And) || check(K::KwWith))
                   && pos_ + 1 < tokens_.size()
                   && tokens_[pos_ + 1].kind == K::Identifier) {
                advance();
                refs.push_back(std::string{advance().lexeme});
            }
        }
        expect(K::Comma, "expected ',' after refs in 'since ... , have ...'");
        expect(K::KwHave, "expected 'have' after 'since ... ,'");
        std::string name;
        if (check(K::Identifier))
            name = advance().lexeme;
        else
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected hypothesis name after 'have'"});
        expect(K::Colon, "expected ':' after hypothesis name");
        auto prop = parseProp();
        return {loc, ast::HaveStep{std::move(name), std::move(prop), std::move(refs), {}}};
    }

    // "it suffices to show P"
    if (check(K::Identifier) && peek().lexeme == "it"
            && pos_ + 1 < tokens_.size()
            && (tokens_[pos_ + 1].kind == K::KwSuffices
                || (tokens_[pos_ + 1].kind == K::Identifier
                    && tokens_[pos_ + 1].lexeme == "suffices"))
            && pos_ + 2 < tokens_.size()
            && tokens_[pos_ + 2].kind == K::Identifier
            && tokens_[pos_ + 2].lexeme == "to"
            && pos_ + 3 < tokens_.size()
            && (tokens_[pos_ + 3].kind == K::KwShow
                || (tokens_[pos_ + 3].kind == K::Identifier
                    && tokens_[pos_ + 3].lexeme == "show"))) {
        const auto loc = peek().loc;
        advance(); advance(); advance(); advance(); // consume "it suffices to show"
        auto prop = parseProp();
        return {loc, ast::ShowStep{std::move(prop)}};
    }

    // "it follows that P [by refs]"
    if (check(K::Identifier) && peek().lexeme == "it"
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Identifier
            && tokens_[pos_ + 1].lexeme == "follows"
            && pos_ + 2 < tokens_.size()
            && tokens_[pos_ + 2].kind == K::Identifier
            && tokens_[pos_ + 2].lexeme == "that") {
        const auto loc = peek().loc;
        advance(); advance(); advance(); // consume "it follows that"
        auto prop = parseProp();
        std::vector<std::string> refs;
        if (check(K::KwBy) || check(K::KwFrom)) {
            advance();
            refs = parseJustification();
        }
        return {loc, ast::ThenStep{std::move(prop), std::move(refs), {}}};
    }

    // "which gives P" / "which shows P" → ThenStep{P, []}
    if (check(K::Identifier) && peek().lexeme == "which"
            && pos_ + 1 < tokens_.size()
            && tokens_[pos_ + 1].kind == K::Identifier
            && (tokens_[pos_ + 1].lexeme == "gives"
                || tokens_[pos_ + 1].lexeme == "shows")) {
        const auto loc = peek().loc;
        advance(); advance(); // consume "which" and "gives"/"shows"
        auto prop = parseProp();
        std::vector<std::string> refs;
        if (check(K::KwBy) || check(K::KwFrom)) {
            advance();
            refs = parseJustification();
        }
        return {loc, ast::ThenStep{std::move(prop), std::move(refs), {}}};
    }

    const auto loc = peek().loc;
    diag_.emit({diag::Severity::Error, loc,
                "expected proof step; got '" + peek().lexeme + "'"});
    advance();
    return {loc, ast::LetStep{}}; // silently skipped by the checker
}

// wlog <name> : <prop>
// introduces prop as an assumption with a side-obligation warning.
ast::Step Parser::parseWlogStep() {
    const auto loc = peek().loc;
    advance(); // consume "wlog"
    std::string name;
    if (check(lexer::TokenKind::Identifier)) {
        name = advance().lexeme;
    } else {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected hypothesis name after 'wlog'"});
        name = "_";
    }
    expect(lexer::TokenKind::Colon, "expected ':' after 'wlog' name");
    auto prop = parseProp();
    return {loc, ast::WlogStep{std::move(name), std::move(prop)}};
}

// suffices to show <prop> [by refs]
// Optionally also accepts "suffices <prop> by refs" (dropping "to show").
ast::Step Parser::parseSufficesStep() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "suffices"
    // Consume optional "to show" or "to prove"
    if (peek().lexeme == "to") {
        advance(); // consume "to"
        // consume "show" or "prove" (either identifier or KwShow keyword)
        if (peek().lexeme == "show" || peek().lexeme == "prove" || check(K::KwShow))
            advance();
    }
    auto prop = parseProp();
    std::vector<std::string> justification;
    if (check(K::KwBy) || check(K::KwFrom)) {
        advance(); // consume "by"/"from"
        justification = parseJustification();
    }
    return {loc, ast::SufficesStep{std::move(prop), std::move(justification)}};
}

// Helper: returns true if the current position starts a direction marker "(→)" or "(<-)".
// The forward marker is  LParen Arrow RParen.
// The backward marker is LParen (KwFrom | (Less Minus)) RParen.
bool Parser::isDirectionMarker() const noexcept {
    using K = lexer::TokenKind;
    if (!check(K::LParen)) return false;
    if (pos_ + 1 >= tokens_.size()) return false;
    const auto k1 = tokens_[pos_ + 1].kind;
    if (k1 == K::Arrow) {
        // (→) : LParen Arrow RParen
        return pos_ + 2 < tokens_.size() && tokens_[pos_ + 2].kind == K::RParen;
    }
    if (k1 == K::KwFrom) {
        // (<-) via "from": LParen KwFrom RParen
        return pos_ + 2 < tokens_.size() && tokens_[pos_ + 2].kind == K::RParen;
    }
    if (k1 == K::Less) {
        // (<-) via "<-": LParen Less Minus RParen
        return pos_ + 3 < tokens_.size()
            && tokens_[pos_ + 2].kind == K::Minus
            && tokens_[pos_ + 3].kind == K::RParen;
    }
    return false;
}

// Consume a direction-marker token sequence and return the label string.
// Assumes isDirectionMarker() is true.
std::string Parser::consumeDirectionMarker() {
    using K = lexer::TokenKind;
    advance(); // consume '('
    std::string label;
    if (check(K::Arrow)) {
        advance(); label = "(->";
    } else if (check(K::KwFrom)) {
        advance(); label = "(<-";
    } else { // Less Minus
        advance(); // '<'
        advance(); // '-'
        label = "(<-";
    }
    advance(); // consume ')'
    label += ")";
    return label;
}

ast::ProofBlock Parser::parseProofBlock() {
    using K = lexer::TokenKind;
    ast::ProofBlock block;
    const auto proof_loc = peek().loc;
    advance(); // consume "proof"

    // detect direction-marker biconditional proof.
    // If the block opens with "(→)" or "(<-)", wrap the entire block as a SplitStep.
    if (isDirectionMarker()) {
        std::vector<ast::SplitArm> arms;

        // Parse first arm: from current direction marker until the next marker or end.
        std::string first_label = consumeDirectionMarker();
        std::vector<std::unique_ptr<ast::Step>> first_steps;
        while (!isAtEnd() && !check(K::KwEnd) && !isDirectionMarker())
            first_steps.push_back(std::make_unique<ast::Step>(parseStep()));
        arms.push_back(ast::SplitArm{std::move(first_label), std::move(first_steps)});

        // Parse second arm (if present).
        if (isDirectionMarker()) {
            std::string second_label = consumeDirectionMarker();
            std::vector<std::unique_ptr<ast::Step>> second_steps;
            while (!isAtEnd() && !check(K::KwEnd) && !isDirectionMarker())
                second_steps.push_back(std::make_unique<ast::Step>(parseStep()));
            arms.push_back(ast::SplitArm{std::move(second_label), std::move(second_steps)});
        }

        expect(K::KwEnd, "expected 'end' to close direction-marker proof block");
        block.steps.push_back(ast::Step{proof_loc, ast::SplitStep{"", std::move(arms)}});
        return block;
    }

    while (!isAtEnd() && !check(K::KwEnd))
        block.steps.push_back(parseStep());
    expect(K::KwEnd, "expected 'end' to close proof block");
    return block;
}

// ── Declaration parsing ────────────────────────────────────────────────────────

// definition <name> { "(" <var> ":" <type> ")" } ":" <prop>
// OR (structure instantiation form):
// definition <name> ":" <StructType> ":="
//   <field_name> ":=" <expr>
//   ...
std::optional<ast::DeclPtr> Parser::parseDefinition() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "definition"

    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected definition name"});
        return std::nullopt;
    }
    std::string name{advance().lexeme};

    // Detect structure instantiation: "definition name : TypeName :="
    // Lookahead: current=Colon, next=Identifier, next+1=ColonEquals
    if (check(K::Colon)
        && pos_ + 1 < tokens_.size()
        && tokens_[pos_ + 1].kind == K::Identifier
        && pos_ + 2 < tokens_.size()
        && tokens_[pos_ + 2].kind == K::ColonEquals)
    {
        advance(); // consume ':'
        std::string struct_type{advance().lexeme}; // consume TypeName
        advance(); // consume ':='

        // Helper: is the current token a valid field binding name followed by ':='?
        auto is_binding_start = [&]() -> bool {
            if (pos_ + 1 >= tokens_.size()) return false;
            if (tokens_[pos_ + 1].kind != K::ColonEquals) return false;
            const auto k = peek().kind;
            if (k == K::Identifier) return true;
            // Accept keyword tokens that are plain word identifiers
            const auto& lex = peek().lexeme;
            if (lex.empty()) return false;
            for (char c : lex)
                if (!std::isalnum(static_cast<unsigned char>(c)) && c != '_')
                    return false;
            return true;
        };

        // Helper: is the current token a top-level declaration keyword?
        auto is_toplevel_kw = [&]() {
            switch (peek().kind) {
                case K::KwAxiom: case K::KwDefinition:
                case K::KwTheorem: case K::KwLemma:
                case K::KwImport: case K::KwInstance:
                case K::KwStructure: case K::Eof:
                    return true;
                default:
                    return false;
            }
        };

        std::map<std::string, ast::ExprPtr> bindings;
        while (!isAtEnd() && !is_toplevel_kw() && is_binding_start()) {
            std::string fname{advance().lexeme}; // consume field name
            advance(); // consume ':='
            auto fexpr = parseExpr();
            bindings.emplace(std::move(fname), ast::make_expr(std::move(fexpr)));
        }

        auto decl = std::make_unique<ast::Decl>(
            ast::DeclKind::Definition, std::move(name), loc,
            ast::Prop{loc, ast::PropFalse{}}, std::nullopt);
        decl->struct_type     = std::move(struct_type);
        decl->struct_bindings = std::move(bindings);
        return decl;
    }

    // Parse optional parameter list: { "(" id ":" type ")" }
    std::vector<ast::Param> params;
    while (check(K::LParen)) {
        advance(); // (
        std::string pname;
        if (check(K::Identifier))
            pname = advance().lexeme;
        else
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected parameter name"});
        expect(K::Colon, "expected ':' in definition parameter");
        ast::TypeNode ptype{ast::TypeUser{"?"}};
        if (check(K::Identifier) || check(K::LParen))
            ptype = parseType();
        expect(K::RParen, "expected ')' to close parameter");
        params.push_back({std::move(pname), std::move(ptype)});
    }

    expect(K::Colon, "expected ':' after definition name");
    auto prop = parseProp();

    // optional predicate body  ":= prop_body"
    std::optional<ast::PropPtr> def_body;
    if (check(K::ColonEquals)) {
        advance(); // consume ':='
        def_body = ast::make_prop(parseProp());
    }

    auto decl = std::make_unique<ast::Decl>(ast::DeclKind::Definition, std::move(name), loc,
                                            std::move(prop), std::nullopt);
    decl->params  = std::move(params);
    decl->def_body = std::move(def_body);
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
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "theorem" or "lemma"

    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected theorem name"});
        return std::nullopt;
    }
    std::string name{advance().lexeme};

    // parse optional parameter list: { "(" id ":" type ")" }
    // Same syntax as definition params; the ':' separator between param and type is
    // the discriminant.  This is a standard `(name : type)` binder list, NOT a Pi
    // type — the Pi type only arises when `(x : A)` is followed by `->`.
    std::vector<ast::Param> params;
    while (check(K::LParen)
           && pos_ + 1 < tokens_.size()
           && tokens_[pos_ + 1].kind == K::Identifier
           && pos_ + 2 < tokens_.size()
           && tokens_[pos_ + 2].kind == K::Colon)
    {
        advance(); // consume '('
        std::string pname;
        if (check(K::Identifier))
            pname = advance().lexeme;
        else
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected parameter name in theorem parameter"});
        expect(K::Colon, "expected ':' in theorem parameter");
        ast::TypeNode ptype{ast::TypeUser{"?"}};
        if (check(K::Identifier) || check(K::LParen))
            ptype = parseType();
        else
            diag_.emit({diag::Severity::Error, peek().loc,
                        "expected type in theorem parameter"});
        expect(K::RParen, "expected ')' to close theorem parameter");
        params.push_back({std::move(pname), std::move(ptype)});
    }

    expect(K::Colon, "expected ':' after theorem name");
    auto prop = parseProp();

    std::optional<ast::ProofBlock> proof;
    if (check(K::KwProof))
        proof = parseProofBlock();

    auto decl = std::make_unique<ast::Decl>(kind, std::move(name), loc,
                                            std::move(prop), std::move(proof));
    decl->params = std::move(params);
    return decl;
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

// structure <Name> ":="
//   { <name> ":" <type>           -- term field
//   | "axiom" <name> ":" <prop>   -- axiom field
//   }
// Parsing stops when the next token is not an identifier (i.e. not the start of
// another field declaration) or is a top-level declaration keyword.
//
// Field names may be any single-token word, including keywords that can serve as
// identifiers in a field context (e.g. "inv", "mul", "one").  A token is a valid
// field name start when it is an Identifier OR a keyword whose lexeme is a plain
// word AND the token AFTER it is a Colon (two-token lookahead).
std::optional<ast::DeclPtr> Parser::parseStructure() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "structure"

    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected structure name after 'structure'"});
        return std::nullopt;
    }
    std::string name{advance().lexeme};

    if (!expect(K::ColonEquals, "expected ':=' after structure name"))
        return std::nullopt;

    // Helper: is the current token the start of a top-level declaration (signals end of fields)?
    // Note: KwAxiom is NOT listed here because "axiom <name> : <prop>" is valid inside a
    // structure body as an axiom field.  The "axiom" branch in the loop below handles it.
    auto is_toplevel_kw = [&]() {
        switch (peek().kind) {
            case K::KwDefinition:
            case K::KwTheorem: case K::KwLemma:
            case K::KwImport: case K::KwInstance:
            case K::KwStructure: case K::KwQuotient: case K::Eof:
                return true;
            default:
                return false;
        }
    };

    // Helper: is the current token a valid term-field name token?
    // Any word token (Identifier or keyword) followed by ':' is accepted.
    // This allows field names like "inv", "mul", "one" even though they are
    // lexed as keyword tokens.
    auto is_field_name_token = [&]() -> bool {
        // Must be followed by ':'
        if (pos_ + 1 >= tokens_.size()) return false;
        if (tokens_[pos_ + 1].kind != K::Colon) return false;
        // Current token must be word-like (Identifier or any keyword)
        const auto k = peek().kind;
        if (k == K::Identifier) return true;
        // Accept keyword tokens that are plain words (not symbols/punctuation)
        switch (k) {
            // Exclude top-level declaration keywords (handled by is_toplevel_kw above)
            case K::KwAxiom: return false; // handled separately as axiom field
            // All other keyword tokens can be field names when followed by ':'
            default: {
                // Only accept if the lexeme is an alphanumeric/underscore word
                const auto& lex = peek().lexeme;
                for (char c : lex)
                    if (!std::isalnum(static_cast<unsigned char>(c)) && c != '_')
                        return false;
                return !lex.empty();
            }
        }
    };

    std::vector<ast::StructField> fields;

    while (!isAtEnd() && !is_toplevel_kw()) {
        // "axiom" <name> ":" <prop>  — axiom field
        if (check(K::KwAxiom)) {
            advance(); // consume "axiom"
            std::string fname;
            if (check(K::Identifier))
                fname = advance().lexeme;
            else
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected axiom field name after 'axiom'"});
            expect(K::Colon, "expected ':' after axiom field name");
            auto prop = parseProp();
            fields.push_back(ast::FieldAxiom{std::move(fname), std::move(prop)});
        }
        // <name> ":" <type>  — term field (identifier or keyword followed by ':')
        else if (is_field_name_token()) {
            std::string fname{advance().lexeme};
            advance(); // consume ':'
            ast::TypeNode ftype{ast::TypeUser{"?"}};
            if (check(K::Identifier) || check(K::LParen))
                ftype = parseType();
            else
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected type after ':' in structure field"});
            fields.push_back(ast::FieldTerm{std::move(fname), std::move(ftype)});
        }
        else {
            // Unknown token — not the start of a field; stop parsing fields.
            break;
        }
    }

    auto decl = std::make_unique<ast::Decl>(
        ast::DeclKind::Structure, std::move(name), loc,
        ast::Prop{loc, ast::PropFalse{}}, std::nullopt);
    decl->fields = std::move(fields);
    return decl;
}

// quotient <Name> := <CarrierType> over <RelName>
//   [ axiom <name> : <prop> ]
//   ...
//
// Introduces a quotient type Name = CarrierType / RelName.  The optional
// axiom fields declare properties of the equivalence relation (typically
// reflexivity, symmetry, transitivity).  The '/' quotient slash is written
// as the context-sensitive word "over" to avoid ambiguity with division.
std::optional<ast::DeclPtr> Parser::parseQuotient() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "quotient"

    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected quotient type name after 'quotient'"});
        return std::nullopt;
    }
    std::string name{advance().lexeme};

    if (!expect(K::ColonEquals, "expected ':=' after quotient name"))
        return std::nullopt;

    // Carrier type name
    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected carrier type name after ':=' in quotient declaration"});
        return std::nullopt;
    }
    std::string carrier{advance().lexeme};

    // Context-sensitive "over" keyword (lexed as Identifier)
    if (!check(K::Identifier) || peek().lexeme != "over") {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected 'over' after carrier type name in quotient declaration"});
        return std::nullopt;
    }
    advance(); // consume "over"

    // Equivalence relation name
    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected relation name after 'over' in quotient declaration"});
        return std::nullopt;
    }
    std::string rel{advance().lexeme};

    // Helper: signals end of the quotient body (top-level declaration start or EOF)
    auto is_toplevel_kw = [&]() {
        switch (peek().kind) {
            case K::KwDefinition:
            case K::KwTheorem: case K::KwLemma:
            case K::KwImport: case K::KwInstance:
            case K::KwStructure: case K::KwQuotient: case K::Eof:
                return true;
            default:
                return false;
        }
    };

    // Parse optional axiom fields
    std::vector<ast::StructField> fields;
    while (!isAtEnd() && !is_toplevel_kw()) {
        if (check(K::KwAxiom)) {
            advance(); // consume "axiom"
            std::string fname;
            if (check(K::Identifier))
                fname = advance().lexeme;
            else
                diag_.emit({diag::Severity::Error, peek().loc,
                            "expected axiom field name after 'axiom'"});
            expect(K::Colon, "expected ':' after axiom field name");
            auto prop = parseProp();
            fields.push_back(ast::FieldAxiom{std::move(fname), std::move(prop)});
        } else {
            // Unknown token in quotient body — stop
            break;
        }
    }

    auto decl = std::make_unique<ast::Decl>(
        ast::DeclKind::Quotient, std::move(name), loc,
        ast::Prop{loc, ast::PropFalse{}}, std::nullopt);
    decl->quot_carrier = std::move(carrier);
    decl->quot_rel     = std::move(rel);
    decl->fields       = std::move(fields);
    return decl;
}

// ── parseNamespace ─────────────────────────────────────────────────────────────
// namespace <Name>
//   <declarations...>
// end <Name>  (or just "end")
std::optional<ast::DeclPtr> Parser::parseNamespace() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "namespace"

    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected namespace name after 'namespace'"});
        return std::nullopt;
    }
    std::string ns_name = std::string{advance().lexeme};

    // Parse inner declarations until "end <Name>" or "end" or EOF.
    std::vector<ast::DeclPtr> inner_decls;
    while (!isAtEnd()) {
        // Stop on "end" (with optional matching name).
        if (check(K::KwEnd)) {
            advance(); // consume "end"
            // Optionally consume the matching name.
            if (check(K::Identifier) && peek().lexeme == ns_name)
                advance();
            break;
        }
        if (auto d = parseDeclaration())
            inner_decls.push_back(std::move(*d));
        else
            syncToDeclaration();
    }

    auto decl = std::make_unique<ast::Decl>(
        ast::DeclKind::Namespace, ns_name, loc,
        ast::Prop{loc, ast::PropFalse{}}, std::nullopt);
    decl->ns_decls = std::move(inner_decls);
    return decl;
}

// ── parseOpen ──────────────────────────────────────────────────────────────────
// open <Name>           — module-level open; brings all Ns.x into scope
// open <Name> in <decl> — scoped open; Ns visible only within that declaration
std::optional<ast::DeclPtr> Parser::parseOpen() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "open"

    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected namespace name after 'open'"});
        return std::nullopt;
    }
    std::string ns_name = std::string{advance().lexeme};

    auto decl = std::make_unique<ast::Decl>(
        ast::DeclKind::Open, ns_name, loc,
        ast::Prop{loc, ast::PropFalse{}}, std::nullopt);

    // "open X in <decl>" — scoped form; "in" is lexed as KwIn
    if (check(K::KwIn)) {
        advance(); // consume "in"
        auto inner = parseDeclaration();
        if (inner)
            decl->open_scope_decl = std::move(*inner);
    }

    return decl;
}

// ── parseNamespaceAlias ────────────────────────────────────────────────────────
// alias <Alias> = <DottedName>
// Creates a namespace alias: all "DottedName.x" entries become accessible as "Alias.x".
std::optional<ast::DeclPtr> Parser::parseNamespaceAlias() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "alias"

    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected alias name after 'alias'"});
        return std::nullopt;
    }
    std::string alias_name = std::string{advance().lexeme};

    if (!check(K::Equals)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected '=' after alias name in 'alias'"});
        return std::nullopt;
    }
    advance(); // consume "="

    // Parse a dotted name: Foo or Foo.Bar or Foo.Bar.Baz
    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected target name after '=' in 'alias'"});
        return std::nullopt;
    }
    std::string target = std::string{advance().lexeme};
    // consume dotted continuation
    while (check(K::Dot) && pos_ + 1 < tokens_.size()
           && tokens_[pos_ + 1].kind == K::Identifier) {
        advance(); // consume "."
        target += "." + std::string{advance().lexeme};
    }

    auto decl = std::make_unique<ast::Decl>(
        ast::DeclKind::NamespaceAlias, alias_name, loc,
        ast::Prop{loc, ast::PropFalse{}}, std::nullopt);
    decl->alias_target = std::move(target);
    return decl;
}

// ── parseTypeAlias ─────────────────────────────────────────────────────────────
// type <Alias> = <type>
std::optional<ast::DeclPtr> Parser::parseTypeAlias() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "type"

    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected alias name after 'type'"});
        return std::nullopt;
    }
    std::string alias_name = std::string{advance().lexeme};

    if (!expect(K::Equals, "expected '=' after type alias name")) return std::nullopt;

    ast::TypeNode body = parseType();

    auto decl = std::make_unique<ast::Decl>(
        ast::DeclKind::TypeAlias, alias_name, loc,
        ast::Prop{loc, ast::PropFalse{}}, std::nullopt);
    decl->type_alias_body = std::move(body);
    return decl;
}

// ── parseInductive ─────────────────────────────────────────────────────────────
// inductive <Name> :=
//   <ctor_name> : [ <arg_type> -> ... -> ] <Name>
//   ...
//
// "inductive" is a context-sensitive identifier.  Constructors are one per line;
// the section ends at a new top-level keyword or EOF.
std::optional<ast::DeclPtr> Parser::parseInductive() {
    using K = lexer::TokenKind;
    const auto loc = peek().loc;
    advance(); // consume "inductive" identifier token

    if (!check(K::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected type name after 'inductive'"});
        return std::nullopt;
    }
    std::string type_name = std::string{advance().lexeme};

    if (!expect(K::ColonEquals, "expected ':=' after inductive type name")) return std::nullopt;

    // Helper: is the current token the start of a new top-level declaration?
    auto is_toplevel_kw = [&]() {
        switch (peek().kind) {
            case K::KwAxiom: case K::KwDefinition:
            case K::KwTheorem: case K::KwLemma:
            case K::KwImport: case K::KwInstance:
            case K::KwStructure: case K::KwType:
            case K::Eof: return true;
            default: break;
        }
        if (check(K::Identifier)) {
            auto lx = peek().lexeme;
            if (lx == "inductive" || lx == "namespace" || lx == "open"
                    || lx == "private" || lx == "protected" || lx == "abstract")
                return true;
        }
        return false;
    };

    std::vector<ast::InductiveConstructor> ctors;
    while (!isAtEnd() && !is_toplevel_kw()) {
        if (!check(K::Identifier)) { advance(); continue; } // skip unexpected tokens
        std::string ctor_name = std::string{advance().lexeme};
        if (!expect(K::Colon, "expected ':' after constructor name '" + ctor_name + "'"))
            break;

        // Parse argument types: zero or more TypeName separated by "->"
        // The final identifier in the chain is the inductive type itself (return type).
        std::vector<std::string> arg_types;
        while (check(K::Identifier)) {
            std::string t = std::string{advance().lexeme};
            // peek: if followed by "->" this is an arg type; otherwise it's the return type
            if (check(K::Arrow) || (check(K::Identifier) && peek().lexeme == "->")) {
                arg_types.push_back(std::move(t));
                advance(); // consume "->"
            } else {
                // This is the return type (should be type_name); don't store as arg
                break;
            }
        }

        ast::InductiveConstructor ctor;
        ctor.name = std::move(ctor_name);
        ctor.arg_types = std::move(arg_types);
        // Mark which args are recursive (type == type_name)
        for (const auto& at : ctor.arg_types)
            ctor.is_recursive.push_back(at == type_name);
        ctors.push_back(std::move(ctor));
    }

    auto decl = std::make_unique<ast::Decl>(
        ast::DeclKind::Inductive, type_name, loc,
        ast::Prop{loc, ast::PropFalse{}}, std::nullopt);
    decl->inductive_ctors = std::move(ctors);
    return decl;
}

std::optional<ast::DeclPtr> Parser::parseDeclaration() {
    using K = lexer::TokenKind;

    // detect optional "private" / "protected" context-sensitive prefix.
    ast::Visibility vis = ast::Visibility::Public;
    if (check(K::Identifier) && peek().lexeme == "private") {
        vis = ast::Visibility::Private;
        advance();
    } else if (check(K::Identifier) && peek().lexeme == "protected") {
        vis = ast::Visibility::Protected;
        advance();
    }

    // detect optional "abstract" context-sensitive prefix before "definition".
    bool is_abstract = false;
    if (check(K::Identifier) && peek().lexeme == "abstract") {
        is_abstract = true;
        advance();
    }

    std::optional<ast::DeclPtr> result;
    if (check(K::KwAxiom))         result = parseAxiom();
    else if (check(K::KwDefinition)) result = parseDefinition();
    else if (check(K::KwTheorem))  result = parseTheorem(ast::DeclKind::Theorem);
    else if (check(K::KwLemma))    result = parseTheorem(ast::DeclKind::Lemma);
    else if (check(K::KwImport))   result = parseImport();
    else if (check(K::KwInstance)) result = parseInstance();
    else if (check(K::KwStructure)) result = parseStructure();
    else if (check(K::KwQuotient)) result = parseQuotient();
    else if (check(K::KwNamespace)) result = parseNamespace();
    else if (check(K::KwOpen))     result = parseOpen();
    else if (check(K::KwType))     result = parseTypeAlias();
    else if (check(K::Identifier) && peek().lexeme == "inductive") result = parseInductive();
    else if (check(K::Identifier) && peek().lexeme == "alias") result = parseNamespaceAlias();
    else {
        diag_.emit({diag::Severity::Error, peek().loc,
                    "expected 'axiom', 'definition', 'theorem', 'lemma', 'instance', "
                    "'structure', 'quotient', 'namespace', 'open', 'type', 'inductive', or 'alias'; got '"
                    + peek().lexeme + "'"});
        advance();
        return std::nullopt;
    }

    // Apply visibility and abstract flags to the parsed declaration.
    if (result) {
        (*result)->visibility = vis;
        (*result)->is_abstract = is_abstract;
    }
    return result;
}

void Parser::syncToDeclaration() {
    using K = lexer::TokenKind;
    while (!isAtEnd()
           && !check(K::KwAxiom) && !check(K::KwDefinition)
           && !check(K::KwTheorem) && !check(K::KwLemma)
           && !check(K::KwImport) && !check(K::KwInstance)
           && !check(K::KwStructure) && !check(K::KwQuotient)
           && !check(K::KwNamespace) && !check(K::KwOpen) && !check(K::KwType)
           && !(check(K::Identifier) && (peek().lexeme == "private"
                                         || peek().lexeme == "protected"
                                         || peek().lexeme == "abstract"
                                         || peek().lexeme == "inductive"))) {
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
