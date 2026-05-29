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
    return lhs;
}

ast::Expr Parser::parseExprUnary() {
    if (check(lexer::TokenKind::Minus)) {
        const auto loc = peek().loc;
        advance();
        auto operand = parseExprPow();
        return {loc, ast::ExprUnary{ast::UnaryOp::Neg, ast::make_expr(std::move(operand))}};
    }
    if (check(lexer::TokenKind::KwInv)) {
        const auto loc = peek().loc;
        advance();
        auto operand = parseExprPow(); // inv applies to the immediately following atom/pow
        std::vector<ast::ExprPtr> args{ast::make_expr(std::move(operand))};
        return {loc, ast::ExprCall{"inv", std::move(args)}};
    }
    if (check(lexer::TokenKind::KwCompl)) {
        const auto loc = peek().loc;
        advance();
        auto operand = parseExprPow(); // compl applies to the immediately following atom/pow
        std::vector<ast::ExprPtr> args{ast::make_expr(std::move(operand))};
        return {loc, ast::ExprCall{"compl", std::move(args)}};
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
        return {loc, ast::ExprBinary{ast::BinOp::Pow, ast::make_expr(std::move(base)),
                                                       ast::make_expr(std::move(exp))}};
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
        return {loc, ast::ExprLit{"0"}}; // error sentinel — skip indexing
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
        return {loc, ast::ExprSetLit{}};
    }

    // Two-token lookahead: {id : type | P} or {id | P}
    if (check(lexer::TokenKind::Identifier) && pos_ + 1 < tokens_.size()) {
        const auto next_kind = tokens_[pos_ + 1].kind;
        if (next_kind == lexer::TokenKind::Colon || next_kind == lexer::TokenKind::Pipe) {
            std::string var = std::string{advance().lexeme};
            std::optional<std::string> type;
            if (check(lexer::TokenKind::Colon)) {
                advance();
                if (check(lexer::TokenKind::Identifier))
                    type = std::string{advance().lexeme};
                else
                    diag_.emit({diag::Severity::Error, peek().loc,
                                "expected type name after ':' in set comprehension"});
            }
            expect(lexer::TokenKind::Pipe, "expected '|' in set comprehension");
            auto pred = parseProp();
            expect(lexer::TokenKind::RBrace, "expected '}' to close set comprehension");
            return {loc, ast::ExprSetCompr{std::move(var), std::move(type),
                                           ast::make_prop(std::move(pred))}};
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
    return {loc, ast::ExprSetLit{std::move(elements)}};
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

    std::optional<std::string> type;
    if (check(lexer::TokenKind::Colon)) {
        advance();
        if (check(lexer::TokenKind::Identifier))
            type = std::string{advance().lexeme};
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
    return {loc, ast::ExprLambda{std::move(var), std::move(type),
                                  ast::make_expr(std::move(body))}};
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

    return {loc, ast::ExprIf{ast::make_prop(std::move(cond)),
                              ast::make_expr(std::move(then_)),
                              ast::make_expr(std::move(else_))}};
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

    std::optional<std::string>  type;
    std::optional<ast::RelOp>   rel;
    std::optional<ast::ExprPtr> bound;

    if (check(lexer::TokenKind::Colon)) {
        advance(); // typed binder: sum i : T
        if (check(lexer::TokenKind::Identifier))
            type = std::string{advance().lexeme};
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
    return {loc, ast::ExprAgg{op, std::move(var), std::move(type), rel, std::move(bound),
                               ast::make_expr(std::move(body))}};
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

    std::string var;
    if (check(lexer::TokenKind::Identifier))
        var = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected variable name after quantifier"});

    std::optional<std::string> type;
    if (check(lexer::TokenKind::Colon)) {
        advance();
        if (check(lexer::TokenKind::Identifier))
            type = std::string{advance().lexeme};
        else
            diag_.emit({diag::Severity::Error, peek().loc, "expected type name after ':'"});
    }

    expect(lexer::TokenKind::Comma, "expected ',' after quantifier binder");
    auto body = parseProp();

    if (is_forall)
        return {loc, ast::PropForall{std::move(var), std::move(type), ast::make_prop(std::move(body))}};
    return {loc, ast::PropExists{std::move(var), std::move(type), ast::make_prop(std::move(body))}};
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
        return {loc, ast::PropAnd{std::move(ab), std::move(ba)}};
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
        return {loc, ast::PropImpl{ast::make_prop(std::move(lhs)),
                                   ast::make_prop(std::move(rhs))}};
    }

    // disjunction [ "implies" / → disjunction ]
    const auto loc = peek().loc;
    auto lhs = parseDisjunction();
    if (check(lexer::TokenKind::Arrow) || check(lexer::TokenKind::KwImplies)) {
        advance();
        auto rhs = parseImplication(); // right-associative
        return {loc, ast::PropImpl{ast::make_prop(std::move(lhs)),
                                   ast::make_prop(std::move(rhs))}};
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
    return lhs;
}

ast::Prop Parser::parseNegation() {
    if (check(lexer::TokenKind::Not)) {
        const auto loc = peek().loc;
        advance();
        auto inner = parseAtomicProp();
        return {loc, ast::PropNot{ast::make_prop(std::move(inner))}};
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
        return {loc, ast::PropFalse{}};
    }

    // "(" ... ")"
    // Parses the inner content as a full proposition, which already handles
    // relational atoms like (x + 1 < n) via the recursive descent below.
    if (check(lexer::TokenKind::LParen)) {
        advance();
        auto inner = parseProp();
        expect(lexer::TokenKind::RParen, "expected ')'");
        return inner;
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
        return {loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                   ast::make_expr(std::move(rhs)), *rel}};
    }

    // Set membership: x in S / x ∈ S
    if (check(K::KwIn) || check(K::MemberOf)) {
        advance();
        auto rhs = parseExpr();
        return {loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                   ast::make_expr(std::move(rhs)), ast::RelOp::In}};
    }
    // x not in S / x ∉ S
    if (check(K::NotMemberOf)) {
        advance();
        auto rhs = parseExpr();
        return {loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                   ast::make_expr(std::move(rhs)), ast::RelOp::NotIn}};
    }
    if (check(K::Not) && pos_ + 1 < tokens_.size()
        && tokens_[pos_ + 1].kind == K::KwIn) {
        advance(); advance(); // consume "not" then "in"
        auto rhs = parseExpr();
        return {loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                   ast::make_expr(std::move(rhs)), ast::RelOp::NotIn}};
    }
    // Subset relations
    if (check(K::KwSubseteq) || check(K::SubseteqSym)) {
        advance();
        auto rhs = parseExpr();
        return {loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                   ast::make_expr(std::move(rhs)), ast::RelOp::SubsetEq}};
    }
    if (check(K::KwSubset) || check(K::SubsetSym)) {
        advance();
        auto rhs = parseExpr();
        return {loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                   ast::make_expr(std::move(rhs)), ast::RelOp::Subset}};
    }
    if (check(K::KwSupseteq) || check(K::SuperseteqSym)) {
        advance();
        auto rhs = parseExpr();
        return {loc, ast::PropRel{ast::make_expr(std::move(lhs)),
                                   ast::make_expr(std::move(rhs)), ast::RelOp::SupersetEq}};
    }

    // Convert a no-rel expression to a propositional atom.
    if (const auto* v = std::get_if<ast::ExprVar>(&lhs.node))
        return {loc, ast::Atomic{v->name}};

    if (const auto* c = std::get_if<ast::ExprCall>(&lhs.node))
        return {loc, ast::PropPred{c->name, c->args}};

    diag_.emit({diag::Severity::Error, loc,
                "arithmetic expression `" + forall::pretty::to_string(lhs)
                + "` in proposition context requires a relational operator"});
    return {loc, ast::PropFalse{}};
}

// ── Proof step parsing ─────────────────────────────────────────────────────────

// justification = ref { ("and" | "with") ref }
std::vector<std::string> Parser::parseJustification() {
    std::vector<std::string> refs;
    if (!check(lexer::TokenKind::Identifier)) return refs;
    refs.push_back(std::string{advance().lexeme});
    while (check(lexer::TokenKind::And) || check(lexer::TokenKind::KwWith)) {
        advance();
        if (check(lexer::TokenKind::Identifier))
            refs.push_back(std::string{advance().lexeme});
    }
    return refs;
}

// let <name> be [a] <type>
ast::Step Parser::parseLetStep() {
    const auto loc = peek().loc;
    advance(); // consume "let"
    std::string var;
    if (check(lexer::TokenKind::Identifier))
        var = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected variable name after 'let'"});

    std::optional<std::string> type;
    if (check(lexer::TokenKind::KwBe)) {
        advance();
        consumeArticle();
        if (check(lexer::TokenKind::Identifier))
            type = std::string{advance().lexeme};
    }
    return {loc, ast::LetStep{std::move(var), std::move(type)}};
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
        expect(lexer::TokenKind::Colon, "expected ':' after 'contradiction'");
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

// have <name> : <prop> by <justification>
ast::Step Parser::parseHaveStep() {
    const auto loc = peek().loc;
    advance(); // consume "have"

    std::string name;
    if (check(lexer::TokenKind::Identifier))
        name = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected hypothesis name after 'have'"});

    expect(lexer::TokenKind::Colon, "expected ':' after hypothesis name");
    auto prop = parseProp();
    expect(lexer::TokenKind::KwBy, "expected 'by' after proposition");
    auto refs = parseJustification();
    return {loc, ast::HaveStep{std::move(name), std::move(prop), std::move(refs)}};
}

// then <prop> [by <justification>]
ast::Step Parser::parseThenStep() {
    const auto loc = peek().loc;
    advance(); // consume "then"
    auto prop = parseProp();
    std::vector<std::string> refs;
    if (check(lexer::TokenKind::KwBy)) {
        advance();
        refs = parseJustification();
    }
    return {loc, ast::ThenStep{std::move(prop), std::move(refs)}};
}

// contradiction : <justification>
ast::Step Parser::parseContradictionStep() {
    const auto loc = peek().loc;
    advance(); // consume "contradiction"
    expect(lexer::TokenKind::Colon, "expected ':' after 'contradiction'");
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

    std::string name;
    if (check(lexer::TokenKind::Identifier))
        name = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected result name after 'cases'"});

    expect(lexer::TokenKind::Colon, "expected ':' after cases result name");

    std::string disjunct_ref;
    if (check(lexer::TokenKind::Identifier))
        disjunct_ref = advance().lexeme;
    else
        diag_.emit({diag::Severity::Error, peek().loc, "expected hypothesis ref after 'cases <name>:'"});

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
        while (!isAtEnd() && !check(lexer::TokenKind::KwCase) && !check(lexer::TokenKind::KwEnd))
            arm_steps.push_back(std::make_unique<ast::Step>(parseStep()));

        arms.push_back(ast::CaseArm{std::move(arm_name), std::move(arm_prop), std::move(arm_steps)});
    }

    return {loc, ast::CasesStep{std::move(name), std::move(disjunct_ref), std::move(arms)}};
}

ast::Step Parser::parseStep() {
    using K = lexer::TokenKind;
    if (check(K::KwLet))          return parseLetStep();
    if (check(K::KwSuppose))      return parseSupposeStep();
    // "we have" — two-token phrase aliasing "have"
    if (check(K::Identifier) && peek().lexeme == "we"
            && pos_ + 1 < tokens_.size() && tokens_[pos_ + 1].kind == K::KwHave)
        { advance(); return parseHaveStep(); }
    if (check(K::KwHave))         return parseHaveStep();
    if (check(K::KwThen))         return parseThenStep();
    if (check(K::KwContradiction)) return parseContradictionStep();
    if (check(K::KwCases))        return parseCasesStep();

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
// Parameter list is parsed and discarded until the type system is in place.
std::optional<ast::DeclPtr> Parser::parseDefinition() {
    const auto loc = peek().loc;
    advance(); // consume "definition"

    if (!check(lexer::TokenKind::Identifier)) {
        diag_.emit({diag::Severity::Error, peek().loc, "expected definition name"});
        return std::nullopt;
    }
    std::string name{advance().lexeme};

    // Parse and discard optional parameter list: { "(" id ":" type ")" }
    while (check(lexer::TokenKind::LParen)) {
        advance(); // (
        if (check(lexer::TokenKind::Identifier)) advance(); // var name
        expect(lexer::TokenKind::Colon, "expected ':' in definition parameter");
        if (check(lexer::TokenKind::Identifier)) advance(); // type name
        expect(lexer::TokenKind::RParen, "expected ')' to close parameter");
    }

    expect(lexer::TokenKind::Colon, "expected ':' after definition name");
    auto prop = parseProp();
    return std::make_unique<ast::Decl>(ast::DeclKind::Definition, std::move(name), loc,
                                       std::move(prop), std::nullopt);
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

std::optional<ast::DeclPtr> Parser::parseDeclaration() {
    using K = lexer::TokenKind;
    if (check(K::KwAxiom))      return parseAxiom();
    if (check(K::KwDefinition)) return parseDefinition();
    if (check(K::KwTheorem))    return parseTheorem(ast::DeclKind::Theorem);
    if (check(K::KwLemma))      return parseTheorem(ast::DeclKind::Lemma);
    if (check(K::KwImport))     return parseImport();

    diag_.emit({diag::Severity::Error, peek().loc,
                "expected 'axiom', 'definition', 'theorem', or 'lemma'; got '"
                + peek().lexeme + "'"});
    advance();
    return std::nullopt;
}

void Parser::syncToDeclaration() {
    using K = lexer::TokenKind;
    while (!isAtEnd()
           && !check(K::KwAxiom) && !check(K::KwDefinition)
           && !check(K::KwTheorem) && !check(K::KwLemma) && !check(K::KwImport)) {
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
