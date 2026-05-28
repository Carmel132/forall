#include <forall/parser/parser.hpp>

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

// ── Proposition parsing ────────────────────────────────────────────────────────
//
// Grammar (from docs/grammar.ebnf):
//   prop        = quantifier | implication
//   implication = "if" prop "then" prop | disjunction [ "implies" disjunction ]
//   disjunction = conjunction { "or"  conjunction }
//   conjunction = negation    { "and" negation    }
//   negation    = "not" atomic_prop | atomic_prop
//   atomic_prop = identifier | "false" | "(" prop ")"

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

ast::Prop Parser::parseAtomicProp() {
    const auto loc = peek().loc;

    if (check(lexer::TokenKind::LParen)) {
        advance();
        auto inner = parseProp();
        expect(lexer::TokenKind::RParen, "expected ')'");
        return inner;
    }

    if (check(lexer::TokenKind::KwFalse)) {
        advance();
        return {loc, ast::PropFalse{}};
    }

    if (check(lexer::TokenKind::Identifier)) {
        std::string name{advance().lexeme};
        return {loc, ast::Atomic{std::move(name)}};
    }

    diag_.emit({diag::Severity::Error, loc,
                "expected proposition; got '" + peek().lexeme + "'"});
    advance();
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
    if (check(K::KwAxiom))   return parseAxiom();
    if (check(K::KwTheorem)) return parseTheorem(ast::DeclKind::Theorem);
    if (check(K::KwLemma))   return parseTheorem(ast::DeclKind::Lemma);
    if (check(K::KwImport))  return parseImport();

    diag_.emit({diag::Severity::Error, peek().loc,
                "expected 'axiom', 'theorem', or 'lemma'; got '" + peek().lexeme + "'"});
    advance();
    return std::nullopt;
}

ast::Module Parser::parse() {
    ast::Module mod;
    while (!isAtEnd()) {
        if (auto decl = parseDeclaration())
            mod.decls.push_back(std::move(*decl));
    }
    return mod;
}

} // namespace forall::parser
