#include <gtest/gtest.h>
#include <forall/ast/node.hpp>
#include <forall/diagnostics/diagnostic.hpp>
#include <forall/formatter/formatter.hpp>
#include <forall/lexer/lexer.hpp>
#include <forall/parser/parser.hpp>

using namespace forall;

// ── Test helpers ───────────────────────────────────────────────────────────────

static ast::Module parse_str(const std::string& src) {
    diag::DiagnosticEngine diag;
    lexer::Lexer lex{src, "<test>", diag};
    auto toks = lex.tokenize();
    parser::Parser p{toks, diag};
    auto mod = p.parse();
    if (diag.hasErrors()) ADD_FAILURE() << "parse error in test input";
    return mod;
}

static std::string fmt(const std::string& src) {
    return formatter::format_module(parse_str(src));
}

static std::string fmt_decl(const std::string& src) {
    auto mod = parse_str(src);
    if (mod.decls.empty()) return "";
    return formatter::format_decl(*mod.decls[0]);
}

// ── Declarations ───────────────────────────────────────────────────────────────

TEST(FormatterTest, Axiom) {
    EXPECT_EQ(fmt_decl("axiom p : P"), "axiom p : P");
}

TEST(FormatterTest, AxiomWithImplication) {
    EXPECT_EQ(fmt_decl("axiom mp : P -> Q"), "axiom mp : P → Q");
}

TEST(FormatterTest, Definition_NoParams) {
    EXPECT_EQ(fmt_decl("definition refl : x = x"), "definition refl : x = x");
}

TEST(FormatterTest, Definition_WithParams) {
    EXPECT_EQ(fmt_decl("definition f (n : Nat) : f(n)"),
              "definition f (n : Nat) : f(n)");
}

TEST(FormatterTest, Import) {
    EXPECT_EQ(fmt_decl("import \"stdlib/nat.forall\""),
              "import \"stdlib/nat.forall\"");
}

TEST(FormatterTest, Instance) {
    // instance declaration formats as "instance T : ClassName"
    // Needs the required axioms to be present to validate, but format_decl
    // works purely on the AST — the checker isn't involved here.
    auto mod = parse_str("instance Real : Field");
    ASSERT_EQ(mod.decls.size(), 1u);
    EXPECT_EQ(formatter::format_decl(*mod.decls[0]), "instance Real : Field");
}

TEST(FormatterTest, TheoremSimple) {
    const std::string src = R"(theorem t : P
proof
  suppose h : P
  then P by h
end)";
    const std::string expected =
        "theorem t : P\n"
        "proof\n"
        "  suppose h : P\n"
        "  then P by h\n"
        "end";
    EXPECT_EQ(fmt_decl(src), expected);
}

TEST(FormatterTest, LemmaKeyword) {
    const std::string src = R"(lemma l : P
proof
  then P by ax
end)";
    EXPECT_EQ(fmt_decl(src).substr(0, 5), "lemma");
}

// ── Proof steps ────────────────────────────────────────────────────────────────

TEST(FormatterTest, Step_Suppose) {
    auto src = "theorem t : Q\nproof\n  suppose h : P\n  then Q by ax\nend";
    auto out = fmt_decl(src);
    EXPECT_NE(out.find("suppose h : P"), std::string::npos);
}

TEST(FormatterTest, Step_Have) {
    auto src = "theorem t : Q\nproof\n  have h : P by ax\n  then Q by ax\nend";
    auto out = fmt_decl(src);
    EXPECT_NE(out.find("have h : P by ax"), std::string::npos);
}

TEST(FormatterTest, Step_HaveMultiRef) {
    auto src = "theorem t : Q\nproof\n  have h : Q by a and b\n  then Q by h\nend";
    auto out = fmt_decl(src);
    EXPECT_NE(out.find("have h : Q by a and b"), std::string::npos);
}

TEST(FormatterTest, Step_ThenByDecide) {
    auto src = "theorem t : 2 + 3 = 5\nproof\n  then 2 + 3 = 5 by decide\nend";
    auto out = fmt_decl(src);
    EXPECT_NE(out.find("then 2 + 3 = 5 by decide"), std::string::npos);
}

TEST(FormatterTest, Step_ThenByNormNum) {
    auto src = "theorem t : x + y = y + x\nproof\n  then x + y = y + x by norm_num\nend";
    auto out = fmt_decl(src);
    EXPECT_NE(out.find("by norm_num"), std::string::npos);
}

TEST(FormatterTest, Step_ThenByRing) {
    auto src = "theorem t : x * y = y * x\nproof\n  then x * y = y * x by ring\nend";
    auto out = fmt_decl(src);
    EXPECT_NE(out.find("by ring"), std::string::npos);
}

TEST(FormatterTest, Step_Take) {
    auto src = "theorem t : P\nproof\n  take n : Nat\n  then P by ax\nend";
    auto out = fmt_decl(src);
    EXPECT_NE(out.find("take n : Nat"), std::string::npos);
}

TEST(FormatterTest, Step_Let) {
    auto src = "theorem t : P\nproof\n  let x be a Nat\n  then P by ax\nend";
    auto out = fmt_decl(src);
    EXPECT_NE(out.find("let x be a Nat"), std::string::npos);
}

TEST(FormatterTest, Step_Contradiction) {
    auto src = "theorem t : false\nproof\n  suppose h : P\n  suppose nh : not P\n  contradiction : nh and h\nend";
    auto out = fmt_decl(src);
    EXPECT_NE(out.find("contradiction"), std::string::npos);
}

TEST(FormatterTest, Step_WitnessAt) {
    auto src = R"(theorem t : P(n)
proof
  have h : P(n) by univ at n
  then P(n) by h
end)";
    auto out = fmt_decl(src);
    EXPECT_NE(out.find("at n"), std::string::npos);
}

// ── Module-level formatting ────────────────────────────────────────────────────

TEST(FormatterTest, Module_BlankLineBetweenDecls) {
    const std::string src = "axiom a : P\naxiom b : Q";
    const std::string out = fmt(src);
    // The two declarations should be separated by a blank line.
    EXPECT_NE(out.find("axiom a : P\n\naxiom b : Q"), std::string::npos);
}

TEST(FormatterTest, Module_SingleDecl) {
    EXPECT_EQ(fmt("axiom a : P"), "axiom a : P\n");
}

TEST(FormatterTest, Module_TheoremEndsWithNewline) {
    auto out = fmt("theorem t : P\nproof\n  then P by ax\nend");
    EXPECT_EQ(out.back(), '\n');
}

// ── Idempotency: fmt(fmt(x)) == fmt(x) ─────────────────────────────────────────

TEST(FormatterTest, Idempotent_Axiom) {
    std::string src = "axiom mp : P -> Q";
    std::string once = fmt(src);
    std::string twice = fmt(once);
    EXPECT_EQ(once, twice);
}

TEST(FormatterTest, Idempotent_Theorem) {
    std::string src = R"(theorem and_comm : P and Q -> Q and P
proof
  suppose h : P and Q
  have hp : P by h
  have hq : Q by h
  have hqp : Q and P by hq and hp
  then P and Q -> Q and P by h and hqp
end)";
    std::string once = fmt(src);
    std::string twice = fmt(once);
    EXPECT_EQ(once, twice);
}
