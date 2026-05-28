#include <gtest/gtest.h>
#include <forall/checker/checker.hpp>
#include <forall/diagnostics/diagnostic.hpp>

#include <filesystem>
#include <fstream>
#include <string>

using namespace forall;

// ── Test helpers ───────────────────────────────────────────────────────────────

// Write source to a uniquely named temp file and run the checker on it.
static diag::DiagnosticEngine run_checker(const std::string& test_name,
                                          const std::string& src) {
    auto path = std::filesystem::temp_directory_path()
                / ("forall_test_" + test_name + ".forall");
    std::ofstream{path} << src;
    diag::DiagnosticEngine diag;
    checker::Checker c{diag};
    c.check(path);
    return diag;
}

static bool has_error(const diag::DiagnosticEngine& diag, const std::string& fragment) {
    for (const auto& d : diag.diagnostics())
        if (d.severity == diag::Severity::Error
                && d.message.find(fragment) != std::string::npos)
            return true;
    return false;
}

// ── Valid proofs ───────────────────────────────────────────────────────────────

TEST(CheckerTest, ValidAxiom) {
    auto diag = run_checker("valid_axiom", "axiom a : P");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidAxiomReferencedInProof) {
    auto diag = run_checker("valid_axiom_ref", R"(
axiom ax : P -> Q
lemma use_ax : Q
proof
  suppose hp : P
  then Q by ax and hp
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidAndElim) {
    auto diag = run_checker("valid_and_elim", R"(
theorem and_elim : Q
proof
  suppose h : P and Q
  then Q by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidAndIntro) {
    auto diag = run_checker("valid_and_intro", R"(
theorem and_intro : P and Q
proof
  suppose hp : P
  suppose hq : Q
  then P and Q by hp and hq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidImplElim) {
    auto diag = run_checker("valid_impl_elim", R"(
theorem mp : Q
proof
  suppose hpq : P -> Q
  suppose hp  : P
  then Q by hpq and hp
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidImplIntro) {
    auto diag = run_checker("valid_impl_intro", R"(
theorem identity : P -> P
proof
  suppose h : P
  then P -> P by h and h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidNotElimAndFalseElim) {
    auto diag = run_checker("valid_not_elim_false_elim", R"(
theorem ex_falso : Q
proof
  suppose hn : not P
  suppose hp : P
  have bot : false by hn and hp
  then Q by bot
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidNotIntro) {
    auto diag = run_checker("valid_not_intro", R"(
theorem contra : not P -> not P
proof
  suppose hn : not P
  then not P -> not P by hn and hn
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidOrIntroL) {
    auto diag = run_checker("valid_or_intro_l", R"(
theorem weaken_l : P -> P or Q
proof
  suppose hp : P
  have h_or : P or Q by hp
  then P -> P or Q by hp and h_or
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidOrIntroR) {
    auto diag = run_checker("valid_or_intro_r", R"(
theorem weaken_r : Q -> P or Q
proof
  suppose hq : Q
  have h_or : P or Q by hq
  then Q -> P or Q by hq and h_or
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidOrElim) {
    auto diag = run_checker("valid_or_elim", R"(
theorem or_comm : (P or Q) -> (Q or P)
proof
  suppose h    : P or Q
  suppose hp   : P
  have qp_l   : Q or P        by hp
  have p_qp   : P -> Q or P   by hp and qp_l
  suppose hq   : Q
  have qp_r   : Q or P        by hq
  have q_qp   : Q -> Q or P   by hq and qp_r
  have qp     : Q or P        by h and p_qp and q_qp
  then (P or Q) -> (Q or P)   by h and qp
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidHaveChain) {
    // Chains: h → h2 → h3, each derived from the previous
    auto diag = run_checker("valid_have_chain", R"(
theorem chain : R
proof
  suppose h1 : P and Q and R
  have h2 : P and Q by h1
  have h3 : P by h2
  then R by h1
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidLetStepIsIgnored) {
    auto diag = run_checker("valid_let_ignored", R"(
theorem trivial : P -> P
proof
  let x be a Nat
  suppose h : P
  then P -> P by h and h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidLemmaUsedInSubsequentProof) {
    // A proved lemma is accumulated into module_env and can be used as a ref
    // in any declaration that follows it in the same file.
    auto diag = run_checker("valid_lemma_reuse", R"(
axiom ab : A -> B
axiom bc : B -> C

lemma a_to_b : A -> B
proof
  suppose h : A
  have hb : B by ab and h
  then A -> B by h and hb
end

theorem a_to_c : A -> C
proof
  suppose h : A
  have hb : B by a_to_b and h
  have hc : C by bc and hb
  then A -> C by h and hc
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Invalid proofs ─────────────────────────────────────────────────────────────

TEST(CheckerTest, InvalidUnknownRef) {
    auto diag = run_checker("invalid_unknown_ref", R"(
theorem bad : P
proof
  then P by ghost
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "unknown hypothesis 'ghost'"));
}

TEST(CheckerTest, InvalidNoProofBlock) {
    auto diag = run_checker("invalid_no_proof", "theorem noproof : P");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "no proof block"));
}

TEST(CheckerTest, InvalidCannotInferRule) {
    // Refs are in the wrong order for AndIntro (rhs then lhs instead of lhs then rhs)
    auto diag = run_checker("invalid_no_rule", R"(
theorem bad : P and Q
proof
  suppose ha : P
  suppose hb : Q
  then P and Q by hb and ha
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "cannot infer inference rule"));
}

TEST(CheckerTest, InvalidThenWithNoJustification) {
    auto diag = run_checker("invalid_then_no_by", R"(
theorem bad : P
proof
  suppose h : P
  then P
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "'then' step requires a 'by' justification"));
}

TEST(CheckerTest, InvalidWrongConclusion) {
    // Proof establishes P but the theorem declares P and Q.
    auto diag = run_checker("invalid_wrong_conclusion", R"(
theorem bad : P and Q
proof
  suppose h : P
  then P by h
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "wrong proposition"));
}

TEST(CheckerTest, InvalidNoThenStep) {
    // A proof with no 'then' step produces no conclusion.
    auto diag = run_checker("invalid_no_then", R"(
theorem bad : P
proof
  suppose h : P
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "no concluding"));
}

TEST(CheckerTest, InvalidContradictionWithNoJustification) {
    auto diag = run_checker("invalid_contradiction_no_by", R"(
theorem bad : P
proof
  contradiction :
end
)");
    EXPECT_TRUE(diag.hasErrors());
}
