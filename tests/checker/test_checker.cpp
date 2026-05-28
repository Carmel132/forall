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

// ── Accessibility: keyword aliases ─────────────────────────────────────────────

TEST(CheckerTest, AliasAssume) {
    // "assume" is interchangeable with "suppose"
    auto diag = run_checker("alias_assume", R"(
theorem identity : P -> P
proof
  assume h : P
  then P -> P by h and h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, AliasTherefore) {
    // "therefore" is interchangeable with "then"
    auto diag = run_checker("alias_therefore", R"(
theorem mp : Q
proof
  suppose hpq : P -> Q
  suppose hp  : P
  therefore Q by hpq and hp
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, AliasThus) {
    // "thus" is interchangeable with "then"
    auto diag = run_checker("alias_thus", R"(
theorem mp2 : Q
proof
  suppose hpq : P -> Q
  suppose hp  : P
  thus Q by hpq and hp
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, AliasWeHave) {
    // "we have" is interchangeable with "have"
    auto diag = run_checker("alias_we_have", R"(
theorem chain : Q
proof
  suppose hpq : P -> Q
  suppose hp  : P
  we have hq : Q by hpq and hp
  then Q by hq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, AliasQed) {
    // "qed" closes a proof block the same as "end"
    auto diag = run_checker("alias_qed", R"(
theorem identity2 : P -> P
proof
  suppose h : P
  then P -> P by h and h
qed
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, AliasMixed) {
    // All four aliases (assume, we have, therefore, qed) in one proof
    auto diag = run_checker("alias_mixed", R"(
theorem mixed : P -> Q
proof
  assume hpq : P -> Q
  assume hp  : P
  we have hq : Q by hpq and hp
  therefore P -> Q by hp and hq
qed
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── New constructs ─────────────────────────────────────────────────────────────

// Biconditional: "A iff B" desugars to "(A→B) ∧ (B→A)" at parse time, so both
// the theorem declaration and the then-step see the same (A→B)∧(B→A) prop.
TEST(CheckerTest, BiconditionalInDeclaration) {
    auto diag = run_checker("bic_decl", R"(
theorem fwd_bwd : A iff B
proof
  suppose hab : A -> B
  suppose hba : B -> A
  then A iff B by hab and hba
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, BiconditionalElim) {
    // ab_bic desugars to (A->B)∧(B->A); AndElimL extracts A->B, then ImplElim derives B.
    auto diag = run_checker("bic_elim", R"(
axiom ab_bic : A iff B
theorem forward : A -> B
proof
  suppose ha : A
  have fwd : A -> B by ab_bic
  have hb  : B      by fwd and ha
  then A -> B by ha and hb
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// Cases step: OrElim with named case arms.
// 'cases' must be the last step before 'end'/'qed' because the arm step loop
// stops only on 'case' or 'end', so a trailing 'then' would be consumed by the
// last arm.  The theorem therefore declares the arm conclusion directly.
TEST(CheckerTest, ValidCasesStep) {
    auto diag = run_checker("cases_step", R"(
axiom pr  : P -> R
axiom qr  : Q -> R
axiom hor : P or Q

theorem or_elim : R
proof
  cases result : hor
    case hp : P => then R by pr and hp
    case hq : Q => then R by qr and hq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidCasesWithHaveArms) {
    // Arms may contain intermediate 'have' steps before the final 'then'.
    auto diag = run_checker("cases_have_arms", R"(
axiom pr  : P -> R
axiom rs  : R -> S
axiom qr  : Q -> R
axiom hor : P or Q

theorem or_to_s : S
proof
  cases result : hor
    case hp : P =>
      have hr : R by pr and hp
      then S by rs and hr
    case hq : Q =>
      have hr : R by qr and hq
      then S by rs and hr
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InvalidCasesWrongDisjunct) {
    // Arm propositions don't match the disjuncts of the hypothesis.
    auto diag = run_checker("cases_wrong_disjunct", R"(
theorem bad : P or Q -> R
proof
  suppose h : P or Q
  cases result : h
    case hp : P =>
      then R by hp
    case hq : X =>
      then R by hq
  then P or Q -> R by h and result
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, InvalidCasesNotDisjunction) {
    // Ref must be a disjunction.
    auto diag = run_checker("cases_not_disj", R"(
theorem bad : P -> Q
proof
  suppose h : P
  cases result : h
    case ha : P => then Q by ha
    case hb : P => then Q by hb
  then P -> Q by h and result
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// Import: axioms and proved lemmas from the imported file are available.
TEST(CheckerTest, ValidImport) {
    namespace fs = std::filesystem;
    auto dir = fs::temp_directory_path();
    auto lib  = dir / "forall_import_lib.forall";
    auto main = dir / "forall_import_main.forall";

    std::ofstream{lib}  << "axiom base : P -> Q\n";
    std::ofstream{main} << R"(
import "forall_import_lib.forall"
theorem use_import : P -> Q
proof
  suppose h  : P
  have    hq : Q by base and h
  then P -> Q by h and hq
end
)";

    diag::DiagnosticEngine diag;
    checker::Checker c{diag};
    c.check(main);
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidImportLemma) {
    // A proved lemma in the imported file is also accessible.
    namespace fs = std::filesystem;
    auto dir = fs::temp_directory_path();
    auto lib  = dir / "forall_import_lemma_lib.forall";
    auto main = dir / "forall_import_lemma_main.forall";

    std::ofstream{lib}  << R"(
axiom ax : A -> B
lemma a_to_b : A -> B
proof
  suppose h  : A
  have    hb : B by ax and h
  then A -> B by h and hb
end
)";
    std::ofstream{main} << R"(
import "forall_import_lemma_lib.forall"
axiom bc : B -> C
theorem a_to_c : A -> C
proof
  suppose h : A
  have hb : B by a_to_b and h
  have hc : C by bc and hb
  then A -> C by h and hc
end
)";

    diag::DiagnosticEngine diag;
    checker::Checker c{diag};
    c.check(main);
    EXPECT_FALSE(diag.hasErrors());
}

// ── Quantifiers ────────────────────────────────────────────────────────────────

// ── Core arithmetic — end-to-end checker tests ────────────────────────────────
//
// The kernel has no arithmetic inference rules yet, so these tests verify:
//   • Relational axioms are accepted (introduce_axiom handles PropRel/PropPred)
//   • Proved theorems can re-use such axioms via the Assumption rule
//   • PropRel equality works so check_proof validates the conclusion correctly

TEST(CheckerTest, RelationalAxiomAccepted) {
    // Axioms with relational propositions are accepted without errors.
    auto diag = run_checker("rel_axiom", R"(
axiom nonneg  : n >= 0
axiom bounded : n < N
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, RelationalTheoremByAssumption) {
    // A theorem whose statement is a relational prop can be proved via Assumption.
    auto diag = run_checker("rel_assumption", R"(
axiom bound : x < N
theorem restate : x < N
proof
  then x < N by bound
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, RelationalSupposeAndConclude) {
    // suppose h : n >= 0; then n >= 0 by h  uses Assumption rule.
    auto diag = run_checker("rel_suppose", R"(
theorem trivial_rel : n >= 0 -> n >= 0
proof
  suppose h : n >= 0
  then n >= 0 -> n >= 0 by h and h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, AbsValueAxiomAccepted) {
    auto diag = run_checker("abs_axiom", "axiom abs_nonneg : |x| >= 0");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ExponentiationAxiomAccepted) {
    auto diag = run_checker("pow_axiom", "axiom sq_nonneg : x ^ 2 >= 0");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, DivModAxiomsAccepted) {
    auto diag = run_checker("divmod_axioms", R"(
axiom div_bound : n div 2 >= 0
axiom mod_range : n mod 2 < 2
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, FunctionCallRelAxiomAccepted) {
    // f(x) > 0 as an axiom, used as a hypothesis
    auto diag = run_checker("call_rel_axiom", R"(
axiom f_pos : f(x) > 0
theorem f_still_pos : f(x) > 0
proof
  then f(x) > 0 by f_pos
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, PredicateAxiomAccepted) {
    // Predicate application as an opaque proposition
    auto diag = run_checker("pred_axiom", R"(
axiom primality : isPrime(n)
theorem restate_pred : isPrime(n)
proof
  then isPrime(n) by primality
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, MixedPropRelAndLogical) {
    // Combining relational and logical connectives in one proof
    auto diag = run_checker("mixed_rel_logical", R"(
axiom pos   : x > 0
axiom small : x < 1
theorem bounded : x > 0 and x < 1
proof
  have hboth : x > 0 and x < 1 by pos and small
  then x > 0 and x < 1 by hboth
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InvalidWrongRelConclusion) {
    // The step correctly proves x < N (Assumption rule), but the theorem
    // declares x < N -> x <= N — so the concluded prop doesn't match.
    auto diag = run_checker("wrong_rel_conclusion", R"(
axiom lt_ax : x < N
theorem bad : x < N -> x <= N
proof
  then x < N by lt_ax
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "wrong proposition"));
}

TEST(CheckerTest, QuantifierAxiom) {
    // Axioms with quantifiers are accepted; kernel semantics are longer-term.
    auto diag = run_checker("quant_axiom", "axiom all_p : for all x, P");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, QuantifierExistsAxiom) {
    auto diag = run_checker("quant_exists_axiom", "axiom some_p : there exists x, P");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, QuantifierTheoremStatement) {
    // A theorem whose statement contains a quantifier: the checker accepts the
    // statement (no kernel quantifier rules yet, but parsing and axiom-seeding work).
    auto diag = run_checker("quant_theorem", R"(
axiom univ : for all x : Nat, P
theorem restate : for all x : Nat, P
proof
  then for all x : Nat, P by univ
end
)");
    EXPECT_FALSE(diag.hasErrors());
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

// ── Lambda abstraction and conditional terms ───────────────────────────────────

TEST(CheckerTest, LambdaAxiomAccepted) {
    // An axiom whose statement contains a lambda expression is accepted.
    auto diag = run_checker("lambda_axiom", "axiom id_fn : f = fun x => x");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, LambdaTypedAxiomAccepted) {
    auto diag = run_checker("lambda_typed_axiom",
                            "axiom sq : f = \xCE\xBB x : Nat, x * x");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, LambdaTheoremByAssumption) {
    // The checker can match a lambda-containing relational prop via Assumption.
    auto diag = run_checker("lambda_assume", R"(
axiom fn_def : f = fun x => x + 1
theorem restate : f = fun x => x + 1
proof
  then f = fun x => x + 1 by fn_def
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, CondExprAxiomAccepted) {
    // An axiom with a conditional expression is accepted.
    auto diag = run_checker("cond_axiom",
                            "axiom abs_val : P and if x >= 0 then x else 0 >= 0");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, CondExprTheoremByAssumption) {
    auto diag = run_checker("cond_assume", R"(
axiom max_def : P and if a >= b then a else b = m
theorem restate : P and if a >= b then a else b = m
proof
  then P and if a >= b then a else b = m by max_def
end
)");
    EXPECT_FALSE(diag.hasErrors());
}
