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
    EXPECT_TRUE(has_error(diag, "expected"));
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
    EXPECT_TRUE(has_error(diag, "expected"));
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

// ── Quantifier rules: ForallElim and ExistsIntro via "by h at t" ───────────────

TEST(CheckerTest, ForallElimHaveStep) {
    // ∀x. P(x) + witness n → P(n) via ForallElim.
    // Uses predicate application: P(x) parsed as PropPred{"P", [ExprVar{x}]}.
    auto diag = run_checker("forall_elim_have", R"(
axiom univ : for all x, P(x)
theorem inst : P(n)
proof
  have hn : P(n) by univ at n
  then P(n) by hn
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ForallElimThenStep) {
    // ForallElim directly in the concluding "then" step.
    auto diag = run_checker("forall_elim_then", R"(
axiom all_pos : for all x, x > 0
theorem n_pos : n > 0
proof
  then n > 0 by all_pos at n
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ExistsIntroHaveStep) {
    // P(n) + witness n → ∃x. P(x) via ExistsIntro.
    auto diag = run_checker("exists_intro_have", R"(
axiom fact : P(n)
theorem witness : there exists x, P(x)
proof
  have ex : there exists x, P(x) by fact at n
  then there exists x, P(x) by ex
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ExistsIntroThenStep) {
    // ExistsIntro directly in the concluding "then" step.
    auto diag = run_checker("exists_intro_then", R"(
axiom fact : n > 0
theorem some_pos : there exists x, x > 0
proof
  then there exists x, x > 0 by fact at n
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ForallElimAndThenUse) {
    // ForallElim result used as a premise in a later step.
    auto diag = run_checker("forall_elim_chain", R"(
axiom all_p_imp_q : for all x, P(x) -> Q(x)
axiom pn : P(n)
theorem qn : Q(n)
proof
  have impl : P(n) -> Q(n) by all_p_imp_q at n
  have hqn  : Q(n)         by impl and pn
  then Q(n) by hqn
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InvalidForallElimWrongConclusion) {
    // Witness n given, but conclusion P(m) != P(n) — kernel should reject.
    auto diag = run_checker("forall_elim_wrong_conc", R"(
axiom univ : for all x, P(x)
theorem bad : P(m)
proof
  then P(m) by univ at n
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, InvalidAtWitnessNotForallOrExists) {
    // "at" witness given but hypothesis is not ∀x.P and conclusion is not ∃x.P.
    auto diag = run_checker("at_wrong_form", R"(
axiom plain : P -> Q
theorem bad : P -> Q
proof
  then P -> Q by plain at n
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, InvalidAtWitnessTwoRefs) {
    // "at" witness requires exactly one ref; two refs should produce an error.
    auto diag = run_checker("at_two_refs", R"(
axiom ax1 : P
axiom ax2 : Q
theorem bad : there exists x, P
proof
  then there exists x, P by ax1 and ax2 at n
end
)");
    EXPECT_TRUE(diag.hasErrors());
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

// ── Aggregate operators ────────────────────────────────────────────────────────

TEST(CheckerTest, SumAxiomAccepted) {
    auto diag = run_checker("sum_axiom", "axiom triangle : sum i < n, i >= 0");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, SumTheoremByAssumption) {
    auto diag = run_checker("sum_assume", R"(
axiom s_def : sum i < n, i >= 0
theorem restate_sum : sum i < n, i >= 0
proof
  then sum i < n, i >= 0 by s_def
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ProdAxiomAccepted) {
    auto diag = run_checker("prod_axiom", "axiom prod_pos : prod i : Nat, i >= 0");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, FloorCeilAxiomsAccepted) {
    auto diag = run_checker("floor_ceil_axioms", R"(
axiom floor_bound : floor(x) <= x
axiom ceil_bound  : x <= ceil(x)
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, FactorialAxiomAccepted) {
    auto diag = run_checker("factorial_axiom", "axiom fact_pos : n! > 0");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, FactorialTheoremByAssumption) {
    auto diag = run_checker("factorial_assume", R"(
axiom fact_pos : n! > 0
theorem restate_fact : n! > 0
proof
  then n! > 0 by fact_pos
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Algebraic operators (compose / ∘, inv) ─────────────────────────────────────

TEST(CheckerTest, ComposeAxiomAccepted) {
    auto diag = run_checker("compose_axiom", "axiom comp : f compose g = h");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ComposeTheoremByAssumption) {
    auto diag = run_checker("compose_assume", R"(
axiom comp_def : f compose g = h
theorem restate_comp : f compose g = h
proof
  then f compose g = h by comp_def
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ComposeUnicodeAxiomAccepted) {
    // Unicode ∘ (U+2218 = E2 88 98) produces the same AST as "compose"
    auto diag = run_checker("compose_unicode_axiom",
                            "axiom comp_u : f \xE2\x88\x98 g = h");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InvAxiomAccepted) {
    auto diag = run_checker("inv_axiom", "axiom inv_ax : inv f = g");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InvTheoremByAssumption) {
    auto diag = run_checker("inv_assume", R"(
axiom inv_def : inv f = g
theorem restate_inv : inv f = g
proof
  then inv f = g by inv_def
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ComposeAndInvAxiomsAccepted) {
    // Multiple axioms using both compose and inv together.
    // Note: lhs avoids a leading '(' (which the prop parser reads as grouped-prop).
    // f compose g compose h is left-assoc: (f∘g)∘h; rhs uses parentheses inside expr context.
    auto diag = run_checker("compose_inv_axioms", R"(
axiom inv_comp   : inv (f compose g) = inv g compose inv f
axiom comp_assoc : f compose g compose h = f compose (g compose h)
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── DeclKind::Definition ──────────────────────────────────────────────────────

TEST(CheckerTest, DefinitionAccepted) {
    auto diag = run_checker("def_accepted", "definition refl : x = x");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, DefinitionUsedInProof) {
    // A definition adds its name to module_env the same way an axiom does.
    auto diag = run_checker("def_used", R"(
definition refl_eq : x = x
theorem restate_def : x = x
proof
  then x = x by refl_eq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, DefinitionWithParamsParsed) {
    // Parameters are parsed and discarded until the type system is in place.
    // The body proposition is treated like an axiom statement.
    auto diag = run_checker("def_with_params", R"(
definition f_pos (x : Real) : f(x) > 0
theorem use_def : f(x) > 0
proof
  then f(x) > 0 by f_pos
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, DefinitionAccumulatesInModuleEnv) {
    // A definition and a later axiom can both be cited together in one proof.
    auto diag = run_checker("def_scope", R"(
definition pos_def : x > 0
axiom bound : x < 1
theorem interval : x > 0 and x < 1
proof
  have h : x > 0 and x < 1 by pos_def and bound
  then x > 0 and x < 1 by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, DefinitionFollowedByLemma) {
    // A proved lemma after a definition can use the definition.
    auto diag = run_checker("def_then_lemma", R"(
definition eq_self : n = n
lemma restate : n = n
proof
  then n = n by eq_self
end
theorem use_lemma : n = n
proof
  then n = n by restate
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Scoped assumption blocks (ScopeStack) ────────────────────────────────────

TEST(CheckerTest, ScopeStackCasesArmShadowing) {
    // Both case arms bind 'h' locally; each uses its own arm assumption.
    // The outer suppose h : P or Q is in a lower frame and is shadowed.
    auto diag = run_checker("scope_shadow", R"(
axiom hor : P or Q
axiom pr  : P -> R
axiom qr  : Q -> R

theorem shadow_test : R
proof
  suppose h : P or Q
  cases result : hor
    case h : P => then R by pr and h
    case h : Q => then R by qr and h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Cases step: "done" arm terminator allows subsequent steps ─────────────────

TEST(CheckerTest, ValidCasesWithDoneAndFollowingThen) {
    // With "done" on each arm, a "then" step after "cases" uses the stored result.
    auto diag = run_checker("cases_done_following_then", R"(
axiom pr  : P -> R
axiom qr  : Q -> R
axiom rs  : R -> S
axiom hor : P or Q

theorem or_then_s : S
proof
  cases result : hor
    case hp : P => then R by pr and hp done
    case hq : Q => then R by qr and hq done
  then S by rs and result
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidCasesWithDoneHaveArmsAndFollowingThen) {
    // Multi-step arms with done, followed by a then step.
    auto diag = run_checker("cases_done_have_then", R"(
axiom pr  : P -> R
axiom rs  : R -> S
axiom qr  : Q -> R
axiom hor : P or Q

theorem or_to_s : S
proof
  cases result : hor
    case hp : P =>
      have hr : R by pr and hp
      then R by hr
    done
    case hq : Q =>
      then R by qr and hq
    done
  then S by rs and result
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InvalidDoneOutsideCases) {
    // "done" as a standalone step is not a valid proof step; expect a parse error.
    auto diag = run_checker("done_outside_cases", R"(
theorem bad : P
proof
  suppose h : P
  done
  then P by h
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// ── ForallIntro via TakeStep ───────────────────────────────────────────────────

TEST(CheckerTest, ValidForallIntro) {
    // Simplest ∀-intro: take n, assume P(n) as axiom, generalize.
    auto diag = run_checker("forall_intro_valid", R"(
axiom base : for all n : Nat, P(n)
theorem all_p : for all n : Nat, P(n)
proof
  take n : Nat
  have h : P(n) by base at n
  then for all n : Nat, P(n) by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidForallIntroNoType) {
    // take without type annotation — both the take and the ∀ omit type.
    auto diag = run_checker("forall_intro_no_type", R"(
axiom px : P(x)
theorem all_p : for all x, P(x)
proof
  take x
  have h : P(x) by px
  then for all x, P(x) by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidForallIntroWithHaveStep) {
    // ForallIntro result stored in a have step (not then).
    auto diag = run_checker("forall_intro_have", R"(
axiom base : for all n : Nat, P(n)
theorem all_p : for all n : Nat, P(n)
proof
  take n : Nat
  have pn : P(n) by base at n
  have result : for all n : Nat, P(n) by pn
  then for all n : Nat, P(n) by result
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InvalidForallIntro_MissingTake) {
    // Trying to use ForallIntro without a preceding TakeStep — error.
    auto diag = run_checker("forall_intro_missing_take", R"(
axiom pn : P(n)
theorem all_p : for all n, P(n)
proof
  have h : P(n) by pn
  then for all n, P(n) by h
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, InvalidForallIntro_TakeVarNotFresh) {
    // n appears free in an assumption — take n should fail the freshness check.
    auto diag = run_checker("forall_intro_not_fresh", R"(
theorem bad : for all n, P(n)
proof
  suppose hn : P(n)
  take n
  then for all n, P(n) by hn
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, ValidForallIntroAfterOtherSteps) {
    // Unrelated hypotheses that don't mention n are fine before take n.
    auto diag = run_checker("forall_intro_unrelated_hyp", R"(
axiom pa : P(a)
axiom base : for all n : Nat, P(n)
theorem all_p : for all n : Nat, P(n)
proof
  suppose ha : P(a)
  take n : Nat
  have h : P(n) by base at n
  then for all n : Nat, P(n) by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── ExistsElim via ObtainStep ─────────────────────────────────────────────────

TEST(CheckerTest, ValidExistsElim) {
    // Classic ∃-elim: from ∃n.P(n), derive Q (which doesn't mention n).
    // "done" after the arm allows the outer then to follow.
    auto diag = run_checker("exists_elim_valid", R"(
axiom qax : Q
theorem t : Q
proof
  suppose he : there exists n, P(n)
  obtain result from he
    case n , hn : P(n) =>
      have q : Q by qax
      then Q by q
  done
  then Q by result
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidExistsElim_WithType) {
    // obtain with typed variable annotation; "done" allows outer then.
    auto diag = run_checker("exists_elim_typed", R"(
axiom qax : Q
theorem t : Q
proof
  suppose he : there exists n : Nat, P(n)
  obtain result from he
    case n : Nat , hn : P(n) =>
      have q : Q by qax
      then Q by q
  done
  then Q by result
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidExistsElim_HypUsedInProof) {
    // The arm hypothesis hn : P(n) can be used in the sub-proof.
    auto diag = run_checker("exists_elim_hyp_used", R"(
axiom impl : for all x, P(x) implies Q
theorem t : Q
proof
  suppose he : there exists n, P(n)
  obtain result from he
    case n , hn : P(n) =>
      have impl_n : P(n) implies Q by impl at n
      have q : Q by impl_n and hn
      then Q by q
  done
  then Q by result
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidExistsElim_WithDone) {
    // obtain with "done" allows a then step afterward
    auto diag = run_checker("exists_elim_done", R"(
axiom qax : Q
theorem t : Q
proof
  suppose he : there exists n, P(n)
  obtain result from he
    case n , hn : P(n) =>
      then Q by qax
  done
  then Q by result
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InvalidExistsElim_ConclusionMentionsVar) {
    // Conclusion P(n) has n free — violates the ∃-elim side condition.
    // (Note: ∃n.P(n) would be fine because n is bound; P(n) is the violation.)
    auto diag = run_checker("exists_elim_side_condition", R"(
theorem bad : P(n)
proof
  suppose he : there exists n, P(n)
  obtain result from he
    case n , hn : P(n) =>
      then P(n) by hn
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, InvalidExistsElim_VarNotFresh) {
    // n already appears free in an assumption — freshness violation at take site.
    auto diag = run_checker("exists_elim_not_fresh", R"(
theorem bad : Q
proof
  suppose hn : P(n)
  suppose he : there exists n, P(n)
  obtain result from he
    case n , hn2 : P(n) =>
      then Q by hn
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, InvalidExistsElim_HypPropMismatch) {
    // Stated hypothesis doesn't match the substituted body of the existential.
    auto diag = run_checker("exists_elim_hyp_mismatch", R"(
theorem bad : Q
proof
  suppose he : there exists n, P(n)
  obtain result from he
    case n , hn : Q =>        -- should be P(n), not Q
      then Q by hn
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, InvalidExistsElim_RefNotExistential) {
    // The ref is not an existential — should fail.
    auto diag = run_checker("exists_elim_not_exists", R"(
theorem bad : Q
proof
  suppose hp : P(n)
  obtain result from hp      -- hp is P(n), not ∃n.P
    case n , hn : P(n) =>
      then Q by hn
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// ── Type-mismatch warnings ─────────────────────────────────────────────────────

static bool has_warning(const diag::DiagnosticEngine& diag, const std::string& fragment) {
    for (const auto& d : diag.diagnostics())
        if (d.severity == diag::Severity::Warning
                && d.message.find(fragment) != std::string::npos)
            return true;
    return false;
}

TEST(CheckerTest, TypeWarning_PropInBinaryArithmetic) {
    // P : Prop, n : Nat — P + n is a type mismatch (Case A: mismatch in sub-expr).
    // The axiom makes the proof valid so hasErrors() is false.
    auto diag = run_checker("type_warn_bin_arith", R"(
axiom ax : P + n > 0
theorem t : P + n > 0
proof
  take P : Prop
  take n : Nat
  have h : P + n > 0 by ax
  then P + n > 0 by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_TRUE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, TypeWarning_PropEqualToNat) {
    // P : Prop = 0 : Nat — comparing Prop to Nat (Case B: top-level mismatch).
    auto diag = run_checker("type_warn_prop_eq_nat", R"(
axiom ax : P = 0
theorem t : P = 0
proof
  take P : Prop
  then P = 0 by ax
end
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_TRUE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, TypeWarning_NoWarnWhenTypesCompatible) {
    // x : Nat, 1 : Nat — x + 1 > 0 is well-typed; no warning.
    auto diag = run_checker("type_no_warn_nat", R"(
axiom ax : x + 1 > 0
theorem t : x + 1 > 0
proof
  take x : Nat
  then x + 1 > 0 by ax
end
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_FALSE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, TypeWarning_NoWarnWhenNoTypeAnnotations) {
    // Variables without 'take x : T' have unknown types → no warning emitted.
    auto diag = run_checker("type_no_warn_no_ann", R"(
axiom ax : P + n > 0
theorem t : P + n > 0
proof
  then P + n > 0 by ax
end
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_FALSE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, TypeWarning_NatAndRealCompatible) {
    // x : Nat, y : Real — Nat promotes to Real, so x + y is well-typed.
    auto diag = run_checker("type_no_warn_nat_real", R"(
axiom ax : x + y > 0
theorem t : x + y > 0
proof
  take x : Nat
  take y : Real
  then x + y > 0 by ax
end
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_FALSE(has_warning(diag, "type mismatch"));
}

// ── FuncSigTable: sig built from definition params ────────────────────────────
//
// Warnings only fire when the ExprCall appears inside a PropRel (expression
// context).  'then isPrime(n)' alone produces PropPred, not PropRel, and
// never reaches check_proprel_types.  To exercise the sig table we write
// propositions like 'isPrime(x) = 0' or 'isPrime(n) = isPrime(n)'.

TEST(CheckerTest, FuncSigTable_WrongArgType_EmitsWarning) {
    // isPrime : Nat -> Prop; isPrime(x) = 0 with x:Prop
    //   lhs ExprCall: arg x has type Prop, expected Nat → Mismatch (Case A)
    auto diag = run_checker("sig_table_arg_mismatch", R"(
definition isPrime (n : Nat) : isPrime(n)
axiom weird : isPrime(x) = 0
theorem t : isPrime(x) = 0
proof
  take x : Prop
  then isPrime(x) = 0 by weird
end
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_TRUE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, FuncSigTable_CorrectArgType_NoWarning) {
    // isPrime : Nat -> Prop; isPrime(n) = isPrime(n) with n:Nat
    //   both sides infer TypeProp → no numeric-vs-Prop mismatch
    auto diag = run_checker("sig_table_arg_ok", R"(
definition isPrime (n : Nat) : isPrime(n)
axiom sym : isPrime(n) = isPrime(n)
theorem t : isPrime(n) = isPrime(n)
proof
  take n : Nat
  then isPrime(n) = isPrime(n) by sym
end
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_FALSE(has_warning(diag, "type mismatch"));
}

// ── Deep type-checking: PropForall/PropExists bind typed vars into TypeEnv ────

TEST(CheckerTest, DeepTypeCheck_QuantifierBodyMismatch_AxiomWarns) {
    // Axiom with ∀ P : Prop, ∀ n : Nat, P + n > 0
    // Body P + n > 0 with {P:Prop, n:Nat} → arithmetic mismatch → Warning
    auto diag = run_checker("deep_quant_axiom_warn", R"(
axiom weird : for all P : Prop, for all n : Nat, P + n > 0
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_TRUE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, DeepTypeCheck_QuantifierBodyWellTyped_NoWarning) {
    // Axiom with ∀ n : Nat, n + 1 > 0 — well-typed
    auto diag = run_checker("deep_quant_axiom_ok", R"(
axiom pos : for all n : Nat, n + 1 > 0
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_FALSE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, DeepTypeCheck_TheoremStatementMismatch_Warns) {
    // Theorem with ∀ P : Prop, P > 0 — Prop compared to Nat in body
    auto diag = run_checker("deep_quant_thm_warn", R"(
axiom ax : for all P : Prop, P > 0
theorem t : for all P : Prop, P > 0
proof
  suppose h : for all P : Prop, P > 0
  then for all P : Prop, P > 0 by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_TRUE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, DeepTypeCheck_UnaryPropNotPropagated) {
    // not P — no PropRel, no type warning
    auto diag = run_checker("deep_not_no_warn", R"(
axiom ax : not P
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_FALSE(has_warning(diag, "type mismatch"));
}

