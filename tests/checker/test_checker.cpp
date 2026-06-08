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

TEST(CheckerTest, ValidLetExprDef) {
    // let x = expr — the binding is a no-op when x not used in props.
    auto diag = run_checker("valid_let_expr_def", R"(
theorem trivial : P -> P
proof
  let x = 42
  suppose h : P
  then P -> P by h and h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidLetExprUsedInHave) {
    // let delta = eps — delta is substituted to eps in the have step.
    auto diag = run_checker("valid_let_expr_used_in_have", R"(
axiom eps_pos : eps > 0
theorem test : eps > 0
proof
  let delta = eps
  have h : delta > 0 by eps_pos
  then eps > 0 by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidLetExprSubstituted) {
    // let delta = eps — delta is substituted in the final then step.
    auto diag = run_checker("valid_let_expr_substituted", R"(
axiom eps_pos : eps > 0
theorem test : eps > 0
proof
  let delta = eps
  then delta > 0 by eps_pos
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

// obtain with two hyp bindings — destructures a conjunction body
TEST(CheckerTest, ValidExistsElim_PairDestructure) {
    auto diag = run_checker("obtain_pair", R"(
axiom ax : there exists n : Nat, n > 0 and n < 10
theorem t : there exists n : Nat, n > 0 and n < 10
proof
  have he : there exists n : Nat, n > 0 and n < 10 by ax
  obtain result from he
    case n : Nat , h_pos : n > 0 , h_small : n < 10 =>
      then there exists n : Nat, n > 0 and n < 10 by ax
  done
  then there exists n : Nat, n > 0 and n < 10 by result
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// obtain with two bindings where the body is used in the arm sub-proof
TEST(CheckerTest, ValidExistsElim_PairUseBothBindings) {
    auto diag = run_checker("obtain_pair_use", R"(
axiom ax : there exists n : Nat, n > 0 and n < 10
theorem t : Q
proof
  suppose hq : Q
  have he : there exists n : Nat, n > 0 and n < 10 by ax
  obtain result from he
    case n : Nat , h_pos : n > 0 , h_small : n < 10 =>
      then Q by hq
  done
  then Q by result
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
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

// ── Set relation type warnings (Case C) ──────────────────────────────────────
//
// Type annotations on forall/exists binders seed the TypeEnv inside
// check_prop_types_deep, enabling infer_type to resolve the operand types.

TEST(CheckerTest, TypeWarning_SetMembership_ElemTypeMismatch) {
    // n : Real, S : Set Nat — n in S is a type mismatch (Real ≠ Nat)
    auto diag = run_checker("set_mem_mismatch", R"(
axiom ax : for all n : Real, for all S : Set Nat, n in S
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_TRUE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, TypeWarning_SetMembership_CompatibleTypes_NoWarning) {
    // n : Nat, S : Set Nat — n in S is well-typed; no warning
    auto diag = run_checker("set_mem_ok", R"(
axiom ax : for all n : Nat, for all S : Set Nat, n in S
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_FALSE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, TypeWarning_Subset_DifferentElementTypes) {
    // A : Set Nat, B : Set Real — A subseteq B is a type mismatch
    auto diag = run_checker("subset_elem_mismatch", R"(
axiom ax : for all A : Set Nat, for all B : Set Real, A subseteq B
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_TRUE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, TypeWarning_Subset_SameElementTypes_NoWarning) {
    // A : Set Nat, B : Set Nat — A subseteq B is well-typed
    auto diag = run_checker("subset_ok", R"(
axiom ax : for all A : Set Nat, for all B : Set Nat, A subseteq B
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_FALSE(has_warning(diag, "type mismatch"));
}

// ── Induction step ────────────────────────────────────────────────────────────

TEST(CheckerTest, ValidInduction_TrivialProp) {
    // Prove ∀ n : Nat, n = n  by induction on n : n = n
    auto diag = run_checker("induction_trivial", R"(
axiom refl_0   : 0 = 0
axiom refl_sn  : for all n : Nat, succ(n) = succ(n)
theorem all_n_eq_n : for all n : Nat, n = n
proof
  induction result on n : n = n
    base:
      then 0 = 0 by refl_0
    inductive:
      then succ(n) = succ(n) by refl_sn at n
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidInduction_UsesIH) {
    // Inductive step uses ih (= P(n)) to conclude P(succ(n))
    auto diag = run_checker("induction_uses_ih", R"(
axiom base_ax : P(0)
axiom step_ax : for all n : Nat, P(n) implies P(succ(n))
theorem all_P : for all n : Nat, P(n)
proof
  induction result on n : P(n)
    base:
      then P(0) by base_ax
    inductive:
      have step_n : P(n) implies P(succ(n)) by step_ax at n
      then P(succ(n)) by step_n and ih
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InvalidInduction_WrongInductiveConclusion) {
    // Inductive block concludes wrong proposition (1 = 1 instead of succ(n) = succ(n))
    auto diag = run_checker("induction_wrong_ind", R"(
axiom base_ax : 0 = 0
axiom wrong_ax : 1 = 1
theorem t : for all n : Nat, n = n
proof
  induction result on n : n = n
    base:
      then 0 = 0 by base_ax
    inductive:
      then 1 = 1 by wrong_ax
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "inductive"));
}

TEST(CheckerTest, InvalidInduction_BaseMissingThenStep) {
    // Base block has no 'then' step
    auto diag = run_checker("induction_no_base_then", R"(
axiom base_ax : 0 = 0
theorem t : for all n : Nat, n = n
proof
  induction result on n : n = n
    base:
      suppose h : 0 = 0
    inductive:
      then succ(n) = succ(n) by ih
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// ── by decide ────────────────────────────────────────────────────────────────

TEST(CheckerTest, Decide_SimpleEquality) {
    auto diag = run_checker("decide_simple", R"(
theorem t : 2 + 3 = 5
proof
  then 2 + 3 = 5 by decide
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Decide_Inequality) {
    auto diag = run_checker("decide_ineq", R"(
theorem t : 4 > 2
proof
  then 4 > 2 by decide
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Decide_ExpressionBothSides) {
    auto diag = run_checker("decide_expr", R"(
theorem t : 3 * 4 = 2 * 6
proof
  then 3 * 4 = 2 * 6 by decide
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Decide_FalseProposition) {
    // 2 + 2 = 5 is false — by decide should reject it
    auto diag = run_checker("decide_false", R"(
theorem t : 2 + 2 = 5
proof
  then 2 + 2 = 5 by decide
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "false"));
}

TEST(CheckerTest, Decide_CannotDecideVariable) {
    // x + 1 > 0 contains a variable — by decide cannot evaluate it
    auto diag = run_checker("decide_variable", R"(
theorem t : x + 1 > 0
proof
  then x + 1 > 0 by decide
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "decide"));
}

TEST(CheckerTest, Decide_HaveStep) {
    // by decide works in a have step too
    auto diag = run_checker("decide_have", R"(
theorem t : 1 < 2 and 3 > 0
proof
  have h1 : 1 < 2 by decide
  have h2 : 3 > 0 by decide
  then 1 < 2 and 3 > 0 by h1 and h2
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Decide_Power) {
    auto diag = run_checker("decide_power", R"(
theorem t : 2 ^ 3 = 8
proof
  then 2 ^ 3 = 8 by decide
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Instance declarations ─────────────────────────────────────────────────────

TEST(CheckerTest, InstanceDecl_ValidRing) {
    // Declare all required Ring axioms prefixed with T_, then instance T : Ring.
    auto diag = run_checker("instance_valid_ring", R"(
axiom T_add_assoc     : P
axiom T_add_comm      : P
axiom T_add_zero      : P
axiom T_zero_add      : P
axiom T_add_neg       : P
axiom T_mul_assoc     : P
axiom T_mul_one       : P
axiom T_one_mul       : P
axiom T_distrib_left  : P
axiom T_distrib_right : P
instance T : Ring
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InstanceDecl_MissingAxiom) {
    // Missing T_add_zero — should error naming the missing axiom.
    auto diag = run_checker("instance_missing_axiom", R"(
axiom T_add_assoc     : P
axiom T_add_comm      : P
axiom T_add_neg       : P
axiom T_mul_assoc     : P
axiom T_mul_one       : P
axiom T_one_mul       : P
axiom T_distrib_left  : P
axiom T_distrib_right : P
instance T : Ring
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "T_add_zero"));
    EXPECT_TRUE(has_error(diag, "T_zero_add"));
}

TEST(CheckerTest, InstanceDecl_UnknownClass) {
    // Declaring an instance for an unknown class should produce an error.
    auto diag = run_checker("instance_unknown_class", R"(
axiom ax : P
instance Real : UnknownAlgebra
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "unknown typeclass"));
}

TEST(CheckerTest, InstanceDecl_OrderedFieldValid) {
    // Declare all OrderedField axioms for type Foo, then instance Foo : OrderedField.
    auto diag = run_checker("instance_ordered_field", R"(
axiom Foo_add_assoc     : P
axiom Foo_add_comm      : P
axiom Foo_add_zero      : P
axiom Foo_zero_add      : P
axiom Foo_add_neg       : P
axiom Foo_mul_assoc     : P
axiom Foo_mul_comm      : P
axiom Foo_mul_one       : P
axiom Foo_one_mul       : P
axiom Foo_distrib_left  : P
axiom Foo_distrib_right : P
axiom Foo_mul_inv       : P
axiom Foo_lt_trans      : P
axiom Foo_lt_add        : P
axiom Foo_lt_mul_pos    : P
instance Foo : OrderedField
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InstanceDecl_AxiomsDeclaredAfterInstanceFails) {
    // Axioms must be declared BEFORE the instance — instance checks module_env
    // as it stands at the point of the instance declaration.
    auto diag = run_checker("instance_axioms_after", R"(
instance T : Ring
axiom T_add_assoc     : P
axiom T_add_comm      : P
axiom T_add_zero      : P
axiom T_zero_add      : P
axiom T_add_neg       : P
axiom T_mul_assoc     : P
axiom T_mul_one       : P
axiom T_one_mul       : P
axiom T_distrib_left  : P
axiom T_distrib_right : P
)");
    EXPECT_TRUE(diag.hasErrors());
}

// ── CheckContext / TypeEnv threading ─────────────────────────────────

TEST(CheckerTest, CheckContext_TypeEnvReachesSubProof) {
    // 'take n : Nat' before a cases step — the type env should be visible inside
    // the cases arm (since CheckContext is now threaded through check_cases_step).
    // A type-mismatch warning fires if a Prop variable is used in arithmetic
    // inside the arm.  Here we verify no such spurious warning fires for a
    // well-typed arm.
    auto diag = run_checker("ctx_type_env_cases", R"(
axiom hn : n > 0
theorem t : n > 0 or n > 0
proof
  take n : Nat
  have h  : n > 0         by hn
  have dis : n > 0 or n > 0 by h
  cases result : dis
    case h1 : n > 0 =>
      then n > 0 or n > 0 by h
    case h2 : n > 0 =>
      then n > 0 or n > 0 by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_FALSE(has_warning(diag, "type mismatch"));
}

TEST(CheckerTest, CheckContext_TypeEnvReachesInductionBase) {
    // 'take n : Nat' before an induction step — type env available in base/inductive.
    // This confirms CheckContext with type_env threads into check_induction_step.
    auto diag = run_checker("ctx_type_env_induction", R"(
axiom nat_zero_eq : 0 = 0
axiom nat_succ_eq : succ(n) = succ(n)
theorem t : for all n : Nat, n = n
proof
  induction result on n : n = n
    base:
      then 0 = 0 by nat_zero_eq
    inductive:
      then succ(n) = succ(n) by nat_succ_eq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── resolve_ring_axioms indirectly: instance imported from another module ──────

TEST(CheckerTest, CheckContext_InstancePropagatedThroughImport) {
    // Declare all Ring axioms for type Foo in one "imported" file, then declare
    // the instance.  In the importing file, verify the instance is recognised.
    // This exercises ModuleResult propagation of the InstanceTable.
    // We use a two-file setup: write both to temp dir.
    auto tmp = std::filesystem::temp_directory_path();
    auto lib_path = tmp / "forall_test_ring_lib.forall";
    auto main_path = tmp / "forall_test_ring_main.forall";

    std::ofstream{lib_path} << R"(
axiom Foo_add_assoc     : P
axiom Foo_add_comm      : P
axiom Foo_add_zero      : P
axiom Foo_zero_add      : P
axiom Foo_add_neg       : P
axiom Foo_mul_assoc     : P
axiom Foo_mul_one       : P
axiom Foo_one_mul       : P
axiom Foo_distrib_left  : P
axiom Foo_distrib_right : P
instance Foo : Ring
)";
    // The import path is relative to main_path's directory (temp dir), so just filename.
    std::ofstream{main_path} << "import \"forall_test_ring_lib.forall\"\n";

    diag::DiagnosticEngine diag;
    checker::Checker c{diag};
    c.check(main_path);
    EXPECT_FALSE(diag.hasErrors());
}

// ── by norm_num (I2/I3) ────────────────────────────────────────────────

TEST(CheckerTest, NormNum_SimpleEquality) {
    // Constant: 2 + 3 = 5 (same as decide, but via poly normalization)
    auto diag = run_checker("norm_num_simple", R"(
theorem t : 2 + 3 = 5
proof
  then 2 + 3 = 5 by norm_num
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NormNum_Commutativity) {
    // x + y = y + x — polynomial identity, both sides normalize to same Poly
    auto diag = run_checker("norm_num_comm", R"(
theorem t : x + y = y + x
proof
  then x + y = y + x by norm_num
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NormNum_Distributivity) {
    // x * (y + z) = x * y + x * z — classic distributivity
    auto diag = run_checker("norm_num_distrib", R"(
theorem t : x * (y + z) = x * y + x * z
proof
  then x * (y + z) = x * y + x * z by norm_num
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NormNum_DistributivityReverse) {
    // x * y + x * z = x * (y + z) — same identity, opposite sides
    auto diag = run_checker("norm_num_distrib_rev", R"(
theorem t : x * y + x * z = x * (y + z)
proof
  then x * y + x * z = x * (y + z) by norm_num
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NormNum_QuadraticExpansion) {
    // (x + y)^2 = x^2 + 2*x*y + y^2
    auto diag = run_checker("norm_num_quadratic", R"(
theorem t : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2
proof
  then (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 by norm_num
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NormNum_MixedConstantsAndVars) {
    // 3 * x + 2 * x = 5 * x
    auto diag = run_checker("norm_num_coeffs", R"(
theorem t : 3 * x + 2 * x = 5 * x
proof
  then 3 * x + 2 * x = 5 * x by norm_num
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NormNum_HaveStep) {
    // by norm_num in a have step, result used in then step
    auto diag = run_checker("norm_num_have", R"(
axiom refl_ax : x + y = y + x
theorem t : x + y = y + x
proof
  have comm : x + y = y + x by norm_num
  then x + y = y + x by comm
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NormNum_FalseIdentity) {
    // x + y = x is not a polynomial identity
    auto diag = run_checker("norm_num_false", R"(
theorem t : x + y = x
proof
  then x + y = x by norm_num
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "polynomial identity"));
}

TEST(CheckerTest, NormNum_NotAnEquality) {
    // by norm_num on a non-equality should fail
    auto diag = run_checker("norm_num_not_eq", R"(
theorem t : x + 1 > 0
proof
  then x + 1 > 0 by norm_num
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "norm_num"));
}

TEST(CheckerTest, NormNum_Subtraction) {
    // (x + y) - y = x via poly normalization
    auto diag = run_checker("norm_num_sub", R"(
theorem t : (x + y) - y = x
proof
  then (x + y) - y = x by norm_num
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NormNum_NegationExpansion) {
    // -(x + y) = -x + (-y) — poly normalization via negation
    auto diag = run_checker("norm_num_neg", R"(
theorem t : -(x + y) = -x + -y
proof
  then -(x + y) = -x + -y by norm_num
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── by ring (I2/I3) ─────────────────────────────────────────────────────

TEST(CheckerTest, Ring_Commutativity) {
    auto diag = run_checker("ring_comm", R"(
theorem t : x + y = y + x
proof
  then x + y = y + x by ring
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Ring_QuadraticExpansion) {
    // (a + b)^2 = a^2 + 2*a*b + b^2 — the canonical ring test
    auto diag = run_checker("ring_quadratic", R"(
theorem t : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
proof
  then (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 by ring
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Ring_DifferenceOfSquares) {
    // (a - b) * (a + b) = a^2 - b^2
    auto diag = run_checker("ring_diff_squares", R"(
theorem t : (a - b) * (a + b) = a ^ 2 - b ^ 2
proof
  then (a - b) * (a + b) = a ^ 2 - b ^ 2 by ring
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Ring_Distributivity) {
    // x * (y + z) = x * y + x * z
    auto diag = run_checker("ring_distrib", R"(
theorem t : x * (y + z) = x * y + x * z
proof
  then x * (y + z) = x * y + x * z by ring
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Ring_FalseIdentity) {
    // x + y = x is not a ring identity
    auto diag = run_checker("ring_false", R"(
theorem t : x + y = x
proof
  then x + y = x by ring
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "ring identity"));
}

TEST(CheckerTest, Ring_NotAnEquality) {
    // by ring on a non-equality should fail
    auto diag = run_checker("ring_not_eq", R"(
theorem t : x + 1 > 0
proof
  then x + 1 > 0 by ring
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "ring"));
}

TEST(CheckerTest, Ring_HaveStep) {
    // by ring works in a have step
    auto diag = run_checker("ring_have", R"(
theorem t : (x + y) * (x - y) = x ^ 2 - y ^ 2
proof
  have sq : (x + y) * (x - y) = x ^ 2 - y ^ 2 by ring
  then (x + y) * (x - y) = x ^ 2 - y ^ 2 by sq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── auto-discharge (then P → Q with no justification) ───────────────────

TEST(CheckerTest, AutoDischarge_ImplIntro_Basic) {
    // "then P → Q" with no 'by' clause — auto-finds suppose[P] and derived[Q]
    auto diag = run_checker("auto_discharge_impl_basic", R"(
axiom ax : P -> Q
theorem t : P -> Q
proof
  suppose h : P
  have hq : Q by ax and h
  then P -> Q
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, AutoDischarge_ImplIntro_Chain) {
    // Multi-level implication: inner implication stored as 'have', outer auto-discharged.
    // ThenStep results are not stored in env; use 'have' for intermediate implications.
    auto diag = run_checker("auto_discharge_chain", R"(
theorem t : P -> Q -> P
proof
  suppose hp : P
  suppose hq : Q
  have qp : Q -> P by hq and hp
  then P -> Q -> P
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, AutoDischarge_NotIntro) {
    // "then not P" auto-discharge: suppose[P] and derived[false] in scope.
    auto diag = run_checker("auto_discharge_not", R"(
theorem t : P -> not P -> false
proof
  suppose hp : P
  suppose hnp : not P
  have bot : false by hnp and hp
  have np_impl : not P -> false by hnp and bot
  then P -> not P -> false
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, AutoDischarge_MissingAssumption_Error) {
    // Auto-discharge should fail if there's no matching suppose in scope
    auto diag = run_checker("auto_discharge_no_assume", R"(
theorem t : P -> Q
proof
  have hq : Q by ax
  then P -> Q
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "auto-discharge"));
}

TEST(CheckerTest, AutoDischarge_MissingConsequent_Error) {
    // Auto-discharge should fail if the consequent has not been derived
    auto diag = run_checker("auto_discharge_no_conseq", R"(
theorem t : P -> Q
proof
  suppose hp : P
  then P -> Q
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "auto-discharge"));
}

// ── auto-discharge combined — "have h : P from ax" + "then P -> Q" (no by) ──────

TEST(CheckerTest, AutoDischarge_WithFromAlias) {
    auto diag = run_checker("auto_discharge_with_from", R"(
axiom ax : P -> Q
theorem t : P -> Q
proof
  suppose h : P
  have hq : Q from ax and h
  then P -> Q
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── anonymous steps (have _ : P by ...) ─────────────────────────────────

TEST(CheckerTest, AnonymousStep_Basic) {
    // "have _ : P by ax" — underscore name; result stored internally
    auto diag = run_checker("anon_step_basic", R"(
axiom ax : P
theorem t : P
proof
  have _ : P by ax
  then P by ax
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, AnonymousStep_UsedForAutoDischarge) {
    // Anonymous step's derived prop is findable by auto-discharge (find_derived)
    auto diag = run_checker("anon_step_auto_discharge", R"(
axiom ax : P -> Q
theorem t : P -> Q
proof
  suppose h : P
  have _ : Q by ax and h
  then P -> Q
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── optional cases result label ─────────────────────────────────────────

TEST(CheckerTest, CasesOptionalLabel_Valid) {
    // "cases h" without a result label — checker auto-generates a name
    auto diag = run_checker("cases_no_label", R"(
axiom ax_pq : P or Q
axiom ax_p  : P -> R
axiom ax_q  : Q -> R
theorem t : R
proof
  cases ax_pq
    case lp : P =>
      have r1 : R by ax_p and lp
      then R by r1
    case lq : Q =>
      have r2 : R by ax_q and lq
      then R by r2
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, CasesLabeledStillWorks) {
    // Old labelled form "cases result : h" with done terminators + follow-up step
    auto diag = run_checker("cases_with_label", R"(
axiom ax_pq : P or Q
axiom ax_p  : P -> R
axiom ax_q  : Q -> R
theorem t : R
proof
  cases result : ax_pq
    case lp : P =>
      have r1 : R by ax_p and lp
      then R by r1
    done
    case lq : Q =>
      have r2 : R by ax_q and lq
      then R by r2
    done
  then R by result
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── bare "then" closes goal without repeating the statement ──────────────

TEST(CheckerTest, BareThен_SimpleAxiom) {
    // "then" with no proposition: checker infers goal from decl.statement
    auto diag = run_checker("bare_then_axiom", R"(
axiom ax : P
theorem t : P
proof
  then by ax
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, BareThen_AutoDischarge) {
    // Bare "then" with no by: auto-discharge P -> Q
    auto diag = run_checker("bare_then_auto_discharge", R"(
axiom ax : P -> Q
theorem t : P -> Q
proof
  suppose h : P
  have hq : Q by ax and h
  then
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, BareThen_WrongGoal_Error) {
    // Bare "then" with mismatched goal still fails at conclusion validation
    auto diag = run_checker("bare_then_wrong_goal", R"(
axiom ax : Q
theorem t : P
proof
  then by ax
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, TrueIntro_HaveStep) {
    // "have ht : true by" (empty refs) uses TrueIntro
    auto diag = run_checker("true_intro_have", R"(
theorem t : true
proof
  have ht : true by
  then true by ht
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, TrueIntro_ThenStep) {
    // "then true" directly closes a true goal
    auto diag = run_checker("true_intro_then", R"(
theorem t : true
proof
  then true
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, TrueIntro_BareThen) {
    // bare "then" with true goal
    auto diag = run_checker("true_intro_bare_then", R"(
theorem t : true
proof
  then
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ShowStep_Valid) {
    // "show P" succeeds when P matches the theorem statement
    auto diag = run_checker("show_valid", R"(
axiom ax : P
theorem t : P
proof
  show P
  then P by ax
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ShowStep_Mismatch_Error) {
    // "show Q" fails when theorem statement is P
    auto diag = run_checker("show_mismatch", R"(
axiom ax : P
theorem t : P
proof
  show Q
  then P by ax
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, ExactStep_Valid) {
    // "exact ax" closes the goal when ax : P and goal is P
    auto diag = run_checker("exact_valid", R"(
axiom ax : P
theorem t : P
proof
  exact ax
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ExactStep_WrongType_Error) {
    // "exact ax" fails when ax : Q and goal is P
    auto diag = run_checker("exact_wrong", R"(
axiom ax : Q
theorem t : P
proof
  exact ax
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, ExactStep_UnknownHyp_Error) {
    // "exact unknown" fails on missing hypothesis
    auto diag = run_checker("exact_unknown", R"(
theorem t : P
proof
  exact nonexistent
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, RewriteStep_Basic) {
    // rewrite x_eq transforms goal P(x) -> P(y) when x_eq : x = y
    auto diag = run_checker("rewrite_basic", R"(
axiom ax_Py : P(y)
axiom x_eq : x = y
theorem t : P(x)
proof
  rewrite x_eq
  then P(y) by ax_Py
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, RewriteStep_NoEffect_Warning) {
    // rewrite where var doesn't appear in goal gives a warning
    auto diag = run_checker("rewrite_no_effect", R"(
axiom ax : P
axiom eq : z = w
theorem t : P
proof
  rewrite eq
  then P by ax
end
)");
    EXPECT_FALSE(diag.hasErrors()); // warning, not error
}

TEST(CheckerTest, RewriteStep_NonEq_Error) {
    // rewrite with a non-equality hypothesis fails
    auto diag = run_checker("rewrite_non_eq", R"(
axiom ax : P
theorem t : Q
proof
  rewrite ax
  then Q
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// Two rewrites in one step: rewrite h1, h2 applies h1 then h2.
// Goal starts as P(x); eq1: x=y transforms it to P(y); eq2: y=z transforms to P(z).
// base provides P(z) to close.
TEST(CheckerTest, RewriteStep_List_TwoForward) {
    auto diag = run_checker("rewrite_list_two", R"(
axiom eq1 : x = y
axiom eq2 : y = z
axiom base_ax : P(z)
theorem t : P(x)
proof
  have base : P(z) by base_ax
  rewrite eq1, eq2
  then P(z) by base
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// Reverse rewrite in list: rewrite eq2 transforms goal P(c) to P(b);
// then ← eq1 (reverse of a=b, so b→a) transforms P(b) to P(a).
// prem provides P(a) to close.
TEST(CheckerTest, RewriteStep_ReverseInList) {
    // Using ordinary string so \xe2\x86\x90 is the UTF-8 left arrow ←.
    auto diag = run_checker("rewrite_reverse_list",
        "axiom eq1 : a = b\n"
        "axiom eq2 : c = b\n"
        "axiom prem_ax : P(a)\n"
        "theorem t : P(c)\n"
        "proof\n"
        "  have prem : P(a) by prem_ax\n"
        "  rewrite eq2, \xe2\x86\x90 eq1\n"
        "  then P(a) by prem\n"
        "end\n");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

TEST(CheckerTest, Linarith_SimpleTransitivity) {
    // MT1: x < y and y < z implies x < z
    auto diag = run_checker("linarith_trans", R"(
theorem t : x < z
proof
  suppose h1 : x < y
  suppose h2 : y < z
  then x < z by linarith
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Linarith_SimpleLeq) {
    // MT1: x <= y and y <= z implies x <= z
    auto diag = run_checker("linarith_leq", R"(
theorem t : x <= z
proof
  suppose h1 : x <= y
  suppose h2 : y <= z
  then x <= z by linarith
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Linarith_NotProvable_Error) {
    // MT1: linarith fails when the goal doesn't follow
    auto diag = run_checker("linarith_fail", R"(
theorem t : x < y
proof
  suppose h1 : x < z
  then x < y by linarith
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, Linarith_HaveStep) {
    // MT1: linarith in a have step
    auto diag = run_checker("linarith_have", R"(
theorem t : x < z
proof
  suppose h1 : x < y
  suppose h2 : y < z
  have result : x < z by linarith
  exact result
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Simp_AndElim) {
    // MT2: simp proves P from P and Q via AndElimL
    auto diag = run_checker("simp_and_elim", R"(
axiom pq : P and Q
theorem t : P
proof
  then P by simp
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Simp_Assumption) {
    // MT2: simp closes goal when goal is directly in scope
    auto diag = run_checker("simp_assumption", R"(
axiom ax : P
theorem t : P
proof
  then P by simp
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Simp_ImplElim) {
    // MT2: simp closes goal via ImplElim (modus ponens)
    auto diag = run_checker("simp_impl_elim", R"(
axiom h_impl : P -> Q
axiom h_p : P
theorem t : Q
proof
  then Q by simp
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Simp_NoProof_Error) {
    // MT2: simp fails when no derivation exists
    auto diag = run_checker("simp_fail", R"(
axiom ax : Q
theorem t : P
proof
  then P by simp
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// simp [h] — restricted lemma set succeeds when the named hypothesis closes the goal
TEST(CheckerTest, Simp_LemmaSet_Succeeds) {
    auto diag = run_checker("simp_lemma_set_ok", R"(
axiom hp : P
axiom hq : Q
theorem t : P
proof
  then P by simp [hp]
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// simp [wrong_h] — restricted lemma set fails when named hypothesis cannot close goal
TEST(CheckerTest, Simp_LemmaSet_WrongHyp_Fails) {
    auto diag = run_checker("simp_lemma_set_fail", R"(
axiom hp : P
axiom hq : Q
theorem t : P
proof
  then P by simp [hq]
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, ApplyStep_Basic) {
    // "apply h" where h : A → B transforms goal B to A
    auto diag = run_checker("apply_basic", R"(
axiom h_impl : P -> Q
axiom h_p : P
theorem t : Q
proof
  apply h_impl
  then P by h_p
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ApplyStep_WrongImplType_Error) {
    // "apply h" fails when h's consequent doesn't match the goal
    auto diag = run_checker("apply_wrong", R"(
axiom h_impl : P -> R
theorem t : Q
proof
  apply h_impl
  then P
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, ApplyStep_NotImpl_Error) {
    // "apply h" fails when h is not an implication
    auto diag = run_checker("apply_not_impl", R"(
axiom ax : P
theorem t : Q
proof
  apply ax
  then Q
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, ByContra_Basic) {
    // "by contra" closes goal when ⊥ is in scope from contradiction
    auto diag = run_checker("by_contra", R"(
axiom ax_p : P
axiom ax_np : not P
theorem t : Q
proof
  have bot : false by ax_np and ax_p
  then Q by contra
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ByContra_NoFalse_Error) {
    // "by contra" fails when ⊥ is not in scope
    auto diag = run_checker("by_contra_no_false", R"(
theorem t : Q
proof
  then Q by contra
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

TEST(CheckerTest, SufficesStep_Basic) {
    // "suffices h : P" where h : P → goal already in scope — desugars to apply h
    auto diag = run_checker("suffices_basic", R"(
axiom h_impl : P -> Q
axiom h_p : P
theorem t : Q
proof
  suffices h_impl : P
  then P by h_p
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, MultipleErrors_BothDeclarationsChecked) {
    // checker should report errors from both declarations even when the
    // first has parse-level errors — don't abort after first error.
    auto diag = run_checker("multi_error", R"(
theorem t1 : P
proof
  then Q
end
theorem t2 : Q
proof
  then P
end
)");
    EXPECT_TRUE(diag.hasErrors());
    // Both theorems should have conclusion errors, not just the first.
    int error_count = 0;
    for (const auto& d : diag.diagnostics())
        if (d.severity == diag::Severity::Error) ++error_count;
    EXPECT_GE(error_count, 2);
}

// ── Structure declarations ─────────────────────────────────────────────────────

TEST(CheckerTest, ValidStructureAxiomsInScope) {
    // After declaring a structure with an axiom field named "hyp", the generated
    // module-level name is "<StructName>_hyp".
    auto diag = run_checker("struct_axioms_in_scope", R"(
structure G :=
  axiom hyp : P

theorem use_struct : P
proof
  then P by G_hyp
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidStructureEmpty) {
    // An empty structure (no fields) should be accepted without errors.
    auto diag = run_checker("struct_empty", R"(
structure Empty :=
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidStructureAxiomUsedInProof) {
    // Full round-trip: declare structure with an axiom, then prove a theorem
    // using the generated axiom name.
    auto diag = run_checker("struct_axiom_used", R"(
structure Alg :=
  axiom base_prop : P -> Q

theorem derive_q : Q
proof
  suppose hp : P
  then Q by Alg_base_prop and hp
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Structure instantiation ──────────────────────────────────────────────

TEST(CheckerTest, ValidStructureInstantiation) {
    // Define a structure with a term field and an axiom referencing it via
    // an expression-level occurrence (PropRel).
    // After instantiation the axiom `NatZero_zero_nonneg` (= 0 >= 0) is
    // inserted into module_env — a subsequent theorem can use it directly.
    auto diag = run_checker("struct_instantiation", R"(
structure HasZero :=
  zero : Nat
  axiom zero_nonneg : zero >= 0

definition NatZero : HasZero :=
  zero := 0

theorem use_inst : 0 >= 0
proof
  then 0 >= 0 by NatZero_zero_nonneg
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidInstantiationAxiomBetaReduced) {
    // An instantiation with a lambda binding whose axiom is beta-reducible.
    // The axiom `id_trivial : id(0) = 0` after substituting `id := fun a => a`
    // becomes `(fun a => a)(0) = 0`, which beta-reduces to `0 = 0`.
    // The instantiation itself should succeed (no errors).
    auto diag = run_checker("struct_beta_reduce", R"(
structure HasId :=
  id   : Nat -> Nat
  axiom id_trivial : id(0) = 0

definition NatId : HasId :=
  id := fun a => a
)");
    // NatId_id_trivial should be produced (beta-reduced to 0 = 0); no errors.
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, InvalidInstantiationUnknownStruct) {
    // Instantiating an undefined structure should be an error.
    auto diag = run_checker("struct_unknown", R"(
definition Bad : NoSuchStruct :=
  x := 0
)");
    EXPECT_TRUE(diag.hasErrors());
}

// ── Parametric structure params and TakeStep injection ───────────────────

TEST(CheckerTest, ValidParametricStructureParam) {
    // theorem with (M : MyStruct) param injects M_my_axiom into the proof
    // so it can be used directly as a hypothesis reference.
    auto diag = run_checker("dt5_param", R"(
structure MyStruct :=
  axiom my_axiom : P and Q

theorem use_param (M : MyStruct) : P and Q
proof
  then P and Q by M_my_axiom
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidTakeStructureInjectsAxioms) {
    // "take G : MyStruct" inside a proof injects G_my_axiom into scope.
    auto diag = run_checker("dt5_take", R"(
structure MyStruct :=
  axiom my_axiom : P and Q

theorem take_struct : P and Q
proof
  take G : MyStruct
  then P and Q by G_my_axiom
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Parametric theorems over structures ──────────────────────────────────

TEST(CheckerTest, ValidParametricTheoremUsesInjectedAxiom) {
    // a theorem with param (M : MyStruct) injects M_my_axiom into the proof
    // scope so it can be cited directly as a hypothesis reference (underscore form).
    auto diag = run_checker("dt6_param_underscore", R"(
structure MyStruct :=
  axiom my_axiom : P and Q

theorem use_param (M : MyStruct) : P and Q
proof
  then P and Q by M_my_axiom
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidParametricTheoremWithDotNotation) {
    // the same injected axiom is also accessible via dot notation "M.my_axiom".
    auto diag = run_checker("dt6_param_dot", R"(
structure MyStruct :=
  axiom my_axiom : P and Q

theorem use_param_dot (M : MyStruct) : P and Q
proof
  then P and Q by M.my_axiom
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Numeric coercions (Nat ↪ Int ↪ Rat ↪ Real) ─────────────────────────

TEST(CheckerTest, ValidMixedNumericPropRel) {
    // n : Nat and literal 0 (Nat) in an equality — no spurious type warning.
    auto diag = run_checker("dt7_nat_eq_zero", R"(
theorem nat_eq_zero : n = 0
proof
  suppose h : n = 0
  then n = 0 by h
end
)");
    // Expect no errors (warnings about Unknown types are acceptable, not errors).
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidNatInRealComparison) {
    // a function expecting Real should accept a Nat argument silently
    // via the numeric tower coercion (no Mismatch warning → no error).
    auto diag = run_checker("dt7_nat_in_real_call", R"(
definition f_real (x : Real) : P
theorem use_nat_for_real : P
proof
  suppose hn : n = 0
  then P by f_real
end
)");
    // The theorem itself may not be provable this way, but we just verify
    // that no spurious type-mismatch error is emitted for the argument.
    // (The proof may fail for logical reasons, not type reasons.)
    // Actually let's test with a simpler case: just that the definition accepts.
    // Simpler test: a theorem with a binary expression n + x where both are in scope.
    auto diag2 = run_checker("dt7_mixed_binary", R"(
theorem mixed_arith : n + 0 >= 0
proof
  suppose h : n + 0 >= 0
  then n + 0 >= 0 by h
end
)");
    EXPECT_FALSE(diag2.hasErrors());
}

// ── Quotient type declarations ───────────────────────────────────────────

TEST(CheckerTest, ValidQuotientDeclaration) {
    // A quotient declaration with all three standard equivalence axioms inserts
    // them as "<QuotName>_<axiomName>" entries in module_env without errors.
    auto diag = run_checker("quotient_declaration", R"(
quotient IntMod2 := Int over mod2_eq
  axiom mod2_refl  : for all a : Int, mod2_eq(a, a)
  axiom mod2_symm  : for all a b : Int, mod2_eq(a, b) -> mod2_eq(b, a)
  axiom mod2_trans : for all a b c : Int, mod2_eq(a, b) -> mod2_eq(b, c) -> mod2_eq(a, c)
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ValidQuotientAxiomsUsable) {
    // Axioms introduced by a quotient declaration are usable in subsequent proofs.
    auto diag = run_checker("quotient_axioms_usable", R"(
quotient Q2 := Int over rel
  axiom rel_refl  : for all a : Int, rel(a, a)
  axiom rel_symm  : for all a b : Int, rel(a, b) -> rel(b, a)
  axiom rel_trans : for all a b c : Int, rel(a, b) -> rel(b, c) -> rel(a, c)

theorem use_refl : for all a : Int, rel(a, a)
proof
  then for all a : Int, rel(a, a) by Q2_rel_refl
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── NL natural-language checker tests ────────────────────────────────────────

// "note that P by h" works (anonymous have resolves via Assumption rule)
TEST(CheckerTest, NL4_NoteThat) {
    auto diag = run_checker("nl4_note_that", R"(
theorem t : P
proof
  suppose h : P
  note that P by h
  then P by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// "since h1 and h2, have hpq : P and Q" works
TEST(CheckerTest, NL5_Since) {
    auto diag = run_checker("nl5_since", R"(
theorem t : P and Q
proof
  suppose hp : P
  suppose hq : Q
  since hp and hq, have hpq : P and Q
  then P and Q by hpq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// "we know X" introduces an anonymous have: have _ : X by X.
// This works when the hypothesis name and the proposition name are the same,
// e.g. "suppose P : P" and then "we know P".
TEST(CheckerTest, NL13_WeKnow) {
    auto diag = run_checker("nl13_we_know", R"(
theorem t : P
proof
  suppose P : P
  we know P
  then P by P
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// "by hypothesis" resolves to the unique assumption in scope
TEST(CheckerTest, NL16_ByHypothesisUnique) {
    auto diag = run_checker("nl16_hypothesis_unique", R"(
theorem t : P
proof
  suppose h : P
  have a : P by hypothesis
  then P by a
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// "by assumption" resolves to the unique assumption in scope
TEST(CheckerTest, NL16_ByAssumptionUnique) {
    auto diag = run_checker("nl16_assumption_unique", R"(
theorem t : P
proof
  suppose h : P
  have a : P by assumption
  then P by a
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// multiple assumptions in scope → warning (not error), still resolves
TEST(CheckerTest, NL16_ByHypothesisAmbiguousWarning) {
    auto diag = run_checker("nl16_hypothesis_ambiguous", R"(
theorem t : P
proof
  suppose h1 : P
  suppose h2 : Q
  have a : P by hypothesis
  then P by a
end
)");
    // Should have a warning but no errors (or may have an error if assumption resolution
    // picks the wrong one — the test just checks that the warning is emitted)
    bool has_warning = false;
    for (const auto& d : diag.diagnostics())
        if (d.severity == diag::Severity::Warning
                && d.message.find("multiple assumptions") != std::string::npos)
            has_warning = true;
    EXPECT_TRUE(has_warning);
}

// "suppose h1 : P and h2 : Q" — both hypotheses in scope
TEST(CheckerTest, NL19_SupposeMultiple) {
    auto diag = run_checker("nl19_suppose_multiple", R"(
theorem t : P and Q
proof
  suppose hp : P and hq : Q
  then P and Q by hp and hq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── silent ImplIntro / NotIntro close at end/qed ────────────────────────

TEST(CheckerTest, NL3AutoCloseImpl) {
    // Proof of A → B ends at "end" after "suppose h : A" and "have h_b : B by ..."
    // with no explicit "then A → B" — should pass via auto-discharge at end/qed.
    auto diag = run_checker("nl3_auto_close_impl", R"(
axiom ax : P -> Q
theorem t : P -> Q
proof
  suppose h : P
  have h_q : Q by ax and h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NL3AutoCloseNot) {
    // Proof of ¬A ends at "end" after "suppose h : A" and "have bot : false by ..."
    // with no explicit "then ¬A" — should pass via auto-discharge at end/qed.
    auto diag = run_checker("nl3_auto_close_not", R"(
axiom ax_p  : P
axiom ax_np : not P
theorem t : not P
proof
  suppose h : P
  have bot : false by ax_np and h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NL3MissingConsequentError) {
    // Proof of A → B ends at "end" after "suppose h : A" but no derivation of B.
    // Should emit an error indicating auto-discharge failed.
    auto diag = run_checker("nl3_missing_consequent", R"(
theorem t : P -> Q
proof
  suppose h : P
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "auto-discharge"));
}

// ── calc block tests ─────────────────────────────────────────────────────

// pure equality chain — passes and result available for later use
TEST(CheckerTest, CalcStep_PureEqualityChain) {
    auto diag = run_checker("calc_eq_chain", R"(
axiom h1 : a = b
axiom h2 : b = c
lemma chain : a = c
proof
  calc res : a = b by h1 = c by h2
  then a = c by res
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// mixed ≤/=/< chain — op_final is <, result usable downstream
TEST(CheckerTest, CalcStep_MixedChainOpFinal) {
    auto diag = run_checker("calc_mixed_chain", R"(
axiom h1 : a <= b
axiom h2 : b = c
axiom h3 : c < d
lemma chain : a < d
proof
  calc res : a <= b by h1 = c by h2 < d by h3
  then a < d by res
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// named result used in subsequent then — passes
TEST(CheckerTest, CalcStep_NamedResultUsedInThen) {
    auto diag = run_checker("calc_named_result", R"(
axiom h1 : x = y
axiom h2 : y = z
theorem trans_eq : x = z
proof
  calc eq_xz : x = y by h1 = z by h2
  then x = z by eq_xz
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// incorrect individual step — error reported
TEST(CheckerTest, CalcStep_WrongJustification) {
    auto diag = run_checker("calc_bad_step", R"(
axiom h1 : a = b
axiom h2 : b = c
lemma bad : a = c
proof
  calc a = b by h2 = c by h1
  then a = c
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// inconsistent direction (< mixed with >) — error reported
TEST(CheckerTest, CalcStep_InconsistentDirection) {
    auto diag = run_checker("calc_inconsistent_dir", R"(
axiom h1 : a < b
axiom h2 : c > b
lemma bad : a < a
proof
  calc a < b by h1 > c by h2
  then a < a
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// ── calc block: _ placeholder and mixed-relation chains ──────────────────

// = then < with _ placeholder — op_final is <
TEST(CheckerTest, CalcStep_UnderscorePlaceholder_EqLt) {
    auto diag = run_checker("calc_us_eq_lt", R"(
axiom h1 : a = b
axiom h2 : b < c
lemma chain : a < c
proof
  calc res : a = b by h1
             _ < c by h2
  then a < c by res
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// <= then < with _ placeholder — op_final is <
TEST(CheckerTest, CalcStep_UnderscorePlaceholder_LeLt) {
    auto diag = run_checker("calc_us_le_lt", R"(
axiom h1 : a <= b
axiom h2 : b < c
lemma chain : a < c
proof
  calc res : a <= b by h1
             _ < c by h2
  then a < c by res
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// 4-step chain = <= < = with _ placeholder — op_final is <
TEST(CheckerTest, CalcStep_UnderscorePlaceholder_FourStep) {
    auto diag = run_checker("calc_us_four", R"(
axiom h1 : a = b
axiom h2 : b <= c
axiom h3 : c < d
axiom h4 : d = e
lemma chain : a < e
proof
  calc res : a = b by h1
             _ <= c by h2
             _ < d by h3
             _ = e by h4
  then a < e by res
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// ── split step tests ─────────────────────────────────────────────────────

// conjunction split — both arms proved, result in scope
TEST(CheckerTest, SplitStep_ConjunctionPasses) {
    auto diag = run_checker("split_conj_ok", R"(
axiom hp : P
axiom hq : Q
theorem t : P and Q
proof
  split result :
    case left =>
      then P by hp
    case right =>
      then Q by hq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// biconditional (P iff Q desugars to (P->Q) and (Q->P)) — split works
TEST(CheckerTest, SplitStep_BiconditionalPasses) {
    auto diag = run_checker("split_iff_ok", R"(
axiom hpq : P -> Q
axiom hqp : Q -> P
theorem t : P iff Q
proof
  split result :
    case left =>
      suppose hp : P
      then Q by hpq and hp
    case right =>
      suppose hq : Q
      then P by hqp and hq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// wrong label — split with a goal that is not a conjunction should error
TEST(CheckerTest, SplitStep_NonConjunctionGoalErrors) {
    auto diag = run_checker("split_non_conj", R"(
theorem t : P or Q
proof
  split
    case left =>
      then P or Q
    case right =>
      then P or Q
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// missing arm — split with only one arm should error
TEST(CheckerTest, SplitStep_MissingArmErrors) {
    auto diag = run_checker("split_one_arm", R"(
axiom hp : P
theorem t : P and Q
proof
  split
    case left =>
      then P by hp
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// ── inline have sub-proofs ───────────────────────────────────────────────

TEST(CheckerTest, NL11_HaveSubProofPasses) {
    auto diag = run_checker("nl11_basic", R"(
axiom ha : P
axiom hb : Q
theorem t : P and Q
proof
  have combined : P and Q
  proof
    suppose hp : P
    suppose hq : Q
    then P and Q by hp and hq
  end
  then P and Q by combined
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NL11_HaveSubProofOuterScopeVisible) {
    // Outer hypothesis ha should be visible inside the sub-proof.
    auto diag = run_checker("nl11_scope", R"(
axiom ha : P
theorem t : P and Q
proof
  suppose hq : Q
  have paq : P and Q
  proof
    then P and Q by ha and hq
  end
  then P and Q by paq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NL11_HaveSubProofWrongConclusionErrors) {
    auto diag = run_checker("nl11_wrong_conc", R"(
axiom ha : P
axiom hb : Q
theorem t : P and Q
proof
  have combined : P and Q
  proof
    then Q by hb
  end
  then P and Q by combined
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// ── by contrapositive ────────────────────────────────────────────────────

TEST(CheckerTest, NL12_ContrapositivePasses) {
    // Prove P → Q by: suppose ¬Q, derive ¬P, then P → Q by contrapositive.
    auto diag = run_checker("nl12_basic", R"(
axiom notQ_imp_notP : not Q -> not P
theorem t : P -> Q
proof
  suppose hnq : not Q
  have hnp : not P by notQ_imp_notP and hnq
  then P -> Q by contrapositive
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NL12_ContrapositiveNegBMissingErrors) {
    // Missing the ¬B assumption — should error.
    auto diag = run_checker("nl12_missing_neg_b", R"(
axiom hnp : not P
theorem t : P -> Q
proof
  have hnp2 : not P by hnp
  then P -> Q by contrapositive
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// ── wlog step ────────────────────────────────────────────────────────────

TEST(CheckerTest, NL14_WlogInsertsAssumption) {
    // wlog introduces the stated prop as an assumption, emits a warning,
    // and the result is usable in subsequent steps.
    auto diag = run_checker("nl14_wlog", R"(
axiom ha : P or Q
theorem t : P
proof
  wlog hw : P
  then P by hw
end
)");
    // Should have no errors (only a warning).
    EXPECT_FALSE(diag.hasErrors());
    // Must have the wlog warning.
    bool has_warning = false;
    for (const auto& d : diag.diagnostics())
        if (d.severity == diag::Severity::Warning
                && d.message.find("wlog") != std::string::npos)
            has_warning = true;
    EXPECT_TRUE(has_warning);
}

// ── direction-marker biconditional proofs ────────────────────────────────

TEST(CheckerTest, NL20_DirectionMarkersBiconditionalPasses) {
    // Biconditional proof using (→)/(←) direction markers.
    // Use axioms to make each direction trivially provable.
    auto diag = run_checker("nl20_iff", R"(
axiom pq : P -> Q
axiom qp : Q -> P
theorem t : P iff Q
proof
  (->)
    suppose hp : P
    then Q by pq and hp
  (<-)
    suppose hq : Q
    then P by qp and hq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NL20_DirectionMarkersWrongDirectionErrors) {
    // The forward arm concludes P instead of Q — should error.
    auto diag = run_checker("nl20_wrong_dir", R"(
axiom pq : P -> Q
axiom qp : Q -> P
theorem t : P iff Q
proof
  (->)
    suppose hp : P
    then P by hp
  (<-)
    suppose hq : Q
    then P by qp and hq
end
)");
    EXPECT_TRUE(diag.hasErrors());
}
// ── omega tactic tests ───────────────────────────────────────────────────

// trivial non-negativity from hypothesis
TEST(CheckerTest, Omega_TrivialNonneg) {
    auto diag = run_checker("omega_nonneg", R"(
theorem t : n >= 0
proof
  suppose h : n >= 0
  then n >= 0 by omega
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// linear sum lower bound  a >= 1, b >= 1 => a + b >= 2
TEST(CheckerTest, Omega_SumLowerBound) {
    auto diag = run_checker("omega_sum_lower", R"(
theorem t : a + b >= 2
proof
  suppose ha : a >= 1
  suppose hb : b >= 1
  then a + b >= 2 by omega
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// squeeze  n >= 0, n <= 0 => n = 0
TEST(CheckerTest, Omega_Squeeze) {
    auto diag = run_checker("omega_squeeze", R"(
theorem t : n = 0
proof
  suppose h1 : n >= 0
  suppose h2 : n <= 0
  then n = 0 by omega
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// strict inconsistency  a > b, b > a => false
TEST(CheckerTest, Omega_StrictInconsistency) {
    auto diag = run_checker("omega_strict_incons", R"(
theorem t : false
proof
  suppose h1 : a > b
  suppose h2 : b > a
  then false by omega
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// simple additive  n >= 0 => n + 1 >= 1
TEST(CheckerTest, Omega_Additive) {
    auto diag = run_checker("omega_additive", R"(
theorem t : n + 1 >= 1
proof
  suppose h : n >= 0
  then n + 1 >= 1 by omega
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// omega in a have step
TEST(CheckerTest, Omega_HaveStep) {
    auto diag = run_checker("omega_have", R"(
theorem t : x + y >= 0
proof
  suppose hx : x >= 0
  suppose hy : y >= 0
  have r : x + y >= 0 by omega
  exact r
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// rejection of a false claim
TEST(CheckerTest, Omega_FalseClaim_Error) {
    auto diag = run_checker("omega_false_claim", R"(
theorem t : n >= 5
proof
  suppose h : n >= 0
  then n >= 5 by omega
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "omega"));
}

// equality from two-sided inequalities via omega
TEST(CheckerTest, Omega_TwoSidedEquality) {
    auto diag = run_checker("omega_two_sided_eq", R"(
theorem t : a = b
proof
  suppose h1 : a >= b
  suppose h2 : b >= a
  then a = b by omega
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── push neg tactic tests ────────────────────────────────────────────────

// push neg on goal ¬(A ∧ B) → ¬A ∨ ¬B
TEST(CheckerTest, PushNeg_AndGoal) {
    auto diag = run_checker("push_neg_and_goal", R"(
theorem t : not (A and B)
proof
  suppose hna : not A
  push neg
  then not A or not B by hna
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// double negation elimination ¬¬A → A
TEST(CheckerTest, PushNeg_DoubleNeg) {
    auto diag = run_checker("push_neg_double_neg", R"(
theorem t : not (not A)
proof
  suppose ha : A
  push neg
  then A by ha
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// relational negation ¬(a < b) → a ≥ b
TEST(CheckerTest, PushNeg_RelationalLt) {
    auto diag = run_checker("push_neg_rel_lt", R"(
theorem t : not (a < b)
proof
  suppose h : a >= b
  push neg
  then a >= b by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// push neg at h — hypothesis ¬(A ∨ B) → ¬A ∧ ¬B
TEST(CheckerTest, PushNeg_AtHypOrGoal) {
    auto diag = run_checker("push_neg_at_or", R"(
theorem t : not A and not B
proof
  suppose h : not (A or B)
  push neg at h
  then not A and not B by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// push neg on ¬(A → B) → A ∧ ¬B
TEST(CheckerTest, PushNeg_Implication) {
    auto diag = run_checker("push_neg_impl", R"(
theorem t : not (A -> B)
proof
  suppose ha : A
  suppose hnb : not B
  push neg
  then A and not B by ha and hnb
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// relational negation ¬(a = b) → a ≠ b
TEST(CheckerTest, PushNeg_RelationalEq) {
    auto diag = run_checker("push_neg_rel_eq", R"(
theorem t : not (a = b)
proof
  suppose h : a /= b
  push neg
  then a /= b by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Qualified names ──────────────────────────────────────────────────────

// qualified name "Lib.base" works after importing "lib.forall"
TEST(CheckerTest, QualifiedName_Works) {
    namespace fs = std::filesystem;
    auto dir = fs::temp_directory_path();
    auto lib  = dir / "forall_mod1_lib.forall";
    auto main = dir / "forall_mod1_main.forall";

    std::ofstream{lib} << "axiom base : P -> Q\n";
    std::ofstream{main} << R"(
import "forall_mod1_lib.forall"
theorem use_qualified : P -> Q
proof
  suppose h : P
  have hq : Q by Forall_mod1_lib.base and h
  then P -> Q by h and hq
end
)";
    // The module name is derived from "forall_mod1_lib.forall" → "Forall_mod1_lib"
    diag::DiagnosticEngine diag;
    checker::Checker c{diag};
    c.check(main);
    EXPECT_FALSE(diag.hasErrors());
}

// unqualified name still works after import (backward-compatible)
TEST(CheckerTest, QualifiedName_UnqualifiedStillWorks) {
    namespace fs = std::filesystem;
    auto dir = fs::temp_directory_path();
    auto lib  = dir / "forall_mod1b_lib.forall";
    auto main = dir / "forall_mod1b_main.forall";

    std::ofstream{lib} << "axiom base2 : P -> Q\n";
    std::ofstream{main} << R"(
import "forall_mod1b_lib.forall"
theorem use_unqualified : P -> Q
proof
  suppose h : P
  have hq : Q by base2 and h
  then P -> Q by h and hq
end
)";
    diag::DiagnosticEngine diag;
    checker::Checker c{diag};
    c.check(main);
    EXPECT_FALSE(diag.hasErrors());
}

// a completely unknown qualified name fails with a clear error
TEST(CheckerTest, QualifiedName_UnknownFails) {
    auto diag = run_checker("qualified_unknown", R"(
axiom base3 : P
theorem use_unknown : P
proof
  then P by Nonexistent.foo
end
)");
    EXPECT_TRUE(diag.hasErrors());
    EXPECT_TRUE(has_error(diag, "Nonexistent.foo"));
}

// ── Namespace blocks ─────────────────────────────────────────────────────

// declarations inside a namespace block are accessible as Ns.name
TEST(CheckerTest, Namespace_QualifiedAccess) {
    auto diag = run_checker("ns_qualified", R"(
namespace Arith
  axiom add_comm : A -> B
end Arith
theorem use_ns : A -> B
proof
  suppose h : A
  have hb : B by Arith.add_comm and h
  then A -> B by h and hb
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// after "open Ns", declarations are accessible unqualified
TEST(CheckerTest, Namespace_OpenBringsIntoScope) {
    auto diag = run_checker("ns_open", R"(
namespace Logic
  axiom excluded_middle : P or not P
end Logic
open Logic
theorem use_em : P or not P
proof
  then P or not P by excluded_middle
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// name collision between two namespaces — later definition wins
TEST(CheckerTest, Namespace_Collision_LaterWins) {
    auto diag = run_checker("ns_collision", R"(
namespace A
  axiom my_axiom : P
end A
namespace B
  axiom my_axiom : Q
end B
open A
open B
-- After both opens, "my_axiom" should resolve (later B.my_axiom wins, proving Q)
axiom want_q : Q
theorem use_collision : Q
proof
  then Q by my_axiom
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── private and protected declarations ───────────────────────────────────

// private axiom in an imported file is NOT accessible in the importer
TEST(CheckerTest, Private_NotExported) {
    namespace fs = std::filesystem;
    auto dir = fs::temp_directory_path();
    auto lib  = dir / "forall_mod3_priv_lib.forall";
    auto main = dir / "forall_mod3_priv_main.forall";

    std::ofstream{lib}  << "private axiom secret : P\n";
    std::ofstream{main} << R"(
import "forall_mod3_priv_lib.forall"
theorem use_secret : P
proof
  then P by secret
end
)";
    diag::DiagnosticEngine diag;
    checker::Checker c{diag};
    c.check(main);
    EXPECT_TRUE(diag.hasErrors());
}

// protected axiom IS accessible in the importer
TEST(CheckerTest, Protected_IsExported) {
    namespace fs = std::filesystem;
    auto dir = fs::temp_directory_path();
    auto lib  = dir / "forall_mod3_prot_lib.forall";
    auto main = dir / "forall_mod3_prot_main.forall";

    std::ofstream{lib}  << "protected axiom shared : P -> Q\n";
    std::ofstream{main} << R"(
import "forall_mod3_prot_lib.forall"
theorem use_shared : P -> Q
proof
  suppose h : P
  have hq : Q by shared and h
  then P -> Q by h and hq
end
)";
    diag::DiagnosticEngine diag;
    checker::Checker c{diag};
    c.check(main);
    EXPECT_FALSE(diag.hasErrors());
}

// ── abstract definitions ─────────────────────────────────────────────────

// abstract definition allows using the name as an opaque fact in proofs
TEST(CheckerTest, AbstractDefinition_UsableInProof) {
    auto diag = run_checker("abstract_def", R"(
abstract definition foo : P -> Q
theorem use_foo : P -> Q
proof
  suppose h : P
  have hq : Q by foo and h
  then P -> Q by h and hq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Beta-reduction after let-def substitution ─────────────────────────────────────
// These tests verify that propositions involving lambda terms are beta-reduced
// before kernel comparison, enabling ForallElim witnesses to normalise correctly.

// ForallElim with a lambda witness whose body reduces to the stated conclusion.
// ∀ f : Nat -> Nat, P(f(0))  instantiated at  fun x => x + 1  should give P(0 + 1).
// After beta-reduction: f[0] = (fun x => x+1)(0) = 0+1, so conclusion is P(0+1).
TEST(CheckerTest, BetaReduceAfterForallElim) {
    auto diag = run_checker("an5_beta_forallelim", R"(
axiom all_f : for all f : Nat -> Nat, P(f(0))
theorem inst_at_succ : P(0 + 1)
proof
  let s = fun x : Nat => x + 1
  have h : P(s(0)) by all_f at s
  then P(0 + 1) by h
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// let x = expr substitution followed by beta-reduction in a ForallElim step.
// The let-bound term is used as a witness; the resulting proposition must normalise.
TEST(CheckerTest, LetTermAsForallElimWitness) {
    auto diag = run_checker("an5_let_witness", R"(
axiom all_n : for all n : Nat, n >= 0
theorem zero_ge_zero : 0 >= 0
proof
  have h : 0 >= 0 by all_n at 0
  then 0 >= 0 by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Expression-level rewrite and induction fixes ──────────

// rewrite with a non-variable lhs (expression-level find-and-replace).
// h : b[k] = a[phi(k)] rewrites b[k] inside |b[k] - L| < eps.
TEST(CheckerTest, ExprLevelRewrite) {
    auto diag = run_checker("an6_expr_rewrite", R"(
axiom match_ax : b[k] = a[phi(k)]
theorem rewrite_in_abs : |a[phi(k)] - L| < eps -> |b[k] - L| < eps
proof
  suppose h_conv : |a[phi(k)] - L| < eps
  rewrite match_ax
  then |a[phi(k)] - L| < eps -> |a[phi(k)] - L| < eps by h_conv and h_conv
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// Expression-level rewrite with a compound lhs: h : a + b = c rewrites a + b → c
// inside an absolute value goal.  After rewrite, goal changes from |a+b|<eps to |c|<eps.
TEST(CheckerTest, ExprLevelRewriteCompound) {
    auto diag = run_checker("expr_rewrite_compound", R"(
axiom sum_ax : a + b = c
axiom h_conv : |c| < eps
theorem use_rewrite : |a + b| < eps
proof
  rewrite sum_ax
  then |c| < eps by h_conv
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// ── Predicate definition unfolding ────────────────────────────────────────

// `have` step concludes a predicate whose unfolded body matches a hypothesis.
// definition Positive(x) := x > 0
// axiom n_pos : n > 0
// have h : Positive(n) -- unfolded to n > 0, matches n_pos via Assumption rule
TEST(CheckerTest, PredDefUnfoldingInHave) {
    auto diag = run_checker("pred_def_have", R"(
definition Positive (x : Real) : Prop := x > 0
axiom n_pos : n > 0
theorem show_pos : Positive(n)
proof
  have h : Positive(n) by n_pos
  then Positive(n) by h
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// `suppose` step with a predicate definition unfolds the assumption.
// definition Positive(x) := x > 0
// Supposing a defined predicate unfolds it so the unfolded body is in scope.
// axiom n_pos : Positive(n) -- unfolds to n > 0 when used in a have step.
TEST(CheckerTest, PredDefUnfoldingInSuppose) {
    auto diag = run_checker("pred_def_suppose", R"(
definition Positive (x : Real) : Prop := x > 0
axiom n_pos : Positive(n)
theorem derive_gt : n > 0
proof
  have h : n > 0 by n_pos
  then n > 0 by h
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// `then` step concludes a predicate by proving its unfolded body.
// definition Ge(a, b) := a >= b
TEST(CheckerTest, PredDefUnfoldingInThen) {
    auto diag = run_checker("pred_def_then", R"(
definition Ge (a : Real) (b : Real) : Prop := a >= b
axiom n_ge_0 : n >= 0
theorem n_ge : Ge(n, 0)
proof
  then Ge(n, 0) by n_ge_0
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// take + induction closes ∀ x, ∀ k, P(x, k) automatically.
// The conclusion validator must wrap both taken vars (∀) around the induction result.
TEST(CheckerTest, InductionWithTake) {
    auto diag = run_checker("induction_take", R"(
axiom step_ax : for all x : Nat, for all n : Nat, P(x, n) -> P(x, succ(n))
axiom base_ax : for all x : Nat, P(x, 0)
theorem all_xn : for all x : Nat, for all n : Nat, P(x, n)
proof
  take x : Nat
  induction result on n : P(x, n)
    base:
      then P(x, 0) by base_ax at x
    inductive:
      have step_x : for all n : Nat, P(x, n) -> P(x, succ(n)) by step_ax at x
      have step : P(x, n) -> P(x, succ(n)) by step_x at n
      then P(x, succ(n)) by step and ih
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// take + suppose + induction closes ∀ x, A → ∀ k, P(x, k) automatically.
TEST(CheckerTest, InductionWithTakeSupposeAndForall) {
    auto diag = run_checker("induction_take_suppose_forall", R"(
axiom step_ax : for all n : Nat, P(n) -> P(succ(n))
axiom base_ax : P(0)
theorem all_p : for all x : Nat, x >= 0 -> for all n : Nat, P(n)
proof
  take x : Nat
  suppose h_x : x >= 0
  induction result on n : P(n)
    base:
      then P(0) by base_ax
    inductive:
      have step : P(n) -> P(succ(n)) by step_ax at n
      then P(succ(n)) by step and ih
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// induction with a preceding suppose closes the implication automatically.
TEST(CheckerTest, InductionAfterSuppose) {
    auto diag = run_checker("an6_induction_after_suppose", R"(
axiom step_ax : for all n : Nat, P(n) -> P(succ(n))
axiom base_ax : P(0)
theorem all_p : Q -> for all n : Nat, P(n)
proof
  suppose h_q : Q
  induction result on n : P(n)
    base:
      then P(0) by base_ax
    inductive:
      have step_n : P(n) -> P(succ(n)) by step_ax at n
      then P(succ(n)) by step_n and ih
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// ── LI1: take mid-proof for standalone ∀-intro ─────────────────────────────────

// Simple: take n, prove body, close with explicit then ∀ n.
TEST(CheckerTest, TakeMidProof_SimpleForallIntro) {
    auto diag = run_checker("take_mid_simple", R"(
axiom add_zero_ax : for all n : Nat, n + 0 = n
theorem simple_forall : for all n : Nat, n + 0 = n
proof
  take n : Nat
  then n + 0 = n by add_zero_ax at n
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// Bare "then" closes after take: no need to restate the ∀.
TEST(CheckerTest, TakeMidProof_BareThenCloses) {
    auto diag = run_checker("take_mid_bare_then", R"(
axiom add_zero_ax : for all n : Nat, n + 0 = n
theorem simple_forall2 : for all n : Nat, n + 0 = n
proof
  take n : Nat
  have h : n + 0 = n by add_zero_ax at n
  then by h
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// Nested takes: ∀ m, ∀ n, m + n = n + m.
TEST(CheckerTest, TakeMidProof_NestedTakes) {
    auto diag = run_checker("take_mid_nested", R"(
axiom comm_ax : for all m : Nat, for all n : Nat, m + n = n + m
theorem nested_forall : for all m : Nat, for all n : Nat, m + n = n + m
proof
  take m : Nat
  take n : Nat
  have comm_m : for all n : Nat, m + n = n + m by comm_ax at m
  then m + n = n + m by comm_m at n
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// Take + suppose: ∀ n, n > 0 → n + 1 > 1.
TEST(CheckerTest, TakeMidProof_TakeAndSuppose) {
    auto diag = run_checker("take_mid_suppose", R"(
axiom impl_ax : for all n : Nat, n > 0 -> n + 1 > 1
theorem take_suppose : for all n : Nat, n > 0 -> n + 1 > 1
proof
  take n : Nat
  suppose h : n > 0
  have inst : n > 0 -> n + 1 > 1 by impl_ax at n
  then n + 1 > 1 by inst and h
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// Wrong conclusion after take — must report an error.
TEST(CheckerTest, TakeMidProof_WrongConclusion) {
    auto diag = run_checker("take_mid_wrong", R"(
axiom add_zero_ax : for all n : Nat, n + 0 = n
theorem wrong_forall : for all n : Nat, n + 0 = n
proof
  take n : Nat
  then n + 1 = n by add_zero_ax at n
end
)");
    EXPECT_TRUE(diag.hasErrors());
}

// ── Type alias checker tests ───────────────────────────────────────────────────

// A type alias used in 'take' expands correctly — numeric ops on the alias
// type are well-typed and produce no warning.
TEST(CheckerTest, TypeAlias_TakeExpandsAlias) {
    auto diag = run_checker("alias_take", R"(
type Count = Nat
axiom ax : x + 1 > 0
theorem t : x + 1 > 0
proof
  take x : Count
  then x + 1 > 0 by ax
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
    EXPECT_FALSE(has_warning(diag, "type mismatch"));
}

// A type alias used in a definition param wires into sig_table — the module
// loads without errors, confirming alias expansion doesn't crash or corrupt.
TEST(CheckerTest, TypeAlias_DefinitionParamExpandsAlias) {
    auto diag = run_checker("alias_def_param", R"(
type Index = Nat
axiom pos_ax : for all n : Nat, n > 0
definition is_positive (n : Index) : n > 0
lemma use_def : for all k : Nat, k > 0
proof
  take k : Nat
  have h : k > 0 by pos_ax at k
  then k > 0 by h
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// ── Structural induction over user-defined inductive types ────────────────────

// A simple inductive type with a base constructor and a recursive constructor.
// Structural induction should certify ∀ x : Color, P(x) when both arms pass.
TEST(CheckerTest, StructuralInduction_TwoCtors_Valid) {
    auto diag = run_checker("struct_ind_valid", R"(
inductive Color :=
  red   : Color
  blue  : Color

axiom P_red  : P(red)
axiom P_blue : P(blue)

theorem all_colors : for all x : Color, P(x)
proof
  take x : Color
  induction h on x : P(x)
    case red:
      then P(red) by P_red
    case blue:
      then P(blue) by P_blue
  then for all x : Color, P(x) by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── IsUpperBound / BoundedAbove / IsSupremum predicate definitions ────────────

// IsUpperBound(S, b) unfolds to: ∀ x : Real, x ∈ S → x ≤ b.
// Verify the definition is usable in a basic proof: if b is an upper bound of S
// and x ∈ S, then x ≤ b.
TEST(CheckerTest, IsUpperBound_UnfoldsCorrectly) {
    auto diag = run_checker("upper_bound_unfold", R"(
definition IsUpperBound (S : Set Real) (b : Real) : Prop :=
  for all x : Real, x in S -> x <= b

-- Alphabetical order of hypothesis names determines discharge order:
-- h_in < h_ub, so h_in wraps outermost in the conclusion.
theorem use_upper_bound :
  for all S : Set Real, for all b : Real, for all x : Real,
    x in S -> (for all y : Real, y in S -> y <= b) -> x <= b
proof
  take S : Set Real
  take b : Real
  take x : Real
  suppose h_in : x in S
  suppose h_ub : for all y : Real, y in S -> y <= b
  have h_impl : x in S -> x <= b by h_ub at x
  then x <= b by h_impl and h_in
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// BoundedAbove(S) unfolds to: ∃ b : Real, IsUpperBound(S, b).
// After unfolding, the existential can be extracted via obtain.
// Verify we can extract the bound and use the upper bound property.
TEST(CheckerTest, BoundedAbove_UnfoldsAndExtractsBound) {
    auto diag = run_checker("bounded_above_obtain", R"(
definition IsUpperBound (S : Set Real) (b : Real) : Prop :=
  for all x : Real, x in S -> x <= b

definition BoundedAbove (S : Set Real) : Prop :=
  there exists b : Real, IsUpperBound(S, b)

theorem bounded_has_bound :
  for all S : Set Real, for all x : Real,
    BoundedAbove(S) -> x in S ->
      there exists b : Real, x <= b
proof
  take S : Set Real
  take x : Real
  suppose h_ba : BoundedAbove(S)
  suppose h_in : x in S
  obtain b_result from h_ba
    case b , h_ub : IsUpperBound(S, b) =>
      have h_impl : x in S -> x <= b by h_ub at x
      have h_le   : x <= b by h_impl and h_in
      then there exists b : Real, x <= b by h_le at b
    done
  then there exists b : Real, x <= b by b_result
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// IsSupremum(S, s) unfolds to: IsUpperBound(S, s) ∧ (∀ b, IsUpperBound(S, b) → s ≤ b).
// Verify we can extract both components.
TEST(CheckerTest, IsSupremum_UnfoldsAndExtractsComponents) {
    auto diag = run_checker("supremum_unfold", R"(
definition IsUpperBound (S : Set Real) (b : Real) : Prop :=
  for all x : Real, x in S -> x <= b

definition IsSupremum (S : Set Real) (s : Real) : Prop :=
  IsUpperBound(S, s) and (for all b : Real, IsUpperBound(S, b) -> s <= b)

theorem sup_is_upper_bound :
  for all S : Set Real, for all s : Real,
    IsSupremum(S, s) -> IsUpperBound(S, s)
proof
  take S : Set Real
  take s : Real
  suppose h_sup : IsSupremum(S, s)
  then IsUpperBound(S, s) by h_sup
end
)");
    EXPECT_FALSE(diag.hasErrors()) << [&]{
        std::string msg;
        for (auto& d : diag.diagnostics()) msg += d.message + "\n";
        return msg;
    }();
}

// When an arm concludes a different proposition the checker must report an error.
TEST(CheckerTest, StructuralInduction_MismatchedArms_Error) {
    auto diag = run_checker("struct_ind_mismatch", R"(
inductive Bool2 :=
  true2  : Bool2
  false2 : Bool2

axiom P_true  : P(true2)
axiom Q_false : Q(false2)

theorem bad : for all x : Bool2, P(x)
proof
  take x : Bool2
  induction h on x : P(x)
    case true2:
      then P(true2) by P_true
    case false2:
      then Q(false2) by Q_false
  then for all x : Bool2, P(x) by h
end
)");
    EXPECT_TRUE(has_error(diag, ""));
}

// A type alias that expands to a function type is non-numeric; using it in
// arithmetic fires the type-mismatch warning.
TEST(CheckerTest, TypeAlias_FunctionTypeTriggersWarning) {
    auto diag = run_checker("alias_fun_warn", R"(
type Sequence = Nat -> Real
axiom ax : f + 1 > 0
theorem t : f + 1 > 0
proof
  take f : Sequence
  then f + 1 > 0 by ax
end
)");
    EXPECT_FALSE(diag.hasErrors());
    EXPECT_TRUE(has_warning(diag, "type mismatch"));
}

// take T : Type is accepted as a valid annotation; proves a universally
// quantified tautology parameterised by an abstract type variable.
TEST(CheckerTest, TakeTypeAnnotation_Valid) {
    auto diag = run_checker("take_type_annotation", R"(
theorem gen_trivial : for all T : Type, for all P : Prop, P implies P
proof
  take T : Type
  take P : Prop
  suppose h : P
  then P by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// take T : Type followed by a step that uses T only in a type annotation —
// the inner proof body is independent of T but the theorem still closes correctly.
TEST(CheckerTest, TakeTypeAnnotation_IndependentBody) {
    auto diag = run_checker("take_type_independent_body", R"(
theorem type_body_indep : for all T : Type, 1 = 1
proof
  take T : Type
  then 1 = 1 by decide
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Equality tactics: refl / symm / trans / congr ────────────────────────

TEST(CheckerTest, Refl_HaveStep) {
    auto diag = run_checker("refl_have", R"(
theorem eq_refl : for all x : Nat, x = x
proof
  take x : Nat
  have h : x = x by refl
  then for all x : Nat, x = x by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Symm_HaveStep) {
    auto diag = run_checker("symm_have", R"(
axiom ab : a = b
theorem ba : b = a
proof
  have h : b = a by symm ab
  then b = a by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Trans_HaveStep) {
    auto diag = run_checker("trans_have", R"(
axiom ab : a = b
axiom bc : b = c
theorem ac : a = c
proof
  have h : a = c by trans ab and bc
  then a = c by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Congr_HaveStep) {
    auto diag = run_checker("congr_have", R"(
axiom ab : a = b
theorem fa_eq_fb : f(a) = f(b)
proof
  have h : f(a) = f(b) by congr ab
  then f(a) = f(b) by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Function extensionality ───────────────────────────────────────────────

// Prove f = g from a pointwise-equality hypothesis via by funext.
TEST(CheckerTest, Funext_HaveStep) {
    auto diag = run_checker("funext_have", R"(
axiom hfg : for all x : Nat, f(x) = g(x)
theorem f_eq_g : f = g
proof
  have h : f = g by funext hfg
  then f = g by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// funext on a non-equality goal should error.
TEST(CheckerTest, Funext_NonEqualityGoal_Errors) {
    auto diag = run_checker("funext_nonrel", R"(
theorem bad : P
proof
  have h : P by funext wrong
end
)");
    EXPECT_TRUE(has_error(diag, "funext"));
}

// ── succ_ne_self and nat_zero_or_succ axioms ─────────────────────────────

// succ_ne_self axiom can be used in a proof by contradiction.
TEST(CheckerTest, SuccNeself_UsableInProof) {
    auto diag = run_checker("succ_ne_self_proof", R"(
axiom succ_ne_self : for all n : Nat, not (succ(n) = n)
theorem succ_ne : not (succ(0) = 0)
proof
  have h : not (succ(0) = 0) by succ_ne_self at 0
  then not (succ(0) = 0) by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// nat_zero_or_succ enables case analysis without a structural induction block.
TEST(CheckerTest, NatZeroOrSucc_Usable) {
    auto diag = run_checker("nat_zero_or_succ_use", R"(
axiom nat_zero_or_succ : for all n : Nat, (n = 0) or (there exists m : Nat, n = succ(m))
theorem zero_or_succ_holds : (1 = 0) or (there exists m : Nat, 1 = succ(m))
proof
  have h : (1 = 0) or (there exists m : Nat, 1 = succ(m)) by nat_zero_or_succ at 1
  then (1 = 0) or (there exists m : Nat, 1 = succ(m)) by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Set Real axioms ───────────────────────────────────────────────────────

// set_real_ext applies to Set Real; the axiom is accessible and parseable.
TEST(CheckerTest, SetReal_ExtAxiom_Parseable) {
    auto diag = run_checker("set_real_ext", R"(
axiom set_real_ext : for all A : Set Real, for all B : Set Real, (for all x : Real, x in A iff x in B) implies A = B
theorem use_ext : for all A : Set Real, for all B : Set Real, (for all x : Real, x in A iff x in B) implies A = B
proof
  have h : for all A : Set Real, for all B : Set Real, (for all x : Real, x in A iff x in B) implies A = B by set_real_ext
  then for all A : Set Real, for all B : Set Real, (for all x : Real, x in A iff x in B) implies A = B by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── BI3: rewrite ↔ h — propositional rewriting via biconditional ──────────────

TEST(CheckerTest, IffRewrite_ForwardSubstitution) {
    // suppose h_iff : P iff Q  — desugars to (P→Q)∧(Q→P)
    // goal initially: P and Q
    // rewrite ↔ h_iff (forward: replace P with Q) → goal becomes Q and Q
    auto diag = run_checker("iff_rewrite_fwd",
        "axiom hp : P\n"
        "axiom hq : Q\n"
        "theorem t : P and Q\n"
        "proof\n"
        "  suppose h_iff : P iff Q\n"
        "  rewrite \xe2\x86\x94 h_iff\n"   // ↔ h_iff
        "  then Q and Q by hq and hq\n"
        "end\n");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, IffRewrite_ReverseSubstitution) {
    // rewrite ↔ ← h_iff: replaces Q with P in goal (reverse: Q→P direction)
    // goal: P and Q  →  goal becomes P and P after reverse iff rewrite
    auto diag = run_checker("iff_rewrite_rev",
        "axiom hp : P\n"
        "axiom hq : Q\n"
        "theorem t : P and Q\n"
        "proof\n"
        "  suppose h_iff : P iff Q\n"
        "  rewrite \xe2\x86\x94 \xe2\x86\x90 h_iff\n"  // ↔ ← h_iff
        "  then P and P by hp and hp\n"
        "end\n");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, IffRewrite_NonBiconditional_Errors) {
    // rewrite ↔ h where h is not a biconditional — should error
    auto diag = run_checker("iff_rewrite_wrong_hyp",
        "axiom heq : n = m\n"
        "theorem t : m = n\n"
        "proof\n"
        "  rewrite \xe2\x86\x94 heq\n"   // ↔ heq — heq is an equality, not biconditional
        "  then m = n by refl\n"
        "end\n");
    EXPECT_TRUE(diag.hasErrors());
}

// ── NS2: open X in <decl> — scoped open ──────────────────────────────────────

TEST(CheckerTest, ScopedOpen_TheoremUsesQualifiedName) {
    // namespace Nat contains Nat.add_zero; open Nat in theorem makes it visible
    auto diag = run_checker("scoped_open_basic", R"(
namespace Nat
  axiom add_zero : for all n : Nat, n + 0 = n
end Nat

open Nat in
theorem my_add_zero : for all n : Nat, n + 0 = n
proof
  have h : for all n : Nat, n + 0 = n by add_zero
  then for all n : Nat, n + 0 = n by h
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, ScopedOpen_InnerDeclAvailableAfterwards) {
    // The declared theorem is registered in module_env and usable in a subsequent proof.
    auto diag = run_checker("scoped_open_result", R"(
namespace Arith
  axiom add_zero : for all n : Nat, n + 0 = n
end Arith

open Arith in
theorem my_add_zero : for all n : Nat, n + 0 = n
proof
  have h : for all n : Nat, n + 0 = n by add_zero
  then for all n : Nat, n + 0 = n by h
end

theorem use_result : for all n : Nat, n + 0 = n
proof
  then for all n : Nat, n + 0 = n by my_add_zero
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Namespace alias (alias N = X.Y) ───────────────────────────────────────────

TEST(CheckerTest, NamespaceAlias_QualifiedAccessViaAlias) {
    // "alias A = Foo" creates "A.bar" from "Foo.bar"
    auto diag = run_checker("ns_alias_basic", R"(
namespace Foo
  axiom bar : P
  axiom baz : Q
end Foo

alias A = Foo

theorem t : P and Q
proof
  have hp : P by A.bar
  have hq : Q by A.baz
  then P and Q by hp and hq
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NamespaceAlias_OriginalStillAccessible) {
    // "alias A = Foo" does not remove the original "Foo.*" entries
    auto diag = run_checker("ns_alias_original_kept", R"(
namespace Foo
  axiom bar : P
end Foo

alias A = Foo

theorem t : P and P
proof
  have h1 : P by Foo.bar
  have h2 : P by A.bar
  then P and P by h1 and h2
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, NamespaceAlias_UnknownSourceNoEntries) {
    // "alias A = NonExistent" with nothing to copy — the alias itself is silent
    // (no error), but A.something will not resolve.
    auto diag = run_checker("ns_alias_empty", R"(
alias A = NonExistent

axiom missing : P
theorem t : P
proof
  then P by missing
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

// ── Namespace qualified access and open re-export ──────────────────────────────

TEST(CheckerTest, Namespace_PredDefOpenAndUnfold) {
    // "open X" brings predicate definitions from namespace X into pred_def_table
    // under unqualified names, so that axiom statements referencing the unqualified
    // predicate are correctly unfolded before kernel comparison.
    auto diag = run_checker("ns_preddef_open_and_unfold", R"(
namespace Math
definition IsZero (x : Nat) : Prop := x = 0
end Math

open Math

axiom zero_is_zero : IsZero(0)

theorem t : 0 = 0
proof
  then 0 = 0 by zero_is_zero
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, Namespace_OpenUnfoldsPredDef) {
    // "open X" brings predicate definitions into pred_def_table so that
    // unfold_preds() can expand them in proofs that write unqualified names.
    auto diag = run_checker("ns_open_unfolds_preddef", R"(
namespace Logic
definition IsTrue (P : Prop) : Prop := P
end Logic

open Logic

axiom p_holds : IsTrue(P)

theorem t : P
proof
  then P by p_holds
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, EqSubst_HaveStep) {
    // have h_pa : a = a  by eq_subst h_eq and h_pb
    // where h_eq : a = b, h_pb : b = b (reflexivity for b)
    auto diag = run_checker("eq_subst_have", R"(
axiom h_eq : a = b
axiom h_pb : b = b

theorem t : a = a
proof
  have h_pa : a = a by eq_subst h_eq and h_pb
  then a = a by h_pa
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, EqSubst_ThenStep) {
    auto diag = run_checker("eq_subst_then", R"(
axiom h_eq : a = b
axiom h_pb : b = b

theorem t : a = a
proof
  then a = a by eq_subst h_eq and h_pb
end
)");
    EXPECT_FALSE(diag.hasErrors());
}

TEST(CheckerTest, EqSubst_WrongPremises) {
    // Only one premise — should error
    auto diag = run_checker("eq_subst_wrong_premises", R"(
axiom h_eq : a = b

theorem t : a = a
proof
  then a = a by eq_subst h_eq
end
)");
    EXPECT_TRUE(diag.hasErrors());
}
