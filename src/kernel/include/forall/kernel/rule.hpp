#pragma once

namespace forall::kernel {

// The inference rules of propositional natural deduction.
//
// Natural deduction gives every logical connective an "introduction" rule
// (how to prove it) and an "elimination" rule (how to use it).  Each case
// below is annotated with its sequent: "premises ⊢ conclusion".
//
//   Γ ⊢ A   means "under assumptions Γ, proposition A is proved".
//
// Rules:
//   Axiom      : ─────────── declared axiom, no premises       ⊢ P
//   Assumption : P ∈ Γ  →   Γ ⊢ P
//   AndIntro   : Γ ⊢ A,  Γ ⊢ B                             →  Γ ⊢ A ∧ B
//   AndElimL   : Γ ⊢ A ∧ B                                  →  Γ ⊢ A
//   AndElimR   : Γ ⊢ A ∧ B                                  →  Γ ⊢ B
//   ImplIntro  : Γ, A ⊢ B                                   →  Γ ⊢ A → B
//   ImplElim   : Γ ⊢ A → B,  Γ ⊢ A                         →  Γ ⊢ B
//   OrIntroL   : Γ ⊢ A                                      →  Γ ⊢ A ∨ B
//   OrIntroR   : Γ ⊢ B                                      →  Γ ⊢ A ∨ B
//   OrElim     : Γ ⊢ A ∨ B, Γ,A ⊢ C, Γ,B ⊢ C              →  Γ ⊢ C
//   NotIntro   : Γ, A ⊢ ⊥                                   →  Γ ⊢ ¬A
//   NotElim    : Γ ⊢ ¬A,  Γ ⊢ A                             →  Γ ⊢ ⊥
//   FalseElim  : Γ ⊢ ⊥                                      →  Γ ⊢ P  (ex falso)
enum class Rule {
    Axiom,
    Assumption,
    AndIntro, AndElimL, AndElimR,
    ImplIntro, ImplElim,
    OrIntroL, OrIntroR, OrElim,
    NotIntro, NotElim,
    FalseElim,
};

} // namespace forall::kernel
