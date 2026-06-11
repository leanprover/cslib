/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Basic
public import Cslib.Logics.Propositional.Metalogic.MCS
public import Cslib.Logics.Propositional.Metalogic.Soundness

/-! # Completeness Theorem for Classical Propositional Logic

This module proves completeness for classical propositional logic via the
Henkin (canonical model / MCS) construction: every tautology is derivable.

## Main Results

- `canonicalValuation`: The canonical valuation from a maximally consistent set.
- `prop_truth_lemma`: `Evaluate (canonicalValuation S) φ ↔ φ ∈ S` for MCS `S`.
- `prop_completeness`: `Tautology φ → Derivable PropositionalAxiom φ`.
- `completeness_iff_tautology`:
    `Tautology φ ↔ Derivable PropositionalAxiom φ`.

## References

* [A. Chagrov, M. Zakharyaschev,
  *Modal Logic*][ChagrovZakharyaschev1997],
  Theorem 1.16 (completeness direction), Section 5.1
* Cslib/Logics/Modal/Metalogic/KCompleteness.lean -- modal K completeness
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

variable {Atom : Type*}

/-! ## Axiom hypotheses for PropositionalAxiom -/

private def h_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    PropositionalAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

private def h_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    PropositionalAxiom
      ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

/-! ## Canonical Valuation -/

/-- The canonical valuation from a maximally consistent set.

For MCS `S`, the atom `p` is true iff `Proposition.atom p ∈ S`. -/
def canonicalValuation (S : Set (PL.Proposition Atom)) :
    Valuation Atom :=
  fun p => Proposition.atom p ∈ S

/-! ## Truth Lemma -/

/-- **Truth Lemma**: For an MCS `S` and its canonical valuation `v`,
`Evaluate v φ ↔ φ ∈ S`.

Proof by structural recursion on `φ` (3 cases: atom, bot, imp). -/
theorem prop_truth_lemma
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S) :
    (φ : PL.Proposition Atom) →
    (Evaluate (canonicalValuation S) φ ↔ φ ∈ S)
  | .atom p => by
    constructor
    · intro h; exact h
    · intro h; exact h
  | .bot => by
    constructor
    · intro h; exact absurd h id
    · intro h;
      exact absurd h (prop_mcs_bot_not_mem h_mcs)
  | .imp φ ψ => by
    constructor
    · -- Forward: Evaluate v (φ → ψ) → (φ → ψ) ∈ S
      intro h_sat
      rcases prop_negation_complete h_implyK h_implyS
        h_mcs (φ.imp ψ) with h | h
      · exact h
      · exfalso
        -- h : neg (φ.imp ψ) ∈ S
        -- Derive φ ∈ S from neg (φ.imp ψ) ∈ S
        have h_phi_S : φ ∈ S := by
          apply prop_closed_under_derivation
            h_implyK h_implyS h_mcs
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by
              simp only [List.mem_cons,
                List.not_mem_nil, or_false] at hx
              exact hx ▸ h)
          show (propDerivationSystem
            PropositionalAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          -- [(φ→ψ), (φ→ψ)→⊥] ⊢ ⊥
          have d_bot' :
              DerivationTree PropositionalAxiom
              [φ.imp ψ, (φ.imp ψ).imp .bot]
              Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _
                (by simp [List.mem_cons]))
              (.assumption _ _
                (by simp [List.mem_cons]))
          -- [(φ→ψ), (φ→ψ)→⊥] ⊢ φ (via EFQ)
          have d_efq' :
              DerivationTree PropositionalAxiom
              [φ.imp ψ, (φ.imp ψ).imp .bot] φ :=
            .modus_ponens _ .bot φ
              (.weakening [] _ _
                (.ax [] _ (.efq φ))
                (fun _ h => nomatch h))
              d_bot'
          -- deduction: [(φ→ψ)→⊥] ⊢ (φ→ψ) → φ
          have d_dt := deductionTheorem
            h_implyK h_implyS
            [(φ.imp ψ).imp .bot] (φ.imp ψ) φ
            d_efq'
          -- Peirce: [(φ→ψ)→⊥] ⊢ ((φ→ψ)→φ) → φ
          have d_peirce' :
              DerivationTree PropositionalAxiom
              [(φ.imp ψ).imp .bot]
              (((φ.imp ψ).imp φ).imp φ) :=
            .weakening [] _ _
              (.ax [] _ (.peirce φ ψ))
              (fun _ h => nomatch h)
          -- MP: [(φ→ψ)→⊥] ⊢ φ
          exact ⟨.modus_ponens _ _ _
            d_peirce' d_dt⟩
        -- By IH backward, Evaluate v φ
        have h_sat_phi :=
          (prop_truth_lemma h_mcs φ).mpr h_phi_S
        -- By assumption, Evaluate v ψ
        have h_psi_S :=
          (prop_truth_lemma h_mcs ψ).mp
            (h_sat h_sat_phi)
        -- Derive neg ψ ∈ S from neg (φ.imp ψ) ∈ S
        have h_neg_psi_S :
            Proposition.neg ψ ∈ S := by
          apply prop_closed_under_derivation
            h_implyK h_implyS h_mcs
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by
              simp only [List.mem_cons,
                List.not_mem_nil, or_false] at hx
              exact hx ▸ h)
          show (propDerivationSystem
            PropositionalAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          -- [ψ, (φ→ψ)→⊥] ⊢ φ→ψ via implyK
          have d_imp :
              DerivationTree PropositionalAxiom
              [ψ, (φ.imp ψ).imp .bot]
              (φ.imp ψ) :=
            .modus_ponens _ ψ (φ.imp ψ)
              (.weakening [] _ _
                (.ax [] _ (.implyK ψ φ))
                (fun _ h => nomatch h))
              (.assumption _ _
                (by simp [List.mem_cons]))
          -- [ψ, (φ→ψ)→⊥] ⊢ ⊥
          have d_bot'' :
              DerivationTree PropositionalAxiom
              [ψ, (φ.imp ψ).imp .bot]
              Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _
                (by simp [List.mem_cons]))
              d_imp
          -- deduction: [(φ→ψ)→⊥] ⊢ ψ → ⊥
          exact ⟨deductionTheorem
            h_implyK h_implyS
            [(φ.imp ψ).imp .bot] ψ .bot d_bot''⟩
        -- Contradiction: ψ ∈ S and ¬ψ ∈ S
        exact prop_mcs_bot_not_mem h_mcs
          (prop_implication_property
            h_implyK h_implyS h_mcs
            h_neg_psi_S h_psi_S)
    · -- Backward: (φ → ψ) ∈ S → Evaluate v φ → Evaluate v ψ
      intro h_mem h_sat_phi
      exact (prop_truth_lemma h_mcs ψ).mpr
        (prop_implication_property
          h_implyK h_implyS h_mcs h_mem
          ((prop_truth_lemma h_mcs φ).mp
            h_sat_phi))

/-! ## Completeness Theorem -/

/-- **Completeness Theorem for Classical Propositional Logic**:

If `φ` is a tautology (true under all valuations), then `φ` is
derivable from the empty context using `PropositionalAxiom`. -/
theorem prop_completeness (φ : PL.Proposition Atom)
    (h_taut : Tautology φ) :
    Derivable PropositionalAxiom φ := by
  by_contra h_not_deriv
  -- Show {¬φ} is consistent
  have h_cons : PropSetConsistent PropositionalAxiom
      ({Proposition.neg φ} :
        Set (PL.Proposition Atom)) := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d⟩
    -- Weaken to [¬φ] ⊢ ⊥
    have d_weak :
        DerivationTree PropositionalAxiom
        [Proposition.neg φ] Proposition.bot :=
      .weakening L [Proposition.neg φ] .bot d
        (fun x hx => by
          have := Set.mem_singleton_iff.mp (hL x hx)
          exact List.mem_cons.mpr (Or.inl this))
    -- Deduction theorem: [] ⊢ ¬φ → ⊥
    have d_dne := deductionTheorem
      h_implyK h_implyS
      [] (Proposition.neg φ) .bot d_weak
    -- Build [] ⊢ φ from [] ⊢ ¬φ → ⊥
    let neg_phi := Proposition.neg φ
    -- EFQ: [] ⊢ ⊥ → φ
    have efq_ax :
        DerivationTree PropositionalAxiom
          (Atom := Atom) []
        (Proposition.bot.imp φ) :=
      .ax [] _ (.efq φ)
    -- implyK: [] ⊢ (⊥→φ) → (¬φ → (⊥→φ))
    have ik :
        DerivationTree PropositionalAxiom
          (Atom := Atom) []
        ((Proposition.bot.imp φ).imp
          (neg_phi.imp
            (Proposition.bot.imp φ))) :=
      .ax [] _
        (.implyK (Proposition.bot.imp φ) neg_phi)
    -- MP: [] ⊢ ¬φ → (⊥ → φ)
    have step_k :=
      DerivationTree.modus_ponens [] _ _ ik efq_ax
    -- implyS
    have is_ax :
        DerivationTree PropositionalAxiom
          (Atom := Atom) []
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp
          (neg_phi.imp φ))) :=
      .ax [] _
        (.implyS neg_phi Proposition.bot φ)
    -- MP: [] ⊢ (¬φ→⊥) → (¬φ→φ)
    have step_s :=
      DerivationTree.modus_ponens [] _ _
        is_ax step_k
    -- MP: [] ⊢ ¬φ → φ
    have step3 :=
      DerivationTree.modus_ponens [] _ _
        step_s d_dne
    -- Peirce: [] ⊢ ((φ→⊥)→φ) → φ
    have peirce_ax :
        DerivationTree PropositionalAxiom
          (Atom := Atom) []
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .ax [] _ (.peirce φ Proposition.bot)
    -- MP: [] ⊢ φ
    have d_phi :=
      DerivationTree.modus_ponens [] _ _
        peirce_ax step3
    exact h_not_deriv ⟨d_phi⟩
  -- Lindenbaum: extend {¬φ} to MCS M
  obtain ⟨M, hM_sup, hM_mcs⟩ :=
    prop_lindenbaum h_cons
  -- ¬φ ∈ M
  have h_neg : Proposition.neg φ ∈ M :=
    hM_sup (Set.mem_singleton _)
  -- By truth lemma (backward), Evaluate v (¬φ)
  have h_eval_neg :=
    (prop_truth_lemma hM_mcs
      (Proposition.neg φ)).mpr h_neg
  -- h_taut gives Evaluate v φ -- contradiction
  exact h_eval_neg
    (h_taut (canonicalValuation M))

/-! ## Biconditional Wrapper -/

/-- **Soundness and Completeness**: `φ` is a tautology iff `φ` is
derivable from the empty context. -/
theorem completeness_iff_tautology
    {φ : PL.Proposition Atom} :
    Tautology φ ↔ Derivable PropositionalAxiom φ :=
  ⟨prop_completeness φ, soundness_tautology⟩

end Cslib.Logic.PL
