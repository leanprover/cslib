/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.Frame
public import Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation

/-!
# Point Insertion Lemmas (Burgess 2.4-2.8)

Implements the core point insertion machinery for the Burgess chronicle
construction, adapted for temporal logic (no FrameClass parameter, no liftBase).

## Key Results

- `F_neg_of_G_not` / `P_neg_of_H_not`: If G(φ)/H(φ) not in MCS, then F(¬φ)/P(¬φ) is.
- `lemma_2_4`: Until witness endpoint construction
- `lemma_2_5b` / `lemma_2_5b_past`: g/h-content ordering transitivity
- `lemma_2_6`: Counterexample insertion
- `dc_delta_B_burgessR3`: Extension of B by delta preserves burgessR3
- `BurgessR3Maximal_extension_fails`: Maximality prevents consistent proper extensions
- `g_content_sub`: BurgessR3Maximal implies gContent(A) ⊆ B

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean
* Burgess 1982: "Axioms for tense logic II: Time periods"
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.flexible false
set_option maxHeartbeats 3200000

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

/-! ## Helper: F(neg phi) from G(phi) not in A -/

/-- If G(φ) ∉ MCS A, then F(¬φ) ∈ A. -/
theorem F_neg_of_G_not {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ : Formula Atom)
    (h_Gφ_not : (𝐆φ) ∉ A) :
    (𝐅(¬φ)) ∈ A := by
  rcases temporal_negation_complete h_mcs (Formula.someFuture φ.neg) with h | h
  · exact h
  · -- h : (someFuture φ.neg).neg ∈ A, which is definitionally allFuture φ ∈ A.
    -- Contradiction with h_Gφ_not.
    exact absurd h h_Gφ_not

/-- If H(φ) ∉ MCS A, then P(¬φ) ∈ A. Dual of `F_neg_of_G_not`. -/
theorem P_neg_of_H_not {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ : Formula Atom)
    (h_Hφ_not : (𝐇φ) ∉ A) :
    (𝐏(¬φ)) ∈ A := by
  rcases temporal_negation_complete h_mcs (Formula.somePast φ.neg) with h | h
  · exact h
  · -- ¬P(¬φ) ∈ A is the same as H(φ) ∈ A (by definition), contradicting h_Hφ_not.
    exact absurd h h_Hφ_not

/-! ## Lemma 2.4: Until Witness Endpoint Construction -/

/-- The Until witness seed: {β} ∪ gContent(A) is consistent when U(γ,β) ∈ MCS A. -/
theorem until_witness_seed_consistent {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : (β U γ) ∈ A) :
    Temporal.SetConsistent ({β} ∪ gContent A) := by
  have h_F_β : (𝐅β) ∈ A := by
    have h_ax : DerivationTree FrameClass.Base [] ((Formula.untl β γ).imp (Formula.someFuture β)) :=
      DerivationTree.axiom [] _ (Axiom.until_F γ β) trivial
    exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_until
  exact forward_temporal_witness_seed_consistent A h_mcs β h_F_β

/-- F(γ) ∈ A for all γ ∈ C when gContent(A) ⊆ C. -/
theorem F_mem_of_g_content_sub {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_gc : gContent A ⊆ C) (γ : Formula Atom) (h_γ : γ ∈ C) :
    (𝐅γ) ∈ A := by
  by_contra h_not_F
  have h_neg_F : (Formula.someFuture γ).neg ∈ A :=
    mcs_neg_of_not_mem h_mcs_A h_not_F
  -- ¬F(γ) ∈ A → G(¬γ) ∈ A: from ⊢ ¬¬γ → γ (DNE) via BX3 contrapositive: ¬F(γ) → ¬F(¬¬γ) = G(¬γ).
  have h_G_neg : (𝐆(¬γ)) ∈ A := by
    have h_dne := doubleNegation γ
    have h_G_dne : DerivationTree FrameClass.Base [] ((γ.neg.neg.imp γ).allFuture) :=
      DerivationTree.temporal_necessitation _ h_dne
    have h_bx3 : DerivationTree FrameClass.Base [] ((γ.neg.neg.imp γ).allFuture.imp
        ((Formula.untl γ.neg.neg Formula.top).imp (Formula.untl γ Formula.top))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_until γ.neg.neg γ Formula.top) trivial
    -- ⊢ F(¬¬γ) → F(γ)
    have h_F_mono : DerivationTree FrameClass.Base [] ((Formula.someFuture γ.neg.neg).imp (Formula.someFuture γ)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dne
    -- Contrapositive: ⊢ ¬F(γ) → ¬F(¬¬γ)
    have h_contra : DerivationTree FrameClass.Base [] ((Formula.someFuture γ).neg.imp (Formula.someFuture γ.neg.neg).neg) :=
      contraposition h_F_mono
    -- ¬F(γ) ∈ A → ¬F(¬¬γ) ∈ A = allFuture(γ.neg) ∈ A
    exact temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_contra) h_neg_F
  have h_neg_C : (¬γ) ∈ C := h_gc h_G_neg
  exact mcs_not_mem_of_neg h_mcs_C h_neg_C h_γ

/-- P(α) ∈ C for all α ∈ A when gContent(A) ⊆ C. -/
theorem P_mem_of_g_content_sub {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_gc : gContent A ⊆ C) (α : Formula Atom) (h_α : α ∈ A) :
    (𝐏α) ∈ C := by
  have h_GP : Formula.allFuture (Formula.somePast α) ∈ A := by
    have h_ax : DerivationTree FrameClass.Base [] (α.imp (Formula.allFuture (Formula.somePast α))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future α) trivial
    exact temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_ax) h_α
  exact h_gc h_GP

/-- BurgessR3Maximal existence from gContent inclusion. -/
theorem burgessR3Maximal_from_g_content_sub' {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_gc : gContent A ⊆ C) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal A B C := by
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with top_def
  have h_top_A : top ∈ A :=
    theoremInMcs h_mcs_A (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_bR : burgessR A top C := by
    intro γ hγ
    have h_F := F_mem_of_g_content_sub h_mcs_A h_mcs_C h_gc γ hγ
    have h_bx12 : DerivationTree FrameClass.Base [] ((Formula.someFuture γ).imp (Formula.untl γ top)) :=
      DerivationTree.axiom [] _ (Axiom.F_until_equiv γ) trivial
    exact temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_bx12) h_F
  have h_bRS : burgessRSince C top A := by
    intro α hα
    have h_P := P_mem_of_g_content_sub h_mcs_A h_gc α hα
    have h_bx12' : DerivationTree FrameClass.Base [] ((Formula.somePast α).imp (Formula.snce α top)) :=
      DerivationTree.axiom [] _ (Axiom.P_since_equiv α) trivial
    exact temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_bx12') h_P
  exact burgessR3Maximal_exists_from_seed A C top h_mcs_A h_mcs_C h_bR h_bRS h_top_A

/-- **Lemma 2.4**: Given MCS A with U(γ, β) ∈ A, there exists MCS C with
β ∈ C, gContent(A) ⊆ C, P(U(γ,β)) ∈ C, and a DCS interval set B with
BurgessR3Maximal(A, B, C). -/
noncomputable def lemma_2_4 {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : (β U γ) ∈ A) :
    ∃ B C : Set (Formula Atom), Temporal.SetMaximalConsistent C ∧
      β ∈ C ∧ gContent A ⊆ C ∧
      Formula.somePast (Formula.untl β γ) ∈ C ∧
      BurgessR3Maximal A B C := by
  have h_seed_cons := until_witness_seed_consistent h_mcs γ β h_until
  obtain ⟨C, h_sup, h_C_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_β_C : β ∈ C := h_sup (Set.mem_union_left _ (Set.mem_singleton β))
  have h_g_sub : gContent A ⊆ C := fun χ hχ => h_sup (Set.mem_union_right _ hχ)
  have h_GP : Formula.allFuture (Formula.somePast (Formula.untl β γ)) ∈ A := by
    have h_ax : DerivationTree FrameClass.Base [] ((Formula.untl β γ).imp
        (Formula.allFuture (Formula.somePast (Formula.untl β γ)))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future (Formula.untl β γ)) trivial
    exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_until
  have h_P_until_C : Formula.somePast (Formula.untl β γ) ∈ C := h_g_sub h_GP
  obtain ⟨B, h_B⟩ := burgessR3Maximal_from_g_content_sub' h_mcs h_C_mcs h_g_sub
  exact ⟨B, C, h_C_mcs, h_β_C, h_g_sub, h_P_until_C, h_B⟩

/-! ## MCS-Level Axiom Helpers -/

/-- BX10 at MCS level: U(γ,β) ∈ A implies F(β) ∈ A. -/
theorem until_F_mcs' {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : (β U γ) ∈ A) :
    (𝐅β) ∈ A :=
  until_implies_F_in_mcs h_mcs h_until

/-- BX5 at MCS level: U(γ,β) ∈ A implies U(γ∧U(γ,β), β) ∈ A. -/
theorem self_accum_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : (β U γ) ∈ A) :
    Formula.untl β (Formula.and γ (Formula.untl β γ)) ∈ A :=
  until_self_accum_in_mcs h_mcs h_until

/-- BX5' at MCS level: snce(γ, β) ∈ A implies snce(γ ∧ snce(γ, β), β) ∈ A. -/
theorem self_accum_since_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_since : (β S γ) ∈ A) :
    Formula.snce β (Formula.and γ (Formula.snce β γ)) ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.snce β γ).imp
      (Formula.snce β (Formula.and γ (Formula.snce β γ)))) :=
    DerivationTree.axiom [] _ (Axiom.self_accum_since γ β) trivial
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_since

/-- BX4 at MCS level: φ ∈ A implies G(P(φ)) ∈ A. -/
theorem connect_future_mcs' {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ : Formula Atom)
    (h_φ : φ ∈ A) :
    Formula.allFuture (Formula.somePast φ) ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] (φ.imp (Formula.allFuture (Formula.somePast φ))) :=
    DerivationTree.axiom [] _ (Axiom.connect_future φ) trivial
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_φ

/-- Conjunction introduction at MCS level. -/
theorem conj_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_φ : φ ∈ A) (h_ψ : ψ ∈ A) :
    Formula.and φ ψ ∈ A :=
  dcs_conj_closed (mcs_is_dcs h_mcs) h_φ h_ψ

/-- MCS disjunction elimination: If (φ ∨ ψ) ∈ A then φ ∈ A ∨ ψ ∈ A.
Recall φ.or ψ = φ.neg.imp ψ. -/
theorem or_elim_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {φ ψ : Formula Atom}
    (h : (φ.or ψ) ∈ A) : φ ∈ A ∨ ψ ∈ A := by
  rcases temporal_negation_complete h_mcs φ with h_φ | h_neg_φ
  · exact Or.inl h_φ
  · exact Or.inr (temporal_implication_property h_mcs h h_neg_φ)

/-- BX7 (linear_until) at MCS level. -/
theorem linear_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ χ θ : Formula Atom)
    (h_u1 : (ψ U φ) ∈ A)
    (h_u2 : (θ U χ) ∈ A) :
    Formula.untl (Formula.and ψ θ) (Formula.and φ χ) ∈ A ∨
    Formula.untl (Formula.and ψ χ) (Formula.and φ χ) ∈ A ∨
    Formula.untl (Formula.and φ θ) (Formula.and φ χ) ∈ A := by
  have h_conj := conj_mcs h_mcs _ _ h_u1 h_u2
  have h_bx7 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.linear_until φ ψ χ θ) trivial
  have h_disj := temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx7) h_conj
  rcases or_elim_mcs h_mcs h_disj with h12 | h3
  · rcases or_elim_mcs h_mcs h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-- BX7' (linear_since) at MCS level. -/
theorem linear_since_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ χ θ : Formula Atom)
    (h_s1 : (ψ S φ) ∈ A)
    (h_s2 : (θ S χ) ∈ A) :
    Formula.snce (Formula.and ψ θ) (Formula.and φ χ) ∈ A ∨
    Formula.snce (Formula.and ψ χ) (Formula.and φ χ) ∈ A ∨
    Formula.snce (Formula.and φ θ) (Formula.and φ χ) ∈ A := by
  have h_conj := conj_mcs h_mcs _ _ h_s1 h_s2
  have h_bx7 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.linear_since φ ψ χ θ) trivial
  have h_disj := temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx7) h_conj
  rcases or_elim_mcs h_mcs h_disj with h12 | h3
  · rcases or_elim_mcs h_mcs h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-! ## Lemma 2.5: gContent Ordering Composition -/

/-- **Lemma 2.5** (composition): gContent ordering is transitive. -/
theorem lemma_2_5b {A D C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_AD : gContent A ⊆ D) (h_DC : gContent D ⊆ C) :
    gContent A ⊆ C := by
  intro φ hφ
  have h_GGφ := mcs_g_trans h_mcs_A hφ
  exact h_DC (h_AD h_GGφ)

/-- Dual: hContent ordering is transitive. -/
theorem lemma_2_5b_past {A D C : Set (Formula Atom)}
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_CD : hContent C ⊆ D) (h_DA : hContent D ⊆ A) :
    hContent C ⊆ A := by
  intro φ hφ
  have h_HHφ : Formula.allPast (Formula.allPast φ) ∈ C := mcs_h_trans h_mcs_C hφ
  exact h_DA (h_CD h_HHφ)

/-! ## Lemma 2.6: Counterexample Insertion -/

/-- **Lemma 2.6**: Given MCS A and C with gContent(A) ⊆ C,
if δ ∉ C, then there exists MCS D with ¬δ ∈ D and gContent(A) ⊆ D. -/
noncomputable def lemma_2_6 {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (_h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_g_AC : gContent A ⊆ C)
    (δ : Formula Atom)
    (h_δ_not_C : δ ∉ C) :
    ∃ D : Set (Formula Atom), Temporal.SetMaximalConsistent D ∧
      (¬δ) ∈ D ∧ gContent A ⊆ D := by
  have h_Gδ_not_A : (𝐆δ) ∉ A := by
    intro h_Gδ; exact h_δ_not_C (h_g_AC h_Gδ)
  have h_F_neg_δ := F_neg_of_G_not h_mcs_A δ h_Gδ_not_A
  have h_seed_cons := forward_temporal_witness_seed_consistent A h_mcs_A δ.neg h_F_neg_δ
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  exact ⟨D, h_D_mcs,
    h_sup (Set.mem_union_left _ (Set.mem_singleton _)),
    fun χ hχ => h_sup (Set.mem_union_right _ hχ)⟩

/-! ## Conjunction Elimination at MCS Level -/

/-- Conjunction left elimination at MCS level. -/
theorem conj_left_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_conj : Formula.and φ ψ ∈ A) :
    φ ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.and φ ψ).imp φ) := lceImp φ ψ
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_conj

/-- Conjunction right elimination at MCS level. -/
theorem conj_right_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_conj : Formula.and φ ψ ∈ A) :
    ψ ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.and φ ψ).imp ψ) := rceImp φ ψ
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_conj

/-! ## G/H Implies F/P (Seriality) -/

/-- In an MCS, G(α) implies F(α). -/
theorem G_implies_F_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (α : Formula Atom)
    (h_G : (𝐆α) ∈ A) :
    (𝐅α) ∈ A := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_weak : DerivationTree FrameClass.Base [] (Formula.imp α (Formula.imp top α)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s α top) trivial
  have h_G_top_α : Formula.allFuture (Formula.imp top α) ∈ A := by
    have h1 := theoremInMcs h_mcs (DerivationTree.temporal_necessitation _ h_weak)
    have h2 := theoremInMcs h_mcs (tempKDistDerived α (Formula.imp top α))
    exact temporal_implication_property h_mcs
      (temporal_implication_property h_mcs h2 h1) h_G
  have h_top_in : top ∈ A :=
    theoremInMcs h_mcs (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_F_top : (𝐅top) ∈ A :=
    temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ Axiom.serial_future trivial)) h_top_in
  have h_TUT : (top U top) ∈ A :=
    temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.F_until_equiv top) trivial)) h_F_top
  have h_TUα : (α U top) ∈ A := by
    have h1 := temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.right_mono_until top α top) trivial))
      h_G_top_α
    exact temporal_implication_property h_mcs h1 h_TUT
  exact temporal_implication_property h_mcs
    (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.until_F top α) trivial)) h_TUα

/-- In an MCS, H(α) implies P(α). Mirror of G_implies_F_mcs. -/
theorem H_implies_P_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (α : Formula Atom)
    (h_H : (𝐇α) ∈ A) :
    (𝐏α) ∈ A := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_weak : DerivationTree FrameClass.Base [] (Formula.imp α (Formula.imp top α)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s α top) trivial
  have h_H_top_α : Formula.allPast (Formula.imp top α) ∈ A := by
    have h1 := theoremInMcs h_mcs (pastNecessitation _ h_weak)
    have h2 := theoremInMcs h_mcs (pastKDist α (Formula.imp top α))
    exact temporal_implication_property h_mcs
      (temporal_implication_property h_mcs h2 h1) h_H
  have h_top_in : top ∈ A :=
    theoremInMcs h_mcs (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_P_top : (𝐏top) ∈ A :=
    temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ Axiom.serial_past trivial)) h_top_in
  have h_TST : (top S top) ∈ A :=
    temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.P_since_equiv top) trivial)) h_P_top
  have h_TSα : (α S top) ∈ A := by
    have h1 := temporal_implication_property h_mcs
      (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.right_mono_since top α top) trivial))
      h_H_top_α
    exact temporal_implication_property h_mcs h1 h_TST
  exact temporal_implication_property h_mcs
    (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.since_P top α) trivial)) h_TSα

/-! ## DCS Neg Insert Consistent -/

/-- If B is CUD and φ ∉ B, then {¬φ} ∪ B is consistent. -/
theorem dcs_neg_union_consistent' {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed Sig)
    {φ : Formula Atom} (h_not : φ ∉ Sig) :
    Temporal.SetConsistent ({φ.neg} ∪ Sig) :=
  dcs_neg_insert_consistent h_dcs.2 h_not

/-! ## R3Maximal / BurgessR3Maximal Properties -/

/-- R3Maximal negation completeness: δ ∉ B implies (¬δ) ∈ B. -/
theorem r3Maximal_neg_of_not_mem {A B C : Set (Formula Atom)}
    (h_R3 : R3Maximal A B C) (δ : Formula Atom) (h_not : δ ∉ B) :
    (¬δ) ∈ B := by
  by_contra h_neg_not
  have h_cons := dcs_neg_insert_consistent h_R3.1.2 h_not
  have h_dc_dcs := deductiveClosure_is_dcs h_cons
  have h_B_sub : B ⊆ deductiveClosure ({δ.neg} ∪ B) :=
    fun φ hφ => subset_deductiveClosure ({δ.neg} ∪ B) (Set.mem_union_right _ hφ)
  have h_neg_in : (¬δ) ∈ deductiveClosure ({δ.neg} ∪ B) :=
    subset_deductiveClosure ({δ.neg} ∪ B) (Set.mem_union_left _ (Set.mem_singleton δ.neg))
  have h_proper : B ⊂ deductiveClosure ({δ.neg} ∪ B) :=
    ⟨h_B_sub, fun h_eq => h_neg_not (h_eq h_neg_in)⟩
  have h_r3 : r3Relation A (deductiveClosure ({δ.neg} ∪ B)) C :=
    r3Relation_subset h_R3.2.1 h_B_sub
  exact h_R3.2.2 _ (deductiveClosure_is_dcs h_cons) h_proper h_r3

/-- R3Maximal forces MCS. -/
theorem R3Maximal_is_mcs {A B C : Set (Formula Atom)}
    (h_R3 : R3Maximal A B C) : Temporal.SetMaximalConsistent B := by
  refine ⟨h_R3.1.1, ?_⟩
  intro φ h_not_φ h_cons_insert
  have h_cons : Temporal.SetConsistent ({φ} ∪ B) := by rwa [Set.insert_eq] at h_cons_insert
  have h_dc_dcs := deductiveClosure_is_dcs h_cons
  have h_B_sub : B ⊆ deductiveClosure ({φ} ∪ B) :=
    fun ψ hψ => subset_deductiveClosure ({φ} ∪ B) (Set.mem_union_right _ hψ)
  have h_φ_in : φ ∈ deductiveClosure ({φ} ∪ B) :=
    subset_deductiveClosure ({φ} ∪ B) (Set.mem_union_left _ (Set.mem_singleton φ))
  exact h_R3.2.2 _ h_dc_dcs ⟨h_B_sub, fun h_eq => h_not_φ (h_eq h_φ_in)⟩
    (r3Relation_subset h_R3.2.1 h_B_sub)

/-- An MCS has no proper DCS extension. -/
theorem mcs_no_proper_dcs_extension {B D : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent B) (h_dcs : SetDeductivelyClosed D)
    (hBD : B ⊂ D) : False := by
  obtain ⟨φ, h_φ_D, h_φ_not_B⟩ := Set.not_subset.mp hBD.2
  have h_incons := h_mcs.2 φ h_φ_not_B
  apply h_incons
  intro L hL ⟨d⟩
  exact h_dcs.1 L (fun ψ hψ => (Set.insert_subset h_φ_D hBD.1) (hL ψ hψ)) ⟨d⟩

/-! ## BurgessR3Maximal Extension Properties -/

/-- If L is a subset of {delta} union B with B a CUD, and L derives phi, then either
phi is in B, or there exists beta in B with ⊢ (beta ∧ delta) → phi. -/
theorem dc_delta_B_controlled {B : Set (Formula Atom)} (h_dcs : ClosedUnderDerivation B)
    {delta phi : Formula Atom} {L : List (Formula Atom)}
    (hL_sub : ∀ psi ∈ L, psi ∈ ({delta} : Set (Formula Atom)) ∪ B)
    (hL_deriv : DerivationTree FrameClass.Base L phi) :
    (phi ∈ B) ∨ (∃ beta ∈ B, Nonempty (DerivationTree FrameClass.Base [] ((Formula.and beta delta).imp phi))) := by
  haveI : ∀ x : Formula Atom, Decidable (x ∈ B) := fun x => Classical.propDecidable _
  by_cases h_delta_L : delta ∈ L
  · let L_B := L.filter (· ∈ B)
    have hL_sub_dB : L ⊆ delta :: L_B := by
      intro psi hpsi
      by_cases h_B : psi ∈ B
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hpsi, decide_eq_true_eq.mpr h_B⟩)
      · rcases hL_sub psi hpsi with h | h
        · rw [Set.mem_singleton_iff.mp h]; exact .head _
        · exact absurd h h_B
    have d_w : DerivationTree FrameClass.Base (delta :: L_B) phi :=
      DerivationTree.weakening L (delta :: L_B) phi hL_deriv hL_sub_dB
    have d_imp := deductionTheorem L_B delta phi d_w
    have hLB_sub : ∀ psi ∈ L_B, psi ∈ B := by
      intro psi hpsi; exact decide_eq_true_eq.mp (List.mem_filter.mp hpsi).2
    by_cases hLB_empty : L_B = []
    · rw [hLB_empty] at d_imp
      -- When L_B is empty, ⊢ delta → phi. Need ⊢ (top ∧ delta) → phi.
      have h_top_B : ((Formula.bot : Formula Atom).imp Formula.bot) ∈ B :=
        cud_contains_theorems h_dcs
          (DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.efq (Formula.bot : Formula Atom)) trivial)
      exact Or.inr ⟨Formula.bot.imp Formula.bot, h_top_B, ⟨impTrans (rceImp (Formula.bot.imp Formula.bot) delta) d_imp⟩⟩
    · have h_imp_B : (delta → phi) ∈ B := h_dcs L_B _ hLB_sub d_imp
      right
      refine ⟨delta.imp phi, h_imp_B, ⟨?_⟩⟩
      have h_l : DerivationTree FrameClass.Base [(Formula.and (delta.imp phi) delta)] (delta.imp phi) :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)]
          (Formula.and (delta.imp phi) delta) (delta.imp phi)
          (DerivationTree.weakening [] [(Formula.and (delta.imp phi) delta)] _
            (lceImp (delta.imp phi) delta) (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp))
      have h_r : DerivationTree FrameClass.Base [(Formula.and (delta.imp phi) delta)] delta :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)]
          (Formula.and (delta.imp phi) delta) delta
          (DerivationTree.weakening [] [(Formula.and (delta.imp phi) delta)] _
            (rceImp (delta.imp phi) delta) (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp))
      have h_mp : DerivationTree FrameClass.Base [(Formula.and (delta.imp phi) delta)] phi :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)] delta phi h_l h_r
      exact deductionTheorem [] (Formula.and (delta.imp phi) delta) phi h_mp
  · left
    have hL_B : ∀ psi ∈ L, psi ∈ B := by
      intro psi hpsi
      rcases hL_sub psi hpsi with h | h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hpsi) h_delta_L
      · exact h
    exact h_dcs L phi hL_B hL_deriv

/-- BurgessR3Maximal extension fails: if δ ∉ B, then DC({δ} ∪ B) does NOT satisfy burgessR3. -/
theorem BurgessR3Maximal_extension_fails {A B C : Set (Formula Atom)}
    (h_R3M : BurgessR3Maximal A B C)
    {delta : Formula Atom} (h_delta_not : delta ∉ B) :
    ¬burgessR3 A (deductiveClosure ({delta} ∪ B)) C := by
  intro h_r3
  have h_cud : ClosedUnderDerivation (deductiveClosure ({delta} ∪ B)) :=
    deductiveClosure_closed_under_derivation _
  have h_sub : B ⊆ deductiveClosure ({delta} ∪ B) :=
    fun phi hphi => subset_deductiveClosure ({delta} ∪ B) (Set.mem_union_right _ hphi)
  have h_delta_in : delta ∈ deductiveClosure ({delta} ∪ B) :=
    subset_deductiveClosure ({delta} ∪ B) (Set.mem_union_left _ (Set.mem_singleton delta))
  have h_proper : B ⊂ deductiveClosure ({delta} ∪ B) :=
    ⟨h_sub, fun h_eq => h_delta_not (h_eq h_delta_in)⟩
  exact h_R3M.2.2 _ h_cud h_proper h_r3

/-- dc_delta_B_burgessR3: Extension of B by delta preserves burgessR3. -/
theorem dc_delta_B_burgessR3 {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_dcs : ClosedUnderDerivation B)
    (h_r3 : burgessR3 A B C)
    {delta : Formula Atom}
    (h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C, Formula.untl gamma (Formula.and beta delta) ∈ A)
    (h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A, Formula.snce alpha (Formula.and beta delta) ∈ C) :
    burgessR3 A (deductiveClosure ({delta} ∪ B)) C := by
  constructor
  · intro phi hphi gamma hgamma
    obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
    rcases dc_delta_B_controlled h_dcs hL_sub d with h_B | ⟨beta, hbeta, ⟨h_impl⟩⟩
    · exact h_r3.1 phi h_B gamma hgamma
    · exact untl_left_mono_thm h_mcs_A h_impl (h_until_all beta hbeta gamma hgamma)
  · intro phi hphi alpha halpha
    obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
    rcases dc_delta_B_controlled h_dcs hL_sub d with h_B | ⟨beta, hbeta, ⟨h_impl⟩⟩
    · exact h_r3.2 phi h_B alpha halpha
    · exact snce_left_mono_thm h_mcs_C h_impl (h_since_all beta hbeta alpha halpha)

/-! ## gContent(A) ⊆ B from BurgessR3Maximal -/

/-- Helper: ⊢ φ → (β → (β ∧ φ)). Conjunction introduction curried. -/
noncomputable def conjIntroCurried (β φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (β.imp (Formula.and β φ))) := by
  have h1 : DerivationTree FrameClass.Base [β, φ] (Formula.and β φ) :=
    DerivationTree.modus_ponens [β, φ] _ _
      (DerivationTree.modus_ponens [β, φ] β _
        (DerivationTree.weakening [] [β, φ] _
          (pairing β φ) (List.nil_subset _))
        (DerivationTree.assumption _ β (by simp)))
      (DerivationTree.assumption _ φ (by simp))
  exact deductionTheorem [] φ _ (deductionTheorem [φ] β _ h1)

/-- Helper: ⊢ φ → (φ.neg → ψ) for any ψ. -/
noncomputable def exFalsoFromAssumption (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.neg.imp ψ)) := by
  have h1 : DerivationTree FrameClass.Base [φ.neg, φ] Formula.bot :=
    DerivationTree.modus_ponens [φ.neg, φ] φ Formula.bot
      (DerivationTree.assumption _ φ.neg (by simp))
      (DerivationTree.assumption _ φ (by simp))
  have h2 : DerivationTree FrameClass.Base [φ.neg, φ] ψ :=
    DerivationTree.modus_ponens [φ.neg, φ] Formula.bot ψ
      (DerivationTree.weakening [] [φ.neg, φ] (Formula.bot.imp ψ)
        (efqAxiom ψ) (List.nil_subset _))
      h1
  exact deductionTheorem [] φ _ (deductionTheorem [φ] φ.neg ψ h2)

/-- When {φ} ∪ B is inconsistent with CUD B, then (¬φ) ∈ B. -/
theorem neg_mem_of_inconsistent_union {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B)
    {φ : Formula Atom} (h_not_cons : ¬Temporal.SetConsistent ({φ} ∪ B)) :
    (¬φ) ∈ B := by
  by_contra h_neg_not_B
  apply h_not_cons
  intro L hL ⟨d⟩
  set M := L.filter (fun x => !decide (x = φ)) with hM_def
  have hM_sub_B : ∀ ψ ∈ M, ψ ∈ B := by
    intro ψ hψ; rw [hM_def] at hψ
    have h_mem := List.mem_filter.mp hψ
    have h1 : ψ ∈ L := h_mem.1
    have h2 : ψ ≠ φ := by simp at h_mem; exact h_mem.2
    rcases hL ψ h1 with h | h
    · exact absurd (Set.mem_singleton_iff.mp h) h2
    · exact h
  have hL_sub_φM : L ⊆ φ :: M := by
    intro x hx
    by_cases heq : x = φ
    · subst heq; exact .head M
    · exact .tail _ (List.mem_filter.mpr ⟨hx, by simp; exact heq⟩)
  have d_w : DerivationTree FrameClass.Base (φ :: M) Formula.bot :=
    DerivationTree.weakening L (φ :: M) Formula.bot d hL_sub_φM
  have d_neg : DerivationTree FrameClass.Base M φ.neg := deductionTheorem M φ Formula.bot d_w
  exact h_neg_not_B (h_cud M φ.neg hM_sub_B d_neg)

/-- G(φ.neg → ψ) ∈ A from G(φ) ∈ A, using exFalsoFromAssumption + temporal necessitation + K. -/
theorem G_ex_falso_strengthen {A : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_Gφ : (𝐆φ) ∈ A) :
    (φ.neg.imp ψ).allFuture ∈ A := by
  have d_ef := exFalsoFromAssumption φ ψ
  exact temporal_implication_property h_mcs_A
    (temporal_implication_property h_mcs_A
      (theoremInMcs h_mcs_A (tempKDistDerived φ (φ.neg.imp ψ)))
      (theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ d_ef)))
    h_Gφ

/-- When {φ} ∪ B is inconsistent, burgessR3(A, Set.univ, C). -/
theorem burgessR3_univ_of_inconsistent_ext {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3 : burgessR3 A B C)
    {φ : Formula Atom} (h_Gφ : (𝐆φ) ∈ A)
    (h_neg_in_B : (¬φ) ∈ B) :
    burgessR3 A Set.univ C := by
  constructor
  · intro ψ _ γ hγ
    have h_untl_neg := h_r3.1 φ.neg h_neg_in_B γ hγ
    have h_G_impl := G_ex_falso_strengthen h_mcs_A φ ψ h_Gφ
    exact untl_left_mono_G h_mcs_A h_G_impl h_untl_neg
  · intro ψ _ α hα
    have h_burgessR : burgessR A ψ C := fun γ hγ => by
      have h_untl_neg := h_r3.1 φ.neg h_neg_in_B γ hγ
      have h_G_impl := G_ex_falso_strengthen h_mcs_A φ ψ h_Gφ
      exact untl_left_mono_G h_mcs_A h_G_impl h_untl_neg
    exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR α hα

/-- Set.univ is ClosedUnderDerivation. -/
theorem set_univ_closed_under_derivation : ClosedUnderDerivation (Set.univ : Set (Formula Atom)) :=
  fun _ _ _ _ => Set.mem_univ _

/-- Inconsistent CUD set equals Set.univ. -/
theorem closed_under_derivation_inconsistent_eq_univ
    {D : Set (Formula Atom)} (h_cud : ClosedUnderDerivation D) (h_not_cons : ¬Temporal.SetConsistent D) :
    D = Set.univ := by
  have h_exists : ∃ L : List (Formula Atom), (∀ φ ∈ L, φ ∈ D) ∧ Nonempty (DerivationTree FrameClass.Base L (Formula.bot : Formula Atom)) := by
    by_contra h_all
    apply h_not_cons
    intro L hL hd
    exact h_all ⟨L, hL, hd⟩
  obtain ⟨L, hL, ⟨d⟩⟩ := h_exists
  have h_bot : (Formula.bot : Formula Atom) ∈ D := h_cud L Formula.bot hL d
  ext φ; simp only [Set.mem_univ, iff_true]
  have d_efq : DerivationTree FrameClass.Base [(Formula.bot : Formula Atom)] φ :=
    DerivationTree.modus_ponens [(Formula.bot : Formula Atom)] Formula.bot φ
      (DerivationTree.weakening [] [(Formula.bot : Formula Atom)] ((Formula.bot : Formula Atom).imp φ)
        (efqAxiom φ) (List.nil_subset _))
      (DerivationTree.assumption [(Formula.bot : Formula Atom)] Formula.bot (by simp))
  exact h_cud [(Formula.bot : Formula Atom)] φ (fun ψ hψ => by simp at hψ; rw [hψ]; exact h_bot) d_efq

/-- gContent(A) ⊆ B from BurgessR3Maximal: every G(φ) ∈ A has φ ∈ B. -/
theorem g_content_sub {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_R3M : BurgessR3Maximal A B C) :
    gContent A ⊆ B := by
  intro φ hφ
  by_contra h_not
  have h_dcs : ClosedUnderDerivation B := h_R3M.1
  have h_r3 : burgessR3 A B C := h_R3M.2.1
  -- Case split: is {φ} ∪ B consistent?
  by_cases h_cons : Temporal.SetConsistent ({φ} ∪ B)
  · -- Consistent case: show DC({φ}∪B) satisfies burgessR3, contradicting maximality
    have h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C,
        Formula.untl gamma (Formula.and beta φ) ∈ A := by
      intro beta h_beta gamma h_gamma
      have h_untl := h_r3.1 beta h_beta gamma h_gamma
      -- G(φ) ∈ A, so G(β → β ∧ φ) ∈ A
      have h_flip := conjIntroCurried beta φ
      have h_G_flip := theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ h_flip)
      have h_kd := tempKDistDerived φ (beta.imp (Formula.and beta φ))
      have h_G_guard_str : (beta.imp (Formula.and beta φ)).allFuture ∈ A :=
        temporal_implication_property h_mcs_A
          (temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_kd) h_G_flip) hφ
      exact untl_left_mono_G h_mcs_A h_G_guard_str h_untl
    have h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A,
        Formula.snce alpha (Formula.and beta φ) ∈ C := by
      intro beta h_beta alpha h_alpha
      have h_burgessR : burgessR A (Formula.and beta φ) C :=
        fun gamma h_gamma => h_until_all beta h_beta gamma h_gamma
      exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR alpha h_alpha
    have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
    exact absurd h_r3_ext (BurgessR3Maximal_extension_fails h_R3M h_not)
  · -- Inconsistent case: (¬φ) ∈ B, derive burgessR3(A, Set.univ, C)
    have h_neg_in := neg_mem_of_inconsistent_union h_dcs h_cons
    have h_r3_univ := burgessR3_univ_of_inconsistent_ext h_mcs_A h_mcs_C h_r3 hφ h_neg_in
    -- Set.univ is CUD, B ⊂ Set.univ (B is consistent since BurgessR3Maximal has a DCS part)
    -- Actually B is CUD. B ≠ Set.univ since ⊥ ∉ B (B is consistent? Not necessarily for BurgessR3Maximal).
    -- BurgessR3Maximal only requires CUD, not SDC. But if B were inconsistent, B = Set.univ.
    -- In that case, φ ∈ B = Set.univ, contradicting h_not. So B must be consistent.
    have h_B_ne_univ : B ≠ Set.univ := by
      intro h_eq
      exact h_not (h_eq ▸ Set.mem_univ φ)
    have h_B_cons : Temporal.SetConsistent B := by
      by_contra h_not_cons
      exact h_B_ne_univ (closed_under_derivation_inconsistent_eq_univ h_dcs h_not_cons)
    -- B ⊂ Set.univ (B is a consistent proper subset)
    have h_proper : B ⊂ Set.univ := by
      constructor
      · exact fun _ _ => Set.mem_univ _
      · intro h_eq; exact h_B_ne_univ (Set.eq_univ_iff_forall.mpr (fun x => h_eq (Set.mem_univ x)))
    exact h_R3M.2.2 Set.univ set_univ_closed_under_derivation h_proper h_r3_univ

/-! ## Xu Lemma 2.3: Guard Strengthening via left_mono_until_G -/

/-- Xu Lemma 2.3 (i): If R(A, B, C) then snce(alpha, top) ∈ B for all alpha ∈ A. -/
theorem xu_lemma_2_3_since_top {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {alpha : Formula Atom} (h_alpha : alpha ∈ A) :
    Formula.snce alpha (Formula.bot.imp Formula.bot) ∈ B := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  -- G(snce(alpha, top)) ∈ A: from alpha ∈ A via BX4 + BX12'
  have h_bx4 : DerivationTree FrameClass.Base [] (alpha.imp (alpha.somePast.allFuture)) :=
    DerivationTree.axiom [] _ (Axiom.connect_future alpha) trivial
  have h_G_P_alpha : alpha.somePast.allFuture ∈ A :=
    temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_bx4) h_alpha
  have h_bx12' : DerivationTree FrameClass.Base [] (alpha.somePast.imp (Formula.snce alpha top)) :=
    DerivationTree.axiom [] _ (Axiom.P_since_equiv alpha) trivial
  have h_G_impl : (alpha.somePast.imp (Formula.snce alpha top)).allFuture ∈ A :=
    theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ h_bx12')
  have h_temp_k := tempKDistDerived alpha.somePast (Formula.snce alpha top)
  have h_G_snce : (Formula.snce alpha top).allFuture ∈ A :=
    temporal_implication_property h_mcs_A
      (temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_temp_k) h_G_impl)
      h_G_P_alpha
  -- Until condition: ∀ beta ∈ B, ∀ gamma ∈ C, untl(gamma, beta ∧ snce(alpha, top)) ∈ A
  have h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C,
      Formula.untl gamma (Formula.and beta (Formula.snce alpha top)) ∈ A := by
    intro beta h_beta gamma h_gamma
    have h_untl := h_r3.1 beta h_beta gamma h_gamma
    have h_flip := conjIntroCurried beta (Formula.snce alpha top)
    have h_G_flip := theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ h_flip)
    have h_temp_k2 := tempKDistDerived (Formula.snce alpha top) (beta.imp (Formula.and beta (Formula.snce alpha top)))
    have h_G_guard_str : (beta.imp (Formula.and beta (Formula.snce alpha top))).allFuture ∈ A :=
      temporal_implication_property h_mcs_A
        (temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_temp_k2) h_G_flip)
        h_G_snce
    exact untl_left_mono_G h_mcs_A h_G_guard_str h_untl
  -- Since condition: from burgessR_implies_burgessRSince
  have h_since_all : ∀ beta ∈ B, ∀ alpha' ∈ A,
      Formula.snce alpha' (Formula.and beta (Formula.snce alpha top)) ∈ C := by
    intro beta h_beta alpha' h_alpha'
    have h_burgessR : burgessR A (Formula.and beta (Formula.snce alpha top)) C :=
      fun gamma h_gamma => h_until_all beta h_beta gamma h_gamma
    exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR alpha' h_alpha'
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-- Xu Lemma 2.3 (ii): If R(A, B, C) then untl(gamma, top) ∈ B for all gamma ∈ C. -/
theorem xu_lemma_2_3_until_top {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {gamma : Formula Atom} (h_gamma : gamma ∈ C) :
    Formula.untl gamma (Formula.bot.imp Formula.bot) ∈ B := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  -- H(untl(gamma, top)) ∈ C: from gamma ∈ C via BX4' + BX12
  have h_bx4' : DerivationTree FrameClass.Base [] (gamma.imp (gamma.someFuture.allPast)) :=
    DerivationTree.axiom [] _ (Axiom.connect_past gamma) trivial
  have h_H_F_gamma : gamma.someFuture.allPast ∈ C :=
    temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_bx4') h_gamma
  have h_bx12 : DerivationTree FrameClass.Base [] (gamma.someFuture.imp (Formula.untl gamma top)) :=
    DerivationTree.axiom [] _ (Axiom.F_until_equiv gamma) trivial
  have h_H_impl : (gamma.someFuture.imp (Formula.untl gamma top)).allPast ∈ C :=
    theoremInMcs h_mcs_C (pastNecessitation _ h_bx12)
  have h_past_k := pastKDist gamma.someFuture (Formula.untl gamma top)
  have h_H_untl : (Formula.untl gamma top).allPast ∈ C :=
    temporal_implication_property h_mcs_C
      (temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_past_k) h_H_impl)
      h_H_F_gamma
  -- Since condition
  have h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A,
      Formula.snce alpha (Formula.and beta (Formula.untl gamma top)) ∈ C := by
    intro beta h_beta alpha' h_alpha'
    have h_snce := h_r3.2 beta h_beta alpha' h_alpha'
    have h_flip := conjIntroCurried beta (Formula.untl gamma top)
    have h_H_flip := theoremInMcs h_mcs_C (pastNecessitation _ h_flip)
    have h_past_k2 := pastKDist (Formula.untl gamma top) (beta.imp (Formula.and beta (Formula.untl gamma top)))
    have h_H_guard_str : (beta.imp (Formula.and beta (Formula.untl gamma top))).allPast ∈ C :=
      temporal_implication_property h_mcs_C
        (temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_past_k2) h_H_flip)
        h_H_untl
    exact snce_left_mono_H h_mcs_C h_H_guard_str h_snce
  -- Until condition from burgessRSince_implies_burgessR
  have h_until_all : ∀ beta ∈ B, ∀ gamma' ∈ C,
      Formula.untl gamma' (Formula.and beta (Formula.untl gamma top)) ∈ A := by
    intro beta h_beta gamma' h_gamma'
    have h_burgessRSince : burgessRSince C (Formula.and beta (Formula.untl gamma top)) A :=
      fun alpha h_alpha => h_since_all beta h_beta alpha h_alpha
    exact burgessRSince_implies_burgessR h_mcs_A h_mcs_C h_burgessRSince gamma' h_gamma'
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-! ## Derivation-Level Monotonicity -/

/-- Derivation-level left_mono for Until. -/
noncomputable def untlLeftMonoDeriv (φ ψ χ : Formula Atom)
    (h_impl : DerivationTree FrameClass.Base [] (φ.imp χ)) :
    DerivationTree FrameClass.Base [] ((Formula.untl ψ φ).imp (Formula.untl ψ χ)) := by
  have h_G := DerivationTree.temporal_necessitation _ h_impl
  have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.left_mono_until_G φ χ ψ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_G

/-- Derivation-level left_mono for Since. -/
noncomputable def snceLeftMonoDeriv (φ ψ χ : Formula Atom)
    (h_impl : DerivationTree FrameClass.Base [] (φ.imp χ)) :
    DerivationTree FrameClass.Base [] ((Formula.snce ψ φ).imp (Formula.snce ψ χ)) := by
  have h_H := pastNecessitation _ h_impl
  have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.left_mono_since_H φ χ ψ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_H

/-- Right monotonicity for Until at MCS level. -/
theorem right_mono_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {φ ψ χ : Formula Atom}
    (h_impl : DerivationTree FrameClass.Base [] (ψ.imp χ))
    (h_untl : (ψ U φ) ∈ A) :
    (χ U φ) ∈ A := by
  have h_G_impl : Formula.allFuture (ψ.imp χ) ∈ A :=
    theoremInMcs h_mcs (DerivationTree.temporal_necessitation _ h_impl)
  have h_bx3 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_until ψ χ φ) trivial
  exact temporal_implication_property h_mcs
    (temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx3) h_G_impl) h_untl

/-- Right monotonicity for Since at MCS level. -/
theorem right_mono_since_mcs {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) {φ ψ χ : Formula Atom}
    (h_impl : DerivationTree FrameClass.Base [] (ψ.imp χ))
    (h_snce : (ψ S φ) ∈ C) :
    (χ S φ) ∈ C := by
  have h_H_impl : Formula.allPast (ψ.imp χ) ∈ C :=
    theoremInMcs h_mcs (pastNecessitation _ h_impl)
  have h_bx3' := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_since ψ χ φ) trivial
  exact temporal_implication_property h_mcs
    (temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx3') h_H_impl) h_snce

/-! ## BX13/BX13' at MCS Level -/

/-- BX13 (enrichment_until) at MCS level. -/
theorem enrichment_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {phi psi p : Formula Atom}
    (h_p : p ∈ A)
    (h_untl : (psi U phi) ∈ A) :
    Formula.untl (Formula.and psi (Formula.snce p phi)) phi ∈ A := by
  have h_conj := conj_mcs h_mcs p (Formula.untl psi phi) h_p h_untl
  have h_bx13 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.enrichment_until phi psi p) trivial
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx13) h_conj

/-- BX13' (enrichment_since) at MCS level. -/
theorem enrichment_since_mcs {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) {phi psi p : Formula Atom}
    (h_p : p ∈ C)
    (h_snce : (psi S phi) ∈ C) :
    Formula.snce (Formula.and psi (Formula.untl p phi)) phi ∈ C := by
  have h_conj := conj_mcs h_mcs p (Formula.snce psi phi) h_p h_snce
  have h_bx13 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.enrichment_since phi psi p) trivial
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_bx13) h_conj

/-! ## F/P Monotonicity -/

/-- F-monotonicity at MCS level. -/
theorem F_mono_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {phi psi : Formula Atom}
    (h_impl : DerivationTree FrameClass.Base [] (phi.imp psi))
    (h_F : (𝐅phi) ∈ A) :
    (𝐅psi) ∈ A := by
  -- F(phi) = untl phi top. G(phi → psi) → F(phi) → F(psi) via right_mono_until.
  exact right_mono_until_mcs h_mcs h_impl h_F

/-- P-monotonicity at MCS level. -/
theorem P_mono_mcs {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) {phi psi : Formula Atom}
    (h_impl : DerivationTree FrameClass.Base [] (phi.imp psi))
    (h_P : (𝐏phi) ∈ C) :
    (𝐏psi) ∈ C := by
  exact right_mono_since_mcs h_mcs h_impl h_P

/-! ## Xu Lemma 3.2.1: Full Guard Strengthening -/

/-- Xu Lemma 3.2.1 (i): If R(A, B, C) then untl(gamma, beta) ∈ B for all beta ∈ B, gamma ∈ C. -/
theorem xu_lemma_3_2_1_until {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {beta : Formula Atom} (h_beta : beta ∈ B)
    {gamma : Formula Atom} (h_gamma : gamma ∈ C) :
    (gamma U beta) ∈ B := by
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  have h_until_all : ∀ beta' ∈ B, ∀ gamma' ∈ C,
      Formula.untl gamma' (Formula.and beta' (Formula.untl gamma beta)) ∈ A := by
    intro beta' h_beta' gamma' h_gamma'
    -- From burgessR3: untl(gamma'', beta'') ∈ A where gamma'' = gamma ∧ gamma', beta'' = beta ∧ beta'
    have h_beta'' : Formula.and beta beta' ∈ B := cud_conj_closed h_dcs h_beta h_beta'
    have h_gamma'' : Formula.and gamma gamma' ∈ C := conj_mcs h_mcs_C gamma gamma' h_gamma h_gamma'
    have h_untl := h_r3.1 (Formula.and beta beta') h_beta'' (Formula.and gamma gamma') h_gamma''
    -- h_untl : untl(γ∧γ', β∧β') ∈ A, i.e., (β∧β') guards until (γ∧γ') happens
    -- BX5: self_accum takes (guard, event): untl(event, guard) → untl(event, guard ∧ untl(event, guard))
    have h_sa := self_accum_until_mcs h_mcs_A (Formula.and beta beta') (Formula.and gamma gamma') h_untl
    have h_guard_r : DerivationTree FrameClass.Base [] (((Formula.and beta beta').and (Formula.untl (Formula.and gamma gamma') (Formula.and beta beta'))).imp
        (Formula.and beta' (Formula.untl gamma beta))) := by
      have h_event_proj := lceImp gamma gamma'  -- ⊢ γ∧γ' → γ
      have h_guard_proj := lceImp beta beta'    -- ⊢ β∧β' → β
      -- ⊢ untl(γ∧γ', β∧β') → untl(γ, β∧β') via right_mono (event)
      have h1 : DerivationTree FrameClass.Base [] ((Formula.untl (Formula.and gamma gamma') (Formula.and beta beta')).imp
          (Formula.untl gamma (Formula.and beta beta'))) := by
        have h_G := DerivationTree.temporal_necessitation _ h_event_proj
        have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_until (Formula.and gamma gamma') gamma (Formula.and beta beta')) trivial
        exact DerivationTree.modus_ponens [] _ _ h_ax h_G
      -- ⊢ untl(γ, β∧β') → untl(γ, β) via left_mono (guard)
      have h2 : DerivationTree FrameClass.Base [] ((Formula.untl gamma (Formula.and beta beta')).imp
          (Formula.untl gamma beta)) :=
        untlLeftMonoDeriv (Formula.and beta beta') gamma beta h_guard_proj
      -- ⊢ untl(γ∧γ', β∧β') → untl(γ, β)
      have h_untl_proj := impTrans h1 h2
      -- Now build the pairing: ⊢ x∧y → β' ∧ untl(γ, β)
      -- ⊢ x∧y → β' from ⊢ x → β' via x = β∧β' → β' and ⊢ x∧y → x
      have h_left := impTrans (lceImp (Formula.and beta beta') (Formula.untl (Formula.and gamma gamma') (Formula.and beta beta')))
        (rceImp beta beta')
      -- ⊢ x∧y → untl(γ,β) from ⊢ y → untl(γ,β) and ⊢ x∧y → y
      have h_right := impTrans (rceImp (Formula.and beta beta') (Formula.untl (Formula.and gamma gamma') (Formula.and beta beta')))
        h_untl_proj
      -- Combine: ⊢ x∧y → β' ∧ untl(γ, β) using pairing
      -- Need: from ⊢ A → B and ⊢ A → C, derive ⊢ A → B ∧ C
      -- Build in context [A]: B and C, then apply pairing
      have := DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.untl (Formula.and gamma gamma') (Formula.and beta beta')))] _ _
        (DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.untl (Formula.and gamma gamma') (Formula.and beta beta')))] _ _
          (DerivationTree.weakening [] [_] _ (pairing beta' (Formula.untl gamma beta)) (List.nil_subset _))
          (DerivationTree.modus_ponens [_] _ _
            (DerivationTree.weakening [] [_] _ h_left (List.nil_subset _))
            (DerivationTree.assumption _ _ (by simp))))
        (DerivationTree.modus_ponens [_] _ _
          (DerivationTree.weakening [] [_] _ h_right (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp)))
      exact deductionTheorem [] _ _ this
    -- Apply left_mono: G(guard_str) → untl(γ∧γ', (β∧β') ∧ untl(γ∧γ', β∧β')) → untl(γ∧γ', β' ∧ untl(γ, β))
    have h_step1 := untl_left_mono_thm h_mcs_A h_guard_r h_sa
    -- Now ⊢ γ∧γ' → γ' to go from untl(γ∧γ', ...) to untl(γ', ...)
    have h_event_proj_r := rceImp gamma gamma'
    exact right_mono_until_mcs h_mcs_A h_event_proj_r h_step1
  -- Since condition from burgessR_implies_burgessRSince
  have h_since_all : ∀ beta' ∈ B, ∀ alpha ∈ A,
      Formula.snce alpha (Formula.and beta' (Formula.untl gamma beta)) ∈ C := by
    intro beta' h_beta' alpha h_alpha
    have h_burgessR : burgessR A (Formula.and beta' (Formula.untl gamma beta)) C :=
      fun gamma' h_gamma' => h_until_all beta' h_beta' gamma' h_gamma'
    exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR alpha h_alpha
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-- Xu Lemma 3.2.1 (ii): If R(A, B, C) then snce(alpha, beta) ∈ B for all beta ∈ B, alpha ∈ A. -/
theorem xu_lemma_3_2_1_since {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {beta : Formula Atom} (h_beta : beta ∈ B)
    {alpha : Formula Atom} (h_alpha : alpha ∈ A) :
    (alpha S beta) ∈ B := by
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  -- Since condition (dual of xu_lemma_3_2_1_until)
  have h_since_all : ∀ beta' ∈ B, ∀ alpha' ∈ A,
      Formula.snce alpha' (Formula.and beta' (Formula.snce alpha beta)) ∈ C := by
    intro beta' h_beta' alpha' h_alpha'
    have h_beta'' : Formula.and beta beta' ∈ B := cud_conj_closed h_dcs h_beta h_beta'
    have h_alpha'' : Formula.and alpha alpha' ∈ A := conj_mcs h_mcs_A alpha alpha' h_alpha h_alpha'
    have h_snce := h_r3.2 (Formula.and beta beta') h_beta'' (Formula.and alpha alpha') h_alpha''
    -- h_snce : snce(α∧α', β∧β') ∈ C. self_accum_since takes (guard, event)
    have h_sa := self_accum_since_mcs h_mcs_C (Formula.and beta beta') (Formula.and alpha alpha') h_snce
    -- Monotonicity to get snce(α', β' ∧ snce(α, β)) from snce(α∧α', (β∧β') ∧ snce(α∧α', β∧β'))
    have h_guard_r : DerivationTree FrameClass.Base [] (((Formula.and beta beta').and (Formula.snce (Formula.and alpha alpha') (Formula.and beta beta'))).imp
        (Formula.and beta' (Formula.snce alpha beta))) := by
      have h_event_proj := lceImp alpha alpha'
      have h_guard_proj := lceImp beta beta'
      have h1 : DerivationTree FrameClass.Base [] ((Formula.snce (Formula.and alpha alpha') (Formula.and beta beta')).imp
          (Formula.snce alpha (Formula.and beta beta'))) := by
        have h_H := pastNecessitation _ h_event_proj
        have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_since (Formula.and alpha alpha') alpha (Formula.and beta beta')) trivial
        exact DerivationTree.modus_ponens [] _ _ h_ax h_H
      have h2 : DerivationTree FrameClass.Base [] ((Formula.snce alpha (Formula.and beta beta')).imp
          (Formula.snce alpha beta)) :=
        snceLeftMonoDeriv (Formula.and beta beta') alpha beta h_guard_proj
      have h_snce_proj := impTrans h1 h2
      have h_left := impTrans (lceImp (Formula.and beta beta') (Formula.snce (Formula.and alpha alpha') (Formula.and beta beta')))
        (rceImp beta beta')
      have h_right := impTrans (rceImp (Formula.and beta beta') (Formula.snce (Formula.and alpha alpha') (Formula.and beta beta')))
        h_snce_proj
      have := DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.snce (Formula.and alpha alpha') (Formula.and beta beta')))] _ _
        (DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.snce (Formula.and alpha alpha') (Formula.and beta beta')))] _ _
          (DerivationTree.weakening [] [_] _ (pairing beta' (Formula.snce alpha beta)) (List.nil_subset _))
          (DerivationTree.modus_ponens [_] _ _
            (DerivationTree.weakening [] [_] _ h_left (List.nil_subset _))
            (DerivationTree.assumption _ _ (by simp))))
        (DerivationTree.modus_ponens [_] _ _
          (DerivationTree.weakening [] [_] _ h_right (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp)))
      exact deductionTheorem [] _ _ this
    have h_step1 := snce_left_mono_thm h_mcs_C h_guard_r h_sa
    have h_event_proj_r := rceImp alpha alpha'
    exact right_mono_since_mcs h_mcs_C h_event_proj_r h_step1
  -- Until condition from burgessRSince_implies_burgessR
  have h_until_all : ∀ beta' ∈ B, ∀ gamma ∈ C,
      Formula.untl gamma (Formula.and beta' (Formula.snce alpha beta)) ∈ A := by
    intro beta' h_beta' gamma h_gamma
    have h_burgessRSince : burgessRSince C (Formula.and beta' (Formula.snce alpha beta)) A :=
      fun alpha' h_alpha' => h_since_all beta' h_beta' alpha' h_alpha'
    exact burgessRSince_implies_burgessR h_mcs_A h_mcs_C h_burgessRSince gamma h_gamma
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-! ## Duality: hContent ↔ gContent -/

/-- hContent(B) ⊆ A implies gContent(A) ⊆ B for MCS A, B. -/
theorem h_content_sub_imp_g_content_sub' {A B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_B : Temporal.SetMaximalConsistent B)
    (h_hBA : hContent B ⊆ A) :
    gContent A ⊆ B := by
  intro ψ hψ
  by_contra h_not
  have h_neg_ψ : (¬ψ) ∈ B := mcs_neg_of_not_mem h_mcs_B h_not
  have h_ax : DerivationTree FrameClass.Base [] (ψ.neg.imp (ψ.neg.someFuture.allPast)) :=
    DerivationTree.axiom [] _ (Axiom.connect_past ψ.neg) trivial
  have h_HF : Formula.allPast (Formula.someFuture ψ.neg) ∈ B :=
    temporal_implication_property h_mcs_B (theoremInMcs h_mcs_B h_ax) h_neg_ψ
  have h_F_neg_ψ_A : (𝐅(¬ψ)) ∈ A := h_hBA h_HF
  have h_G_nn : Formula.allFuture ψ.neg.neg ∈ A := by
    have h_dni_ax := dni ψ
    have h_G_dni := theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ h_dni_ax)
    have h_kd := tempKDistDerived ψ ψ.neg.neg
    have h1 := temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_kd) h_G_dni
    exact temporal_implication_property h_mcs_A h1 hψ
  exact someFuture_allFuture_neg_absurd h_mcs_A ψ.neg h_F_neg_ψ_A h_G_nn

/-- gContent(A) ⊆ B implies hContent(B) ⊆ A for MCS A, B. -/
theorem g_content_sub_imp_h_content_sub' {A B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_B : Temporal.SetMaximalConsistent B)
    (h_gAB : gContent A ⊆ B) :
    hContent B ⊆ A := by
  intro ψ hψ
  by_contra h_not
  have h_neg_ψ : (¬ψ) ∈ A := mcs_neg_of_not_mem h_mcs_A h_not
  have h_GP : Formula.allFuture (Formula.somePast ψ.neg) ∈ A :=
    connect_future_mcs' h_mcs_A ψ.neg h_neg_ψ
  have h_P_neg_ψ_B : (𝐏(¬ψ)) ∈ B := h_gAB h_GP
  have h_H_nn : Formula.allPast ψ.neg.neg ∈ B := by
    have h_dni_ax := dni ψ
    have h_H_dni := theoremInMcs h_mcs_B (pastNecessitation _ h_dni_ax)
    have h_kd := pastKDist ψ ψ.neg.neg
    have h1 := temporal_implication_property h_mcs_B (theoremInMcs h_mcs_B h_kd) h_H_dni
    exact temporal_implication_property h_mcs_B h1 hψ
  exact somePast_allPast_neg_absurd h_mcs_B ψ.neg h_P_neg_ψ_B h_H_nn

/-! ## Lemma 2.6 Splitting: BurgessR3Maximal Interval Insertion -/

/-- **Lemma 2.6 Splitting**: Given BurgessR3Maximal(A, B, C) with β ∉ B,
construct MCS D with (¬β) ∈ D and decomposed BurgessR3Maximal relations. -/
theorem lemma_2_6_splitting {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (β : Formula Atom)
    (h_β_not_B : β ∉ B) :
    ∃ B' D B'', BurgessR3Maximal A B' D ∧ BurgessR3Maximal D B'' C ∧
      Temporal.SetMaximalConsistent D ∧ (¬β) ∈ D ∧ B ⊆ D ∧ B ⊆ B' ∧ B ⊆ B'' := by
  have h_B_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Step 1: Trivial seed {β.neg} ∪ B is consistent
  have h_sdc : SetDeductivelyClosed B := cud_not_mem_is_sdc h_B_dcs h_β_not_B
  have h_seed_cons : Temporal.SetConsistent ({β.neg} ∪ B) := dcs_neg_insert_consistent h_B_dcs h_β_not_B
  -- Step 2: Lindenbaum-extend to MCS D
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  -- Step 3: Extract seed memberships
  have h_β_neg_D : (¬β) ∈ D := h_sup (Set.mem_union_left _ (Set.mem_singleton β.neg))
  have h_B_sub_D : B ⊆ D := fun φ hφ => h_sup (Set.mem_union_right _ hφ)
  -- Step 4: Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  have h_untl_D : ∀ β' ∈ B, ∀ γ ∈ C, Formula.untl γ β' ∈ D := by
    intro β' hβ' γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until h_mcs_A h_mcs_C h_r3m hβ' hγ)
  have h_snce_D : ∀ β' ∈ B, ∀ α ∈ A, Formula.snce α β' ∈ D := by
    intro β' hβ' α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since h_mcs_A h_mcs_C h_r3m hβ' hα)
  -- Step 5: Establish burgessR3(D, B, C)
  have h_rSet_D : burgessRSet D B C := fun β' hβ' γ hγ => h_untl_D β' hβ' γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β' hβ'
    exact burgessR_implies_burgessRSince h_D_mcs h_mcs_C (h_rSet_D β' hβ')
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  -- Step 6: Establish burgessR3(A, B, D)
  have h_rSetSince_A : burgessRSetSince D B A := fun β' hβ' α hα => h_snce_D β' hβ' α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β' hβ'
    exact burgessRSince_implies_burgessR h_mcs_A h_D_mcs (h_rSetSince_A β' hβ')
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Step 7: BurgessR3Maximal via Zorn
  obtain ⟨B', h_B_sub_B', h_B'_max⟩ := burgessR3Maximal_extension_exists h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_B_sub_B'', h_B''_max⟩ := burgessR3Maximal_extension_exists h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_β_neg_D, h_B_sub_D, h_B_sub_B', h_B_sub_B''⟩

/-! ## Propositional Helpers for Burgess Compression -/

/-- Identity derivation: ⊢ φ → φ. -/
noncomputable def identity' (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp φ) := by
  have h1 : DerivationTree FrameClass.Base [φ] φ := DerivationTree.assumption [φ] φ (by simp)
  exact deductionTheorem [] φ φ h1

/-- From ⊢ R → A and ⊢ R → B, derive ⊢ R → A ∧ B. -/
noncomputable def combineImpConj {R A B : Formula Atom}
    (h1 : DerivationTree FrameClass.Base [] (R.imp A))
    (h2 : DerivationTree FrameClass.Base [] (R.imp B)) :
    DerivationTree FrameClass.Base [] (R.imp (Formula.and A B)) := by
  have d1 : DerivationTree FrameClass.Base [R] A :=
    DerivationTree.modus_ponens [R] R A
      (DerivationTree.weakening [] [R] _ h1 (List.nil_subset _))
      (DerivationTree.assumption _ R (by simp))
  have d2 : DerivationTree FrameClass.Base [R] B :=
    DerivationTree.modus_ponens [R] R B
      (DerivationTree.weakening [] [R] _ h2 (List.nil_subset _))
      (DerivationTree.assumption _ R (by simp))
  have d3 : DerivationTree FrameClass.Base [R] (Formula.and A B) :=
    DerivationTree.modus_ponens [R] B (Formula.and A B)
      (DerivationTree.modus_ponens [R] A (B.imp (Formula.and A B))
        (DerivationTree.weakening [] [R] _ (pairing A B) (List.nil_subset _)) d1) d2
  exact deductionTheorem [] R (Formula.and A B) d3

/-- De Morgan for disjunction negation: ⊢ ¬(A ∨ B) → ¬A ∧ ¬B.
    Recall A.or B = A.neg.imp B. -/
noncomputable def demorganDisjNegForward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.or B).neg.imp (Formula.and A.neg B.neg)) := by
  set neg_disj := (A.or B).neg -- = (A.neg.imp B).neg = (A.neg.imp B) → ⊥
  -- Step 1: derive ¬A from neg_disj
  -- ⊢ A → (¬A → B): this is exFalsoFromAssumption A B
  have h_A_to_disj : DerivationTree FrameClass.Base [] (A.imp (A.neg.imp B)) :=
    exFalsoFromAssumption A B
  -- In context [neg_disj, A]: derive ⊥
  have d_negA : DerivationTree FrameClass.Base [neg_disj] A.neg := by
    have d1 : DerivationTree FrameClass.Base [A, neg_disj] (A.neg.imp B) :=
      DerivationTree.modus_ponens [A, neg_disj] A (A.neg.imp B)
        (DerivationTree.weakening [] [A, neg_disj] _ h_A_to_disj (List.nil_subset _))
        (DerivationTree.assumption _ A (by simp))
    have d2 : DerivationTree FrameClass.Base [A, neg_disj] Formula.bot :=
      DerivationTree.modus_ponens [A, neg_disj] (A.neg.imp B) Formula.bot
        (DerivationTree.assumption _ neg_disj (by simp)) d1
    exact deductionTheorem [neg_disj] A Formula.bot d2
  -- Step 2: derive ¬B from neg_disj
  -- ⊢ B → (¬A → B) via weakening: ⊢ B → ¬A → B is Axiom.imp_s
  have h_B_to_disj : DerivationTree FrameClass.Base [] (B.imp (A.neg.imp B)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s B A.neg) trivial
  have d_negB : DerivationTree FrameClass.Base [neg_disj] B.neg := by
    have d1 : DerivationTree FrameClass.Base [B, neg_disj] (A.neg.imp B) :=
      DerivationTree.modus_ponens [B, neg_disj] B (A.neg.imp B)
        (DerivationTree.weakening [] [B, neg_disj] _ h_B_to_disj (List.nil_subset _))
        (DerivationTree.assumption _ B (by simp))
    have d2 : DerivationTree FrameClass.Base [B, neg_disj] Formula.bot :=
      DerivationTree.modus_ponens [B, neg_disj] (A.neg.imp B) Formula.bot
        (DerivationTree.assumption _ neg_disj (by simp)) d1
    exact deductionTheorem [neg_disj] B Formula.bot d2
  -- Step 3: pair ¬A and ¬B
  have d_conj : DerivationTree FrameClass.Base [neg_disj] (Formula.and A.neg B.neg) :=
    DerivationTree.modus_ponens [neg_disj] B.neg (Formula.and A.neg B.neg)
      (DerivationTree.modus_ponens [neg_disj] A.neg (B.neg.imp (Formula.and A.neg B.neg))
        (DerivationTree.weakening [] [neg_disj] _ (pairing A.neg B.neg) (List.nil_subset _))
        d_negA)
      d_negB
  exact deductionTheorem [] neg_disj (Formula.and A.neg B.neg) d_conj

/-! ## List-Level Cut and Conjunction Helpers -/

/-- List-level cut (derivation from implied context):
If Γ ⊢ φ for each φ ∈ L, and L ⊢ ψ, then Γ ⊢ ψ. -/
noncomputable def derivationFromImplied (Γ : Context Atom) :
    (L : Context Atom) → (ψ : Formula Atom) →
    (∀ φ ∈ L, DerivationTree FrameClass.Base Γ φ) →
    DerivationTree FrameClass.Base L ψ →
    DerivationTree FrameClass.Base Γ ψ
  | [], ψ, _, d => DerivationTree.weakening [] Γ ψ d (List.nil_subset Γ)
  | l :: L', ψ, h_derives, d => by
    have d_impl : DerivationTree FrameClass.Base L' (l.imp ψ) := deductionTheorem L' l ψ d
    have h_derives' : ∀ φ ∈ L', DerivationTree FrameClass.Base Γ φ := fun φ hφ =>
      h_derives φ (List.mem_cons.mpr (Or.inr hφ))
    have d_impl_Γ : DerivationTree FrameClass.Base Γ (l.imp ψ) :=
      derivationFromImplied Γ L' (l.imp ψ) h_derives' d_impl
    have d_l : DerivationTree FrameClass.Base Γ l := h_derives l (List.mem_cons.mpr (Or.inl rfl))
    exact DerivationTree.modus_ponens Γ l ψ d_impl_Γ d_l

/-- Conjunction of a list of formulas. Empty list gives ⊤ (= ⊥→⊥). -/
noncomputable def listConj : List (Formula Atom) → Formula Atom
  | [] => Formula.bot.imp Formula.bot  -- top
  | [φ] => φ
  | (φ :: rest) => Formula.and φ (listConj rest)

/-- ⊢ listConj L → φ for each φ ∈ L. -/
noncomputable def listConjImpliesElem :
    (L : List (Formula Atom)) → (φ : Formula Atom) → (h : φ ∈ L) →
    DerivationTree FrameClass.Base [] ((listConj L).imp φ)
  | [ψ], φ, h => by
    simp [List.mem_singleton] at h
    subst h; simp [listConj]; exact identity' φ
  | (ψ₁ :: ψ₂ :: rest), φ, h => by
    simp [listConj]
    by_cases h_eq : φ = ψ₁
    · subst h_eq; exact lceImp φ (listConj (ψ₂ :: rest))
    · have h' : φ ∈ ψ₂ :: rest := by
        rcases List.mem_cons.mp h with rfl | h'
        · exact absurd rfl h_eq
        · exact h'
      have h_right : DerivationTree FrameClass.Base [] _ := rceImp ψ₁ (listConj (ψ₂ :: rest))
      have h_rec := listConjImpliesElem (ψ₂ :: rest) φ h'
      exact impTrans h_right h_rec

/-- If B is CUD and all elements of L are in B, then listConj L ∈ B. -/
theorem list_conj_mem_dcs {B : Set (Formula Atom)} (h_dcs : ClosedUnderDerivation B) :
    (L : List (Formula Atom)) → (h : ∀ φ ∈ L, φ ∈ B) → listConj L ∈ B
  | [], _ => cud_contains_theorems h_dcs (identity' (Formula.bot : Formula Atom))
  | [φ], h => by simp [listConj]; exact h φ (List.mem_singleton.mpr rfl)
  | (φ₁ :: φ₂ :: rest), h => by
    simp [listConj]
    have h1 : φ₁ ∈ B := h φ₁ (List.mem_cons.mpr (Or.inl rfl))
    have h2 : listConj (φ₂ :: rest) ∈ B :=
      list_conj_mem_dcs h_dcs (φ₂ :: rest) (fun ψ hψ =>
        h ψ (List.mem_cons.mpr (Or.inr hψ)))
    exact cud_conj_closed h_dcs h1 h2

/-- If A is MCS and all elements of L are in A, then listConj L ∈ A. -/
theorem list_conj_mem_mcs {A : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent A) :
    (L : List (Formula Atom)) → (h : ∀ φ ∈ L, φ ∈ A) → listConj L ∈ A
  | [], _ => theoremInMcs h_mcs (identity' (Formula.bot : Formula Atom))
  | [φ], h => by simp [listConj]; exact h φ (List.mem_singleton.mpr rfl)
  | (φ₁ :: φ₂ :: rest), h => by
    simp [listConj]
    have h1 : φ₁ ∈ A := h φ₁ (List.mem_cons.mpr (Or.inl rfl))
    have h2 : listConj (φ₂ :: rest) ∈ A :=
      list_conj_mem_mcs h_mcs (φ₂ :: rest) (fun ψ hψ =>
        h ψ (List.mem_cons.mpr (Or.inr hψ)))
    exact conj_mcs h_mcs φ₁ (listConj (φ₂ :: rest)) h1 h2

/-- If F(φ) ∈ A (MCS), then {φ} is consistent. -/
theorem consistent_of_F_mem {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    (φ : Formula Atom) (h_F : (𝐅φ) ∈ A) :
    Temporal.SetConsistent ({φ} : Set (Formula Atom)) := by
  have h_seed := forward_temporal_witness_seed_consistent A h_mcs φ h_F
  exact SetConsistent_of_subset (Set.subset_union_left) h_seed

/-- If P(φ) ∈ C (MCS), then {φ} is consistent. -/
theorem consistent_of_P_mem {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C)
    (φ : Formula Atom) (h_P : (𝐏φ) ∈ C) :
    Temporal.SetConsistent ({φ} : Set (Formula Atom)) := by
  have h_seed := past_temporal_witness_seed_consistent C h_mcs φ h_P
  exact SetConsistent_of_subset (Set.subset_union_left) h_seed

/-- If {φ} is consistent and [φ] ⊢ ⊥, then False. -/
theorem inconsistent_singleton_false {φ : Formula Atom}
    (h_cons : Temporal.SetConsistent ({φ} : Set (Formula Atom)))
    (d : DerivationTree FrameClass.Base [φ] Formula.bot) : False :=
  h_cons [φ] (fun ψ hψ => by simp [List.mem_singleton] at hψ; subst hψ; exact Set.mem_singleton _) ⟨d⟩

/-! ## Guard Conjunction Helpers -/

/-- Guard conjunction for Until: If untl(β₁, γ) ∈ A and untl(β₂, γ) ∈ A (MCS A),
then untl(β₁∧β₂, γ) ∈ A. Uses BX7 + BX3. -/
theorem untl_conj_guard {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (h1 : (γ U β₁) ∈ A)
    (h2 : (γ U β₂) ∈ A) :
    Formula.untl γ (Formula.and β₁ β₂) ∈ A := by
  have h_conj : Formula.and (Formula.untl γ β₁) (Formula.untl γ β₂) ∈ A :=
    dcs_conj_closed (mcs_is_dcs h_mcs) h1 h2
  have h_bx7 := theoremInMcs h_mcs
    (DerivationTree.axiom [] _ (Axiom.linear_until β₁ γ β₂ γ) trivial)
  have h_disj := temporal_implication_property h_mcs h_bx7 h_conj
  set guard := Formula.and β₁ β₂
  set D1 := Formula.untl (Formula.and γ γ) guard
  set D2 := Formula.untl (Formula.and γ β₂) guard
  set D3 := Formula.untl (Formula.and β₁ γ) guard
  set target := Formula.untl γ guard
  have mk_thm : ∀ e : Formula Atom, DerivationTree FrameClass.Base [] (e.imp γ) →
      DerivationTree FrameClass.Base [] ((Formula.untl e guard).imp target) := by
    intro e h_e_imp
    have h_G := DerivationTree.temporal_necessitation _ h_e_imp
    have h_bx3 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_until e γ guard) trivial
    exact DerivationTree.modus_ponens [] _ _ h_bx3 h_G
  have h_D1_impl := theoremInMcs h_mcs (mk_thm _ (lceImp γ γ))
  have h_D2_impl := theoremInMcs h_mcs (mk_thm _ (lceImp γ β₂))
  have h_D3_impl := theoremInMcs h_mcs (mk_thm _ (rceImp β₁ γ))
  rcases temporal_negation_complete h_mcs D3 with h | h
  · exact temporal_implication_property h_mcs h_D3_impl h
  · have h_D1_or_D2 : Formula.or D1 D2 ∈ A := by
      rcases temporal_negation_complete h_mcs (Formula.or D1 D2) with h' | h'
      · exact h'
      · have := temporal_implication_property h_mcs h_disj h'
        exact absurd this (mcs_not_mem_of_neg h_mcs h)
    rcases temporal_negation_complete h_mcs D1 with h' | h'
    · exact temporal_implication_property h_mcs h_D1_impl h'
    · have h_D2 := temporal_implication_property h_mcs h_D1_or_D2 h'
      exact temporal_implication_property h_mcs h_D2_impl h_D2

/-- Guard conjunction for Since: If snce(β₁, γ) ∈ A and snce(β₂, γ) ∈ A (MCS A),
then snce(β₁∧β₂, γ) ∈ A. Uses BX7' + BX3'. -/
theorem snce_conj_guard {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (h1 : (γ S β₁) ∈ A)
    (h2 : (γ S β₂) ∈ A) :
    Formula.snce γ (Formula.and β₁ β₂) ∈ A := by
  have h_conj : Formula.and (Formula.snce γ β₁) (Formula.snce γ β₂) ∈ A :=
    dcs_conj_closed (mcs_is_dcs h_mcs) h1 h2
  have h_bx7' := theoremInMcs h_mcs
    (DerivationTree.axiom [] _ (Axiom.linear_since β₁ γ β₂ γ) trivial)
  have h_disj := temporal_implication_property h_mcs h_bx7' h_conj
  set guard := Formula.and β₁ β₂
  set D1 := Formula.snce (Formula.and γ γ) guard
  set D2 := Formula.snce (Formula.and γ β₂) guard
  set D3 := Formula.snce (Formula.and β₁ γ) guard
  set target := Formula.snce γ guard
  have mk_thm : ∀ e : Formula Atom, DerivationTree FrameClass.Base [] (e.imp γ) →
      DerivationTree FrameClass.Base [] ((Formula.snce e guard).imp target) := by
    intro e h_e_imp
    have h_H := pastNecessitation _ h_e_imp
    have h_bx3' := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_since e γ guard) trivial
    exact DerivationTree.modus_ponens [] _ _ h_bx3' h_H
  have h_D1_impl := theoremInMcs h_mcs (mk_thm _ (lceImp γ γ))
  have h_D2_impl := theoremInMcs h_mcs (mk_thm _ (lceImp γ β₂))
  have h_D3_impl := theoremInMcs h_mcs (mk_thm _ (rceImp β₁ γ))
  rcases temporal_negation_complete h_mcs D3 with h | h
  · exact temporal_implication_property h_mcs h_D3_impl h
  · have h_D1_or_D2 : Formula.or D1 D2 ∈ A := by
      rcases temporal_negation_complete h_mcs (Formula.or D1 D2) with h' | h'
      · exact h'
      · have := temporal_implication_property h_mcs h_disj h'
        exact absurd this (mcs_not_mem_of_neg h_mcs h)
    rcases temporal_negation_complete h_mcs D1 with h' | h'
    · exact temporal_implication_property h_mcs h_D1_impl h'
    · have h_D2 := temporal_implication_property h_mcs h_D1_or_D2 h'
      exact temporal_implication_property h_mcs h_D2_impl h_D2

/-- Set-level guard conjunction for burgessR. -/
theorem burgessR_conj {A C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {α β : Formula Atom}
    (hα : burgessR A α C) (hβ : burgessR A β C) :
    burgessR A (Formula.and α β) C := by
  intro γ hγ
  exact untl_conj_guard h_mcs (hα γ hγ) (hβ γ hγ)

/-- Set-level guard conjunction for burgessRSince. -/
theorem burgessRSince_conj {A C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C)
    {α β : Formula Atom}
    (hα : burgessRSince C α A) (hβ : burgessRSince C β A) :
    burgessRSince C (Formula.and α β) A := by
  intro γ hγ
  exact snce_conj_guard h_mcs (hα γ hγ) (hβ γ hγ)

/-! ## Iterated BX13 Enrichment Structures -/

/-- Structure to hold the result of iterated BX13 enrichment. -/
structure EnrichedEvent (A : Set (Formula Atom)) (guard event : Formula Atom) (alphas : List (Formula Atom)) where
  event' : Formula Atom
  h_untl : Formula.untl event' guard ∈ A
  h_impl : DerivationTree FrameClass.Base [] (event'.imp event)
  h_snce : ∀ α ∈ alphas, DerivationTree FrameClass.Base [] (event'.imp (Formula.snce α guard))

/-- Iterated BX13 enrichment: given untl(guard, event) ∈ A and a list of
formulas each in A, enrich the event with snce(guard, αⱼ) for each αⱼ. -/
noncomputable def iteratedEnrichment {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    (guard : Formula Atom) :
    (alphas : List (Formula Atom)) →
    (h_alphas : ∀ α ∈ alphas, α ∈ A) →
    (event : Formula Atom) →
    (event U guard) ∈ A →
    EnrichedEvent A guard event alphas
  | [], _, event, h_untl => EnrichedEvent.mk event h_untl (identity' event) (fun _ h => by simp at h)
  | α :: rest, h_alphas, event, h_untl => by
    have h_α : α ∈ A := h_alphas α (List.mem_cons.mpr (Or.inl rfl))
    have h_enriched := enrichment_until_mcs h_mcs h_α h_untl
    have h_rest : ∀ α' ∈ rest, α' ∈ A := fun α' hα' =>
      h_alphas α' (List.mem_cons.mpr (Or.inr hα'))
    let evt := iteratedEnrichment h_mcs guard rest h_rest
      (Formula.and event (Formula.snce α guard)) h_enriched
    exact EnrichedEvent.mk evt.event' evt.h_untl
      (impTrans evt.h_impl (lceImp event (Formula.snce α guard)))
      (fun α' hα' => by
        by_cases h_eq : α' = α
        · subst h_eq; exact impTrans evt.h_impl (rceImp event (Formula.snce α' guard))
        · have h : α' ∈ rest := by
            rcases List.mem_cons.mp hα' with rfl | h
            · exact absurd rfl h_eq
            · exact h
          exact evt.h_snce α' h)

/-- Structure for iterated BX13' (Since-direction) enrichment. -/
structure EnrichedEventSince (C : Set (Formula Atom)) (guard event : Formula Atom) (gammas : List (Formula Atom)) where
  event' : Formula Atom
  h_snce : Formula.snce event' guard ∈ C
  h_impl : DerivationTree FrameClass.Base [] (event'.imp event)
  h_untl : ∀ γ ∈ gammas, DerivationTree FrameClass.Base [] (event'.imp (Formula.untl γ guard))

/-- Iterated BX13' enrichment (Since direction). -/
noncomputable def iteratedEnrichmentSince {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C)
    (guard : Formula Atom) :
    (gammas : List (Formula Atom)) →
    (h_gammas : ∀ γ ∈ gammas, γ ∈ C) →
    (event : Formula Atom) →
    (event S guard) ∈ C →
    EnrichedEventSince C guard event gammas
  | [], _, event, h_snce => EnrichedEventSince.mk event h_snce (identity' event) (fun _ h => by simp at h)
  | γ :: rest, h_gammas, event, h_snce => by
    have h_γ : γ ∈ C := h_gammas γ (List.mem_cons.mpr (Or.inl rfl))
    have h_enriched := enrichment_since_mcs h_mcs h_γ h_snce
    have h_rest : ∀ γ' ∈ rest, γ' ∈ C := fun γ' hγ' =>
      h_gammas γ' (List.mem_cons.mpr (Or.inr hγ'))
    let evt := iteratedEnrichmentSince h_mcs guard rest h_rest
      (Formula.and event (Formula.untl γ guard)) h_enriched
    exact EnrichedEventSince.mk evt.event' evt.h_snce
      (impTrans evt.h_impl (lceImp event (Formula.untl γ guard)))
      (fun γ' hγ' => by
        by_cases h_eq : γ' = γ
        · subst h_eq; exact impTrans evt.h_impl (rceImp event (Formula.untl γ' guard))
        · have h : γ' ∈ rest := by
            rcases List.mem_cons.mp hγ' with rfl | h
            · exact absurd rfl h_eq
            · exact h
          exact evt.h_untl γ' h)

/-! ## Lemma 2.7: Until-Formula Splitting -/

/-- The D0 seed for Lemma 2.7: B ∪ {eta} ∪ {snce(α, β∧xi) : β ∈ B, α ∈ A}. -/
def lemma_2_7_seed (A B _C : Set (Formula Atom)) (xi eta : Formula Atom) : Set (Formula Atom) :=
  B ∪ {eta} ∪ {φ | ∃ β ∈ B, ∃ α ∈ A, φ = Formula.snce α (Formula.and β xi)}

/-- Extract a B-guard from a single element of the lemma_2_7_seed. -/
noncomputable def l27_guard {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation B)
    (xi eta : Formula Atom) (φ : Formula Atom) (h : φ ∈ lemma_2_7_seed A B C xi eta) :
    { g : Formula Atom // g ∈ B } := by
  classical
  by_cases h1 : φ ∈ B
  · exact ⟨φ, h1⟩
  · by_cases h5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce α (Formula.and β' xi)
    · exact ⟨Classical.choose h5, (Classical.choose_spec h5).1⟩
    · exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_dcs (identity' (Formula.bot : Formula Atom))⟩

/-- Recursively extract B-guards from L ⊆ lemma_2_7_seed. -/
noncomputable def l27_collect_guards {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation B)
    (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed A B C xi eta) →
    { gs : List (Formula Atom) // ∀ g ∈ gs, g ∈ B }
  | [], _ => ⟨[], fun _ h => (by simp at h)⟩
  | φ :: rest, hL =>
    let ⟨g, hg⟩ := l27_guard h_dcs xi eta φ (hL φ (List.mem_cons.mpr (Or.inl rfl)))
    let ⟨gs, hgs⟩ := l27_collect_guards h_dcs xi eta rest
      (fun ψ hψ => hL ψ (List.mem_cons.mpr (Or.inr hψ)))
    ⟨g :: gs, fun g' hg' => by
      rcases List.mem_cons.mp hg' with rfl | h
      · exact hg
      · exact hgs g' h⟩

/-- For each element of L ⊆ lemma_2_7_seed, extract the A-event. -/
noncomputable def l27_a_event_list {A B C : Set (Formula Atom)}
    (xi eta : Formula Atom) (L : List (Formula Atom))
    (_hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed A B C xi eta) : List (Formula Atom) :=
  L.filterMap (fun φ => by
    classical
    exact if h : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce α (Formula.and β' xi) then
      some (Classical.choose (Classical.choose_spec h).2)
    else none)

/-- Elements of l27_a_event_list are in A. -/
theorem l27_a_event_list_mem {A B C : Set (Formula Atom)}
    {xi eta : Formula Atom} {L : List (Formula Atom)}
    {hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed A B C xi eta}
    {α : Formula Atom} (hα : α ∈ l27_a_event_list xi eta L hL) : α ∈ A := by
  unfold l27_a_event_list at hα
  rcases List.mem_filterMap.mp hα with ⟨φ, _, h_eq⟩
  split at h_eq
  · next h_snce5 =>
    simp at h_eq
    rw [← h_eq]
    exact (Classical.choose_spec ((Classical.choose_spec h_snce5).2)).1
  · simp at h_eq

/-- If φ ∈ L ∩ B then φ is in l27_collect_guards output. -/
theorem l27_collect_guards_mem_of_B {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation B) (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed A B C xi eta) →
    ∀ φ ∈ L, φ ∈ B → φ ∈ (l27_collect_guards h_dcs xi eta L hL).val
  | [], _, φ, hφ, _ => (by simp at hφ)
  | ψ :: rest, hL, φ, hφ, h_B => by
    simp [l27_collect_guards]
    rcases List.mem_cons.mp hφ with rfl | h_rest
    · left
      unfold l27_guard; simp [h_B]
    · right; exact l27_collect_guards_mem_of_B h_dcs xi eta rest _ φ h_rest h_B

/-- Formula.and is injective in the first argument. -/
theorem formula_and_left_cancel {a b c : Formula Atom}
    (h : Formula.and a c = Formula.and b c) : a = b := by
  simp only [Formula.and, Formula.neg] at h
  exact (Formula.imp.injEq _ _ _ _ |>.mp (Formula.imp.injEq _ _ _ _ |>.mp h).1).1

/-- l27_guard for snce(β'∧xi,α') when snce(β'∧xi,α') ∉ B returns β'. -/
theorem l27_guard_snce_xi_val {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation B) (xi eta β' α' : Formula Atom)
    (h_seed : Formula.snce α' (Formula.and β' xi) ∈ lemma_2_7_seed A B C xi eta)
    (h_not_B : Formula.snce α' (Formula.and β' xi) ∉ B)
    (hβ' : β' ∈ B) (hα' : α' ∈ A) :
    (l27_guard h_dcs xi eta (Formula.snce α' (Formula.and β' xi)) h_seed).val = β' := by
  unfold l27_guard; simp [h_not_B]
  split
  · next h =>
    have h_exists : ∃ β'' ∈ B, ∃ α'' ∈ A,
        Formula.snce α' (Formula.and β' xi) = Formula.snce α'' (Formula.and β'' xi) :=
      ⟨β', h.1, α', h.2, rfl⟩
    have h_spec := Classical.choose_spec h_exists
    obtain ⟨hβ_B, α'', hα'', h_eq⟩ := h_spec
    rw [Formula.snce.injEq] at h_eq
    have h_β_eq := (formula_and_left_cancel h_eq.2).symm
    convert h_β_eq using 1; simp
  · next h =>
    exfalso; exact h ⟨hβ', hα'⟩

/-- If snce(β'∧xi,α') ∈ L with β'∈B, α'∈A, snce(β'∧xi,α') ∉ B,
then β' is in the guard list. -/
theorem l27_collect_guards_mem_of_snce_xi {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation B) (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed A B C xi eta) →
    ∀ β' α', Formula.snce α' (Formula.and β' xi) ∈ L → β' ∈ B → α' ∈ A →
      Formula.snce α' (Formula.and β' xi) ∉ B →
      β' ∈ (l27_collect_guards h_dcs xi eta L hL).val
  | [], _, β', α', hφ, _, _, _ => (by simp at hφ)
  | ψ :: rest, hL, β', α', hφ, hβ', hα', h_not_B => by
    simp [l27_collect_guards]
    rcases List.mem_cons.mp hφ with rfl | h_rest
    · left
      exact (l27_guard_snce_xi_val h_dcs xi eta β' α'
        (hL (Formula.snce α' (Formula.and β' xi)) (List.mem_cons.mpr (Or.inl rfl)))
        h_not_B hβ' hα').symm
    · right
      exact l27_collect_guards_mem_of_snce_xi h_dcs xi eta rest _ β' α' h_rest hβ' hα' h_not_B

/-- If snce(β'∧xi,α') ∈ L with β'∈B, α'∈A, then α' ∈ l27_a_event_list. -/
theorem l27_a_event_list_α_mem_xi {A B C : Set (Formula Atom)}
    {xi eta : Formula Atom} {L : List (Formula Atom)}
    {hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed A B C xi eta}
    {β' α' : Formula Atom} (hφ : Formula.snce α' (Formula.and β' xi) ∈ L)
    (hβ' : β' ∈ B) (hα' : α' ∈ A) :
    α' ∈ l27_a_event_list xi eta L hL := by
  unfold l27_a_event_list
  apply List.mem_filterMap.mpr
  refine ⟨Formula.snce α' (Formula.and β' xi), hφ, ?_⟩
  have h_ex : ∃ β'' ∈ B, ∃ α'' ∈ A, Formula.snce α' (Formula.and β' xi) = Formula.snce α'' (Formula.and β'' xi) :=
    ⟨β', hβ', α', hα', rfl⟩
  rw [dif_pos h_ex]
  congr 1
  have h_spec := Classical.choose_spec (Classical.choose_spec h_ex).2
  rw [Formula.snce.injEq] at h_spec
  exact h_spec.2.1.symm

/-- Consistency of the Lemma 2.7 D0 seed. Uses BX5+BX7+BX13 chain. -/
theorem lemma_2_7_seed_consistent {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : (eta U xi) ∈ A)
    (h_xi_not_B : xi ∉ B) :
    Temporal.SetConsistent (lemma_2_7_seed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  have h_not_r3_xi := BurgessR3Maximal_extension_fails h_r3m h_xi_not_B
  have h_neg_until_exists : ∃ beta0 ∈ B, ∃ gamma0 ∈ C,
      Formula.untl gamma0 (Formula.and beta0 xi) ∉ A := by
    by_contra h_all_until
    push Not at h_all_until
    have h_rset : burgessRSet A (deductiveClosure ({xi} ∪ B)) C := by
      intro phi hphi gamma hgamma
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨h_impl⟩⟩
      · exact h_r3.1 phi h_B_case gamma hgamma
      · exact untl_left_mono_thm h_mcs_A h_impl (h_all_until beta_w hbeta_w gamma hgamma)
    have h_rsince : burgessRSetSince C (deductiveClosure ({xi} ∪ B)) A := by
      intro phi hphi alpha halpha
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨h_impl⟩⟩
      · exact h_r3.2 phi h_B_case alpha halpha
      · have h_burgessR_ext : burgessR A (Formula.and beta_w xi) C :=
          fun gamma hgamma => h_all_until beta_w hbeta_w gamma hgamma
        have h_snce_ext := burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR_ext alpha halpha
        exact snce_left_mono_thm h_mcs_C h_impl h_snce_ext
    exact h_not_r3_xi ⟨h_rset, h_rsince⟩
  obtain ⟨beta0, h_beta0, gamma0, h_gamma0, h_not_in_A⟩ := h_neg_until_exists
  have h_neg_until_in_A : (Formula.untl gamma0 (Formula.and beta0 xi)).neg ∈ A := by
    rcases temporal_negation_complete h_mcs_A
      (Formula.untl gamma0 (Formula.and beta0 xi)) with h | h
    · exfalso; exact h_not_in_A h
    · exact h
  intro L hL ⟨d⟩
  have h_bx5_xe := self_accum_until_mcs h_mcs_A xi eta h_until
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B) (h_b_beta0 : DerivationTree FrameClass.Base [] (b.imp beta0))
      (γ_hat : Formula Atom) (hγ : γ_hat ∈ C) (h_γ_gamma0 : DerivationTree FrameClass.Base [] (γ_hat.imp gamma0))
      (alpha_list : List (Formula Atom)) (h_alphas : ∀ α ∈ alpha_list, α ∈ A),
      Σ' (event : Formula Atom),
        (𝐅event) ∈ A ×'
        DerivationTree FrameClass.Base [] (event.imp b) ×'
        DerivationTree FrameClass.Base [] (event.imp eta) ×'
        DerivationTree FrameClass.Base [] (event.imp (Formula.untl γ_hat b)) ×'
        (∀ α ∈ alpha_list, DerivationTree FrameClass.Base [] (event.imp (Formula.snce α (Formula.and b (Formula.and xi (Formula.untl eta xi)))))) by
    let b_list_raw := (l27_collect_guards h_B_dcs xi eta L hL).val
    have hb_list : ∀ g ∈ b_list_raw, g ∈ B := (l27_collect_guards h_B_dcs xi eta L hL).property
    let b_list := beta0 :: b_list_raw
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact h_beta0
      · exact hb_list g h
    let a_list := l27_a_event_list xi eta L hL
    have ha_list : ∀ α ∈ a_list, α ∈ A := fun α hα => l27_a_event_list_mem hα
    let b := listConj b_list
    let γ_hat := gamma0
    have hb_B : b ∈ B := list_conj_mem_dcs h_B_dcs b_list hb_list'
    have hγ_C : γ_hat ∈ C := h_gamma0
    have h_b_to_beta0 : DerivationTree FrameClass.Base [] (b.imp beta0) :=
      listConjImpliesElem b_list beta0 (List.mem_cons.mpr (Or.inl rfl))
    have h_γ_to_gamma0 : DerivationTree FrameClass.Base [] (γ_hat.imp gamma0) := identity' gamma0
    obtain ⟨event, h_F_event, h_ev_b, h_ev_eta, _h_ev_untl, h_ev_snce⟩ :=
      h_key b hb_B h_b_to_beta0 γ_hat hγ_C h_γ_to_gamma0 a_list ha_list
    let χ_gen := Formula.and xi (Formula.untl eta xi)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree FrameClass.Base [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_raw : φ ∈ b_list_raw := l27_collect_guards_mem_of_B h_B_dcs xi eta L hL φ hφ h_B_case
        have h_φ_in_b : φ ∈ b_list := List.mem_cons.mpr (Or.inr h_φ_in_raw)
        have h_b_to_φ : DerivationTree FrameClass.Base [] (b.imp φ) := listConjImpliesElem b_list φ h_φ_in_b
        have h_ev_to_φ : DerivationTree FrameClass.Base [] (event.imp φ) := impTrans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · by_cases h_snce5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce α (Formula.and β' xi)
          · let β' := Classical.choose h_snce5
            have hβ' : β' ∈ B := (Classical.choose_spec h_snce5).1
            let α' := Classical.choose (Classical.choose_spec h_snce5).2
            have hα' : α' ∈ A := (Classical.choose_spec (Classical.choose_spec h_snce5).2).1
            have h_eq : φ = Formula.snce α' (Formula.and β' xi) := (Classical.choose_spec (Classical.choose_spec h_snce5).2).2
            have h_φ_eq_snce5 : Formula.snce α' (Formula.and β' xi) ∈ L := by rw [←h_eq]; exact hφ
            rw [h_eq]
            by_cases h_snce5_B : Formula.snce α' (Formula.and β' xi) ∈ B
            · have h_in_raw := l27_collect_guards_mem_of_B h_B_dcs xi eta L hL (Formula.snce α' (Formula.and β' xi)) h_φ_eq_snce5 h_snce5_B
              have h_in_b : Formula.snce α' (Formula.and β' xi) ∈ b_list := List.mem_cons.mpr (Or.inr h_in_raw)
              have h_b_imp : DerivationTree FrameClass.Base [] (b.imp (Formula.snce α' (Formula.and β' xi))) :=
                listConjImpliesElem b_list (Formula.snce α' (Formula.and β' xi)) h_in_b
              have h_ev_imp := impTrans h_ev_b h_b_imp
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_ev_imp (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
            · have h_α'_in_a := @l27_a_event_list_α_mem_xi _ A B C xi eta L hL β' α' h_φ_eq_snce5 hβ' hα'
              have h_ev_snce_α' := h_ev_snce α' h_α'_in_a
              have h_β'_in_raw := l27_collect_guards_mem_of_snce_xi h_B_dcs xi eta L hL β' α' h_φ_eq_snce5 hβ' hα' h_snce5_B
              have h_β'_in_b : β' ∈ b_list := List.mem_cons.mpr (Or.inr h_β'_in_raw)
              have h_b_to_β' : DerivationTree FrameClass.Base [] (b.imp β') := listConjImpliesElem b_list β' h_β'_in_b
              have h_bχ_to_β'xi : DerivationTree FrameClass.Base [] ((Formula.and b χ_gen).imp (Formula.and β' xi)) := by
                have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp b χ_gen) h_b_to_β'
                have h2 : DerivationTree FrameClass.Base [] _ := impTrans (rceImp b χ_gen) (lceImp xi (Formula.untl eta xi))
                exact combineImpConj h1 h2
              have h_mono := snceLeftMonoDeriv (Formula.and b χ_gen) α' (Formula.and β' xi) h_bχ_to_β'xi
              have h_chain := impTrans h_ev_snce_α' h_mono
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp [lemma_2_7_seed, h_B_case, h_eta, h_snce5] at h_φ_seed
    have d_event : DerivationTree FrameClass.Base [event] Formula.bot :=
      derivationFromImplied [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_F_mem h_mcs_A event h_F_event
    exact inconsistent_singleton_false h_event_cons d_event
  -- Prove h_key: the generalized BX5+BX7+BX13 chain helper.
  intro b hb h_b_beta0 γ_hat hγ h_γ_gamma0 alpha_list h_alphas
  have h_untl_bg : (γ_hat U b) ∈ A := h_r3.1 b hb γ_hat hγ
  have h_bx5_bg := self_accum_until_mcs h_mcs_A b γ_hat h_untl_bg
  let φ_gen := Formula.and b (Formula.untl γ_hat b)
  let χ_gen := Formula.and xi (Formula.untl eta xi)
  have h_bx7_gen := linear_until_mcs h_mcs_A φ_gen γ_hat χ_gen eta h_bx5_bg h_bx5_xe
  have h_guard_to_b0xi : DerivationTree FrameClass.Base [] ((Formula.and φ_gen χ_gen).imp (Formula.and beta0 xi)) := by
    have h1 : DerivationTree FrameClass.Base [] _ := impTrans (impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.untl γ_hat b))) h_b_beta0
    have h2 : DerivationTree FrameClass.Base [] _ := impTrans (rceImp φ_gen χ_gen) (lceImp xi (Formula.untl eta xi))
    exact combineImpConj h1 h2
  have h_D3_gen : Formula.untl (Formula.and φ_gen eta) (Formula.and φ_gen χ_gen) ∈ A := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_rm : DerivationTree FrameClass.Base [] ((Formula.and γ_hat eta).imp gamma0) :=
        impTrans (lceImp γ_hat eta) h_γ_gamma0
      have h_contra := right_mono_until_mcs h_mcs_A h_rm
        (untl_left_mono_thm h_mcs_A h_guard_to_b0xi h_D1)
      exact mcs_not_mem_of_neg h_mcs_A h_neg_until_in_A h_contra
    · exfalso
      have h_rm : DerivationTree FrameClass.Base [] ((Formula.and γ_hat χ_gen).imp gamma0) :=
        impTrans (lceImp γ_hat χ_gen) h_γ_gamma0
      have h_contra := right_mono_until_mcs h_mcs_A h_rm
        (untl_left_mono_thm h_mcs_A h_guard_to_b0xi h_D2)
      exact mcs_not_mem_of_neg h_mcs_A h_neg_until_in_A h_contra
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichment h_mcs_A guard alpha_list h_alphas base_event h_D3_gen
  let event := evt.event'
  have h_F_event : (𝐅event) ∈ A := until_implies_F_in_mcs h_mcs_A evt.h_untl
  have h_ev_base := evt.h_impl
  have h_ev_b : DerivationTree FrameClass.Base [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.untl γ_hat b)))
  have h_ev_eta : DerivationTree FrameClass.Base [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_untl : DerivationTree FrameClass.Base [] (event.imp (Formula.untl γ_hat b)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.untl γ_hat b)))
  have h_ev_snce : ∀ α ∈ alpha_list,
      DerivationTree FrameClass.Base [] (event.imp (Formula.snce α (Formula.and b χ_gen))) := by
    intro α hα
    have h_snce_guard := evt.h_snce α hα
    have h_guard_to_bχ : DerivationTree FrameClass.Base [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.untl γ_hat b))
      have h2 : DerivationTree FrameClass.Base [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_snce_guard (snceLeftMonoDeriv guard α (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_F_event, h_ev_b, h_ev_eta, h_ev_untl, h_ev_snce⟩

/-- **Lemma 2.7**: Given BurgessR3Maximal(A, B, C) with untl(xi, eta) ∈ A and xi ∉ B,
construct MCS D with eta ∈ D and B' with B ⊆ B' and xi ∈ B'. -/
theorem lemma_2_7 {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : (eta U xi) ∈ A)
    (h_xi_not_B : xi ∉ B) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal A B' D ∧
      BurgessR3Maximal D B'' C ∧
      Temporal.SetMaximalConsistent D ∧
      eta ∈ D ∧
      B ⊆ B' ∧
      B ⊆ D ∧
      B ⊆ B'' ∧
      xi ∈ B' := by
  have h_seed_cons := lemma_2_7_seed_consistent h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_until h_xi_not_B
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma_2_7_seed A B C xi eta; simp [lemma_2_7_seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma_2_7_seed A B C xi eta; simp [lemma_2_7_seed, hφ]
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, (γ U β) ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, (α S β) ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  have h_snce_conj_xi_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce α (Formula.and β xi) ∈ D := by
    intro β hβ α hα; apply h_sup
    show Formula.snce α (Formula.and β xi) ∈ lemma_2_7_seed A B C xi eta
    simp only [lemma_2_7_seed, Set.mem_union, Set.mem_setOf_eq]; right; exact ⟨β, hβ, α, hα, rfl⟩
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (identity' (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_snce_xi_D : ∀ α ∈ A, (α S xi) ∈ D := by
    intro α hα
    have h_impl : DerivationTree FrameClass.Base [] ((Formula.and β₀ xi).imp xi) := rceImp β₀ xi
    exact snce_left_mono_thm h_D_mcs h_impl (h_snce_conj_xi_D β₀ hβ₀ α hα)
  have h_burgessRSince_xi : burgessRSince D xi A := h_snce_xi_D
  have h_burgessR_xi : burgessR A xi D :=
    burgessRSince_implies_burgessR h_mcs_A h_D_mcs h_burgessRSince_xi
  have h_burgessR_conj' : ∀ β ∈ B, burgessR A (Formula.and β xi) D := by
    intro β hβ
    exact burgessR_conj h_mcs_A (h_rSet_A β hβ) h_burgessR_xi
  have h_until_conj : ∀ β ∈ B, ∀ δ ∈ D, Formula.untl δ (Formula.and β xi) ∈ A := by
    intro β hβ δ hδ
    exact h_burgessR_conj' β hβ δ hδ
  have h_r3_DC_ABD : burgessR3 A (deductiveClosure ({xi} ∪ B)) D :=
    dc_delta_B_burgessR3 h_mcs_A h_D_mcs h_B_dcs h_r3_ABD h_until_conj h_snce_conj_xi_D
  have h_DC_cud : ClosedUnderDerivation (deductiveClosure ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation _
  obtain ⟨B', h_DC_sub_B', h_B'_max⟩ := burgessR3Maximal_extension_exists h_mcs_A h_D_mcs
    h_DC_cud h_r3_DC_ABD
  obtain ⟨B'', h_B_sub_B'', h_B''_max⟩ := burgessR3Maximal_extension_exists h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure _ (Set.mem_union_right _ hφ)
  have h_B_sub_B' : B ⊆ B' := Set.Subset.trans h_B_sub_DC h_DC_sub_B'
  have h_xi_in_DC : xi ∈ deductiveClosure ({xi} ∪ B) :=
    subset_deductiveClosure _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B' : xi ∈ B' := h_DC_sub_B' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_B', h_B_sub_D,
    h_B_sub_B'', h_xi_in_B'⟩

/-! ## Lemma 2.8: Until-Formula Splitting (Variant) -/

/-- **Lemma 2.8 seed consistency**: Same seed as Lemma 2.7 but with
¬(eta ∨ (xi ∧ untl(xi, eta))) ∈ C instead of xi ∉ B. -/
theorem lemma_2_8_seed_consistent {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : (eta U xi) ∈ A)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.untl eta xi))).neg ∈ C) :
    Temporal.SetConsistent (lemma_2_7_seed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  set γ' := (Formula.or eta (Formula.and xi (Formula.untl eta xi))).neg with γ'_def
  have h_γ'_to_neg_eta : DerivationTree FrameClass.Base [] (γ'.imp eta.neg) :=
    impTrans (demorganDisjNegForward eta (Formula.and xi (Formula.untl eta xi)))
      (lceImp eta.neg (Formula.and xi (Formula.untl eta xi)).neg)
  have h_γ'_to_neg_chi : DerivationTree FrameClass.Base [] (γ'.imp (Formula.and xi (Formula.untl eta xi)).neg) :=
    impTrans (demorganDisjNegForward eta (Formula.and xi (Formula.untl eta xi)))
      (rceImp eta.neg (Formula.and xi (Formula.untl eta xi)).neg)
  have h_bx5_xe := self_accum_until_mcs h_mcs_A xi eta h_until
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B)
      (γ_hat : Formula Atom) (hγ : γ_hat ∈ C) (h_γ_to_γ' : DerivationTree FrameClass.Base [] (γ_hat.imp γ'))
      (alpha_list : List (Formula Atom)) (h_alphas : ∀ α ∈ alpha_list, α ∈ A),
      Σ' (event : Formula Atom),
        (𝐅event) ∈ A ×'
        DerivationTree FrameClass.Base [] (event.imp b) ×'
        DerivationTree FrameClass.Base [] (event.imp eta) ×'
        DerivationTree FrameClass.Base [] (event.imp (Formula.untl γ_hat b)) ×'
        (∀ α ∈ alpha_list, DerivationTree FrameClass.Base [] (event.imp (Formula.snce α (Formula.and b (Formula.and xi (Formula.untl eta xi)))))) by
    intro L hL ⟨d⟩
    let b_list_raw := (l27_collect_guards h_B_dcs xi eta L hL).val
    have hb_list : ∀ g ∈ b_list_raw, g ∈ B := (l27_collect_guards h_B_dcs xi eta L hL).property
    let a_list := l27_a_event_list xi eta L hL
    have ha_list : ∀ α ∈ a_list, α ∈ A := fun α hα => l27_a_event_list_mem hα
    let b_list_full := (Formula.bot.imp Formula.bot) :: b_list_raw
    have hb_list_full : ∀ g ∈ b_list_full, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact cud_contains_theorems h_B_dcs (identity' (Formula.bot : Formula Atom))
      · exact hb_list g h
    let b := listConj b_list_full
    let γ_hat := γ'
    have hb_B : b ∈ B := list_conj_mem_dcs h_B_dcs b_list_full hb_list_full
    have hγ_C : γ_hat ∈ C := h_neg_disj
    have h_γhat_to_γ' : DerivationTree FrameClass.Base [] (γ_hat.imp γ') := identity' γ'
    obtain ⟨event, h_F_event, h_ev_b, h_ev_eta, _h_ev_untl, h_ev_snce⟩ :=
      h_key b hb_B γ_hat hγ_C h_γhat_to_γ' a_list ha_list
    let χ_gen := Formula.and xi (Formula.untl eta xi)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree FrameClass.Base [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_raw : φ ∈ b_list_raw := l27_collect_guards_mem_of_B h_B_dcs xi eta L hL φ hφ h_B_case
        have h_φ_in_b : φ ∈ b_list_full := List.mem_cons.mpr (Or.inr h_φ_in_raw)
        have h_b_to_φ : DerivationTree FrameClass.Base [] (b.imp φ) := listConjImpliesElem b_list_full φ h_φ_in_b
        have h_ev_to_φ : DerivationTree FrameClass.Base [] (event.imp φ) := impTrans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · by_cases h_snce5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce α (Formula.and β' xi)
          · let β' := Classical.choose h_snce5
            have hβ' : β' ∈ B := (Classical.choose_spec h_snce5).1
            let α' := Classical.choose (Classical.choose_spec h_snce5).2
            have hα' : α' ∈ A := (Classical.choose_spec (Classical.choose_spec h_snce5).2).1
            have h_eq : φ = Formula.snce α' (Formula.and β' xi) := (Classical.choose_spec (Classical.choose_spec h_snce5).2).2
            have h_φ_eq_snce5 : Formula.snce α' (Formula.and β' xi) ∈ L := by rw [←h_eq]; exact hφ
            rw [h_eq]
            by_cases h_snce5_B : Formula.snce α' (Formula.and β' xi) ∈ B
            · have h_in_raw := l27_collect_guards_mem_of_B h_B_dcs xi eta L hL (Formula.snce α' (Formula.and β' xi)) h_φ_eq_snce5 h_snce5_B
              have h_in_b : Formula.snce α' (Formula.and β' xi) ∈ b_list_full := List.mem_cons.mpr (Or.inr h_in_raw)
              have h_b_imp : DerivationTree FrameClass.Base [] (b.imp (Formula.snce α' (Formula.and β' xi))) :=
                listConjImpliesElem b_list_full (Formula.snce α' (Formula.and β' xi)) h_in_b
              have h_ev_imp := impTrans h_ev_b h_b_imp
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_ev_imp (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
            · have h_α'_in_a := @l27_a_event_list_α_mem_xi _ A B C xi eta L hL β' α' h_φ_eq_snce5 hβ' hα'
              have h_ev_snce_α' := h_ev_snce α' h_α'_in_a
              have h_β'_in_raw := l27_collect_guards_mem_of_snce_xi h_B_dcs xi eta L hL β' α' h_φ_eq_snce5 hβ' hα' h_snce5_B
              have h_β'_in_b : β' ∈ b_list_full := List.mem_cons.mpr (Or.inr h_β'_in_raw)
              have h_b_to_β' : DerivationTree FrameClass.Base [] (b.imp β') := listConjImpliesElem b_list_full β' h_β'_in_b
              have h_bχ_to_β'xi : DerivationTree FrameClass.Base [] ((Formula.and b χ_gen).imp (Formula.and β' xi)) := by
                have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp b χ_gen) h_b_to_β'
                have h2 : DerivationTree FrameClass.Base [] _ := impTrans (rceImp b χ_gen) (lceImp xi (Formula.untl eta xi))
                exact combineImpConj h1 h2
              have h_mono := snceLeftMonoDeriv (Formula.and b χ_gen) α' (Formula.and β' xi) h_bχ_to_β'xi
              have h_chain := impTrans h_ev_snce_α' h_mono
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp [lemma_2_7_seed, h_B_case, h_eta, h_snce5] at h_φ_seed
    have d_event : DerivationTree FrameClass.Base [event] Formula.bot :=
      derivationFromImplied [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_F_mem h_mcs_A event h_F_event
    exact inconsistent_singleton_false h_event_cons d_event
  -- Prove h_key: BX5+BX7+BX13 chain with D1/D2 eliminated via γ'
  intro b hb γ_hat hγ h_γ_to_γ' alpha_list h_alphas
  have h_untl_bg : (γ_hat U b) ∈ A := h_r3.1 b hb γ_hat hγ
  have h_bx5_bg := self_accum_until_mcs h_mcs_A b γ_hat h_untl_bg
  let φ_gen := Formula.and b (Formula.untl γ_hat b)
  let χ_gen := Formula.and xi (Formula.untl eta xi)
  have h_bx7_gen := linear_until_mcs h_mcs_A φ_gen γ_hat χ_gen eta h_bx5_bg h_bx5_xe
  have h_D3_gen : Formula.untl (Formula.and φ_gen eta) (Formula.and φ_gen χ_gen) ∈ A := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_event_to_bot : DerivationTree FrameClass.Base [] ((Formula.and γ_hat eta).imp Formula.bot) := by
        have h1 : DerivationTree FrameClass.Base [] ((Formula.and γ_hat eta).imp eta.neg) :=
          impTrans (lceImp γ_hat eta) (impTrans h_γ_to_γ' h_γ'_to_neg_eta)
        have h2 : DerivationTree FrameClass.Base [] _ := rceImp γ_hat eta
        let PConj := Formula.and γ_hat eta
        have d1 : DerivationTree FrameClass.Base [PConj] eta.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree FrameClass.Base [PConj] eta := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_F_bot := F_mono_mcs h_mcs_A h_event_to_bot (until_implies_F_in_mcs h_mcs_A h_D1)
      have h_G_top : Formula.allFuture (Formula.bot.imp Formula.bot) ∈ A :=
        theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ (identity' (Formula.bot : Formula Atom)))
      exact someFuture_allFuture_neg_absurd h_mcs_A Formula.bot h_F_bot h_G_top
    · exfalso
      have h_event_to_bot : DerivationTree FrameClass.Base [] ((Formula.and γ_hat χ_gen).imp Formula.bot) := by
        have h1 : DerivationTree FrameClass.Base [] ((Formula.and γ_hat χ_gen).imp χ_gen.neg) :=
          impTrans (lceImp γ_hat χ_gen) (impTrans h_γ_to_γ' h_γ'_to_neg_chi)
        have h2 : DerivationTree FrameClass.Base [] _ := rceImp γ_hat χ_gen
        let PConj := Formula.and γ_hat χ_gen
        have d1 : DerivationTree FrameClass.Base [PConj] χ_gen.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree FrameClass.Base [PConj] χ_gen := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_F_bot := F_mono_mcs h_mcs_A h_event_to_bot (until_implies_F_in_mcs h_mcs_A h_D2)
      have h_G_top : Formula.allFuture (Formula.bot.imp Formula.bot) ∈ A :=
        theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ (identity' (Formula.bot : Formula Atom)))
      exact someFuture_allFuture_neg_absurd h_mcs_A Formula.bot h_F_bot h_G_top
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichment h_mcs_A guard alpha_list h_alphas base_event h_D3_gen
  let event := evt.event'
  have h_F_event : (𝐅event) ∈ A := until_implies_F_in_mcs h_mcs_A evt.h_untl
  have h_ev_base := evt.h_impl
  have h_ev_b : DerivationTree FrameClass.Base [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.untl γ_hat b)))
  have h_ev_eta : DerivationTree FrameClass.Base [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_untl : DerivationTree FrameClass.Base [] (event.imp (Formula.untl γ_hat b)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.untl γ_hat b)))
  have h_ev_snce : ∀ α ∈ alpha_list,
      DerivationTree FrameClass.Base [] (event.imp (Formula.snce α (Formula.and b χ_gen))) := by
    intro α hα
    have h_snce_guard := evt.h_snce α hα
    have h_guard_to_bχ : DerivationTree FrameClass.Base [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.untl γ_hat b))
      have h2 : DerivationTree FrameClass.Base [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_snce_guard (snceLeftMonoDeriv guard α (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_F_event, h_ev_b, h_ev_eta, h_ev_untl, h_ev_snce⟩

/-- **Lemma 2.8**: Given BurgessR3Maximal(A, B, C) with untl(xi, eta) ∈ A and
¬(eta ∨ (xi ∧ untl(xi, eta))) ∈ C, construct splitting. -/
theorem lemma_2_8 {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : (eta U xi) ∈ A)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.untl eta xi))).neg ∈ C) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal A B' D ∧
      BurgessR3Maximal D B'' C ∧
      Temporal.SetMaximalConsistent D ∧
      eta ∈ D ∧
      B ⊆ D ∧
      B ⊆ B' ∧
      B ⊆ B'' ∧
      xi ∈ B' := by
  have h_seed_cons := lemma_2_8_seed_consistent h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_until h_neg_disj
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma_2_7_seed A B C xi eta; simp [lemma_2_7_seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma_2_7_seed A B C xi eta; simp [lemma_2_7_seed, hφ]
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, (γ U β) ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, (α S β) ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  have h_snce_conj_xi_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce α (Formula.and β xi) ∈ D := by
    intro β hβ α hα; apply h_sup
    show Formula.snce α (Formula.and β xi) ∈ lemma_2_7_seed A B C xi eta
    simp only [lemma_2_7_seed, Set.mem_union, Set.mem_setOf_eq]; right; exact ⟨β, hβ, α, hα, rfl⟩
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (identity' (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_snce_xi_D : ∀ α ∈ A, (α S xi) ∈ D := by
    intro α hα
    exact snce_left_mono_thm h_D_mcs (rceImp β₀ xi) (h_snce_conj_xi_D β₀ hβ₀ α hα)
  have h_burgessRSince_xi : burgessRSince D xi A := h_snce_xi_D
  have h_burgessR_xi : burgessR A xi D :=
    burgessRSince_implies_burgessR h_mcs_A h_D_mcs h_burgessRSince_xi
  have h_burgessR_conj' : ∀ β ∈ B, burgessR A (Formula.and β xi) D := by
    intro β hβ
    exact burgessR_conj h_mcs_A (h_rSet_A β hβ) h_burgessR_xi
  have h_until_conj : ∀ β ∈ B, ∀ δ ∈ D, Formula.untl δ (Formula.and β xi) ∈ A := by
    intro β hβ δ hδ; exact h_burgessR_conj' β hβ δ hδ
  have h_r3_DC_ABD : burgessR3 A (deductiveClosure ({xi} ∪ B)) D :=
    dc_delta_B_burgessR3 h_mcs_A h_D_mcs h_B_dcs h_r3_ABD h_until_conj h_snce_conj_xi_D
  have h_DC_cud : ClosedUnderDerivation (deductiveClosure ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation _
  obtain ⟨B', h_DC_sub_B', h_B'_max⟩ := burgessR3Maximal_extension_exists h_mcs_A h_D_mcs
    h_DC_cud h_r3_DC_ABD
  obtain ⟨B'', h_B_sub_B'', h_B''_max⟩ := burgessR3Maximal_extension_exists h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure _ (Set.mem_union_right _ hφ)
  have h_B_sub_B' : B ⊆ B' := Set.Subset.trans h_B_sub_DC h_DC_sub_B'
  have h_xi_in_DC : xi ∈ deductiveClosure ({xi} ∪ B) :=
    subset_deductiveClosure _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B' : xi ∈ B' := h_DC_sub_B' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_D, h_B_sub_B',
    h_B_sub_B'', h_xi_in_B'⟩

/-! ## Lemma 2.4 with Guard (Enriched Version) -/

/-- **Lemma 2.4 with guard**: Strengthened version of lemma_2_4 that additionally
returns γ ∈ B (guard membership in the interval DCS). -/
noncomputable def lemma_2_4_with_guard {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : (β U γ) ∈ A) :
    ∃ B C : Set (Formula Atom), Temporal.SetMaximalConsistent C ∧
      β ∈ C ∧ gContent A ⊆ C ∧
      BurgessR3Maximal A B C ∧
      γ ∈ B := by
  obtain ⟨B₀, C, h_C_mcs, h_β_C, h_g_sub, _, h_R3M₀⟩ := lemma_2_4 h_mcs γ β h_until
  -- Check if γ is already in B₀
  by_cases h_γ_B₀ : γ ∈ B₀
  · exact ⟨B₀, C, h_C_mcs, h_β_C, h_g_sub, h_R3M₀, h_γ_B₀⟩
  · -- γ ∉ B₀: use lemma_2_7 to split and get B' with γ ∈ B'.
    obtain ⟨B', D, B'', h_R3M_AB'D, _, h_D_mcs, h_eta_D, h_B₀_sub_B', h_B₀_sub_D, _, h_γ_B'⟩ :=
      lemma_2_7 h_mcs h_C_mcs h_R3M₀ h_R3M₀.1 h_g_sub γ β h_until h_γ_B₀
    have h_g_sub_D : gContent A ⊆ D := by
      have h_gc_B₀ := g_content_sub h_mcs h_C_mcs h_R3M₀
      exact Set.Subset.trans h_gc_B₀ h_B₀_sub_D
    exact ⟨B', D, h_D_mcs, h_eta_D, h_g_sub_D, h_R3M_AB'D, h_γ_B'⟩

/-! ## Phase 4: Since-Direction Mirrors -/

/-- Since-direction seed: B ∪ {eta} ∪ {untl(γ, β∧xi) | β∈B, γ∈C}. -/
def lemma_2_7_since_seed (_A B C : Set (Formula Atom)) (xi eta : Formula Atom) : Set (Formula Atom) :=
  B ∪ {eta} ∪ {φ | ∃ β ∈ B, ∃ γ ∈ C, φ = Formula.untl γ (Formula.and β xi)}

/-- Extract γ' events from component 3 elements of a list. -/
noncomputable def l27s_c5_event_list (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  L.filterMap (fun φ => by
    classical
    exact if h : ∃ β' ∈ B, ∃ γ ∈ C, φ = Formula.untl γ (Formula.and β' xi) then
      some (Classical.choose (Classical.choose_spec h).2)
    else none)

/-- Elements of l27s_c5_event_list are in C. -/
theorem l27s_c5_event_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {γ : Formula Atom} (hγ : γ ∈ l27s_c5_event_list B C xi L) : γ ∈ C := by
  unfold l27s_c5_event_list at hγ
  simp [List.mem_filterMap] at hγ
  obtain ⟨φ, _, hγ_eq⟩ := hγ
  by_cases h : ∃ β' ∈ B, ∃ γ' ∈ C, φ = Formula.untl γ' (Formula.and β' xi)
  · simp [h] at hγ_eq; subst hγ_eq
    exact (Classical.choose_spec (Classical.choose_spec h).2).1
  · simp [h] at hγ_eq

/-- Extract β' guards from component 3 elements. -/
noncomputable def l27s_b5_guard_list (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  L.filterMap (fun φ => by
    classical
    exact if h : ∃ β' ∈ B, ∃ γ ∈ C, φ = Formula.untl γ (Formula.and β' xi) then
      some (Classical.choose h)
    else none)

/-- Elements of l27s_b5_guard_list are in B. -/
theorem l27s_b5_guard_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β : Formula Atom} (hβ : β ∈ l27s_b5_guard_list B C xi L) : β ∈ B := by
  unfold l27s_b5_guard_list at hβ
  simp [List.mem_filterMap] at hβ
  obtain ⟨φ, _, hβ_eq⟩ := hβ
  by_cases h : ∃ β' ∈ B, ∃ γ' ∈ C, φ = Formula.untl γ' (Formula.and β' xi)
  · simp [h] at hβ_eq; subst hβ_eq
    exact (Classical.choose_spec h).1
  · simp [h] at hβ_eq

/-- For a component 3 element, the extracted γ' is in c5_event_list. -/
theorem l27s_c5_γ_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl γ' (Formula.and β' xi) ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    γ' ∈ l27s_c5_event_list B C xi L := by
  unfold l27s_c5_event_list
  simp only [List.mem_filterMap]
  refine ⟨Formula.untl γ' (Formula.and β' xi), hφ, ?_⟩
  have h : ∃ β'' ∈ B, ∃ γ'' ∈ C, Formula.untl γ' (Formula.and β' xi) =
      Formula.untl γ'' (Formula.and β'' xi) := ⟨β', hβ', γ', hγ', rfl⟩
  simp only [h, ↓reduceDIte]
  have h_spec := (Classical.choose_spec (Classical.choose_spec h).2)
  exact congr_arg some (Formula.untl.inj h_spec.2).1.symm

/-- For a component 3 element, the extracted β' is in b5_guard_list. -/
theorem l27s_b5_β_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl γ' (Formula.and β' xi) ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    β' ∈ l27s_b5_guard_list B C xi L := by
  unfold l27s_b5_guard_list
  simp only [List.mem_filterMap]
  refine ⟨Formula.untl γ' (Formula.and β' xi), hφ, ?_⟩
  have h : ∃ β'' ∈ B, ∃ γ'' ∈ C, Formula.untl γ' (Formula.and β' xi) =
      Formula.untl γ'' (Formula.and β'' xi) := ⟨β', hβ', γ', hγ', rfl⟩
  simp only [h, ↓reduceDIte]
  have h_spec := Classical.choose_spec h
  obtain ⟨_, γ'', _, h_formula_eq⟩ := h_spec
  have h_inj := Formula.untl.inj h_formula_eq
  simp only [Formula.and] at h_inj
  exact congr_arg some ((Formula.imp.inj (Formula.imp.inj h_inj.2).1).1).symm

/-- Since-direction seed consistency. Uses BX5'+BX7'+BX13' chain. -/
theorem lemma_2_7_since_seed_consistent {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : (eta S xi) ∈ C)
    (h_xi_not_B : xi ∉ B) :
    Temporal.SetConsistent (lemma_2_7_since_seed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  have h_not_r3_xi := BurgessR3Maximal_extension_fails h_r3m h_xi_not_B
  have h_neg_since_exists : ∃ beta0 ∈ B, ∃ alpha0 ∈ A,
      Formula.snce alpha0 (Formula.and beta0 xi) ∉ C := by
    by_contra h_all_since
    push Not at h_all_since
    have h_rset : burgessRSet A (deductiveClosure ({xi} ∪ B)) C := by
      intro phi hphi gamma hgamma
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨h_impl⟩⟩
      · exact h_r3.1 phi h_B_case gamma hgamma
      · have h_burgessRSince_ext : burgessRSince C (Formula.and beta_w xi) A :=
          fun alpha halpha => h_all_since beta_w hbeta_w alpha halpha
        have h_burgessR_ext := burgessRSince_implies_burgessR h_mcs_A h_mcs_C h_burgessRSince_ext
        exact untl_left_mono_thm h_mcs_A h_impl (h_burgessR_ext gamma hgamma)
    have h_rsince : burgessRSetSince C (deductiveClosure ({xi} ∪ B)) A := by
      intro phi hphi alpha halpha
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨h_impl⟩⟩
      · exact h_r3.2 phi h_B_case alpha halpha
      · exact snce_left_mono_thm h_mcs_C h_impl (h_all_since beta_w hbeta_w alpha halpha)
    exact h_not_r3_xi ⟨h_rset, h_rsince⟩
  obtain ⟨beta0, h_beta0, alpha0, h_alpha0, h_not_in_C⟩ := h_neg_since_exists
  have h_neg_since_in_C : (Formula.snce alpha0 (Formula.and beta0 xi)).neg ∈ C := by
    rcases temporal_negation_complete h_mcs_C
      (Formula.snce alpha0 (Formula.and beta0 xi)) with h | h
    · exfalso; exact h_not_in_C h
    · exact h
  intro L hL ⟨d⟩
  have h_bx5_xe := self_accum_since_mcs h_mcs_C xi eta h_since
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B) (h_b_beta0 : DerivationTree FrameClass.Base [] (b.imp beta0))
      (α_hat : Formula Atom) (hα : α_hat ∈ A) (h_α_alpha0 : DerivationTree FrameClass.Base [] (α_hat.imp alpha0))
      (gamma_list : List (Formula Atom)) (h_gammas : ∀ γ ∈ gamma_list, γ ∈ C),
      Σ' (event : Formula Atom),
        (𝐏event) ∈ C ×'
        DerivationTree FrameClass.Base [] (event.imp b) ×'
        DerivationTree FrameClass.Base [] (event.imp eta) ×'
        DerivationTree FrameClass.Base [] (event.imp (Formula.snce α_hat b)) ×'
        (∀ γ ∈ gamma_list, DerivationTree FrameClass.Base [] (event.imp (Formula.untl γ (Formula.and b (Formula.and xi (Formula.snce eta xi)))))) by
    let b_list_5 := l27s_b5_guard_list B C xi L
    have hb_list_5 : ∀ g ∈ b_list_5, g ∈ B := fun g hg => l27s_b5_guard_list_mem hg
    let c_list := l27s_c5_event_list B C xi L
    have hc_list : ∀ γ ∈ c_list, γ ∈ C := fun γ hγ => l27s_c5_event_list_mem hγ
    haveI : DecidablePred (· ∈ B) := fun _ => Classical.dec _
    let b_list_B := L.filter (· ∈ B)
    have hb_list_B : ∀ g ∈ b_list_B, g ∈ B := by
      intro g hg; exact decide_eq_true_eq.mp (List.mem_filter.mp hg).2
    let b_list := beta0 :: (b_list_B ++ b_list_5)
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact h_beta0
      · rcases List.mem_append.mp h with h1 | h2
        · exact hb_list_B g h1
        · exact hb_list_5 g h2
    let a_list : List (Formula Atom) := [alpha0]
    have ha_list : ∀ α ∈ a_list, α ∈ A := by
      intro α hα; simp [a_list] at hα; subst hα; exact h_alpha0
    let b := listConj b_list
    let α_hat := listConj a_list
    have hb_B : b ∈ B := list_conj_mem_dcs h_B_dcs b_list hb_list'
    have hα_A : α_hat ∈ A := list_conj_mem_mcs h_mcs_A a_list ha_list
    have h_b_to_beta0 : DerivationTree FrameClass.Base [] (b.imp beta0) :=
      listConjImpliesElem b_list beta0 (List.mem_cons.mpr (Or.inl rfl))
    have h_α_to_alpha0 : DerivationTree FrameClass.Base [] (α_hat.imp alpha0) :=
      listConjImpliesElem a_list alpha0 (by simp [a_list])
    obtain ⟨event, h_P_event, h_ev_b, h_ev_eta, _h_ev_snce, h_ev_untl⟩ :=
      h_key b hb_B h_b_to_beta0 α_hat hα_A h_α_to_alpha0 c_list hc_list
    let χ_gen := Formula.and xi (Formula.snce eta xi)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree FrameClass.Base [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_B_list : φ ∈ b_list_B :=
          List.mem_filter.mpr ⟨hφ, decide_eq_true_eq.mpr h_B_case⟩
        have h_φ_in_b : φ ∈ b_list :=
          List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h_φ_in_B_list)))
        have h_b_to_φ := listConjImpliesElem b_list φ h_φ_in_b
        have h_ev_to_φ := impTrans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · by_cases h_comp5 : ∃ β' ∈ B, ∃ γ' ∈ C, φ = Formula.untl γ' (Formula.and β' xi)
          · let β' := Classical.choose h_comp5
            have hβ' : β' ∈ B := (Classical.choose_spec h_comp5).1
            let γ' := Classical.choose (Classical.choose_spec h_comp5).2
            have hγ' : γ' ∈ C :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).1
            have h_eq : φ = Formula.untl γ' (Formula.and β' xi) :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).2
            rw [h_eq]
            have h_φ_eq : Formula.untl γ' (Formula.and β' xi) ∈ L := by
              rw [← h_eq]; exact hφ
            have h_β'_in_5 := l27s_b5_β_mem h_φ_eq hβ' hγ'
            have h_β'_in_b : β' ∈ b_list :=
              List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h_β'_in_5)))
            have h_b_to_β' := listConjImpliesElem b_list β' h_β'_in_b
            have h_γ'_in_c := l27s_c5_γ_mem h_φ_eq hβ' hγ'
            have h_ev_untl_γ' := h_ev_untl γ' h_γ'_in_c
            have h_bχ_to_β'xi : DerivationTree FrameClass.Base [] ((Formula.and b χ_gen).imp
                (Formula.and β' xi)) := by
              have h1 := impTrans (lceImp b χ_gen) h_b_to_β'
              have h2 : DerivationTree FrameClass.Base [] ((Formula.and b χ_gen).imp xi) :=
                impTrans (rceImp b χ_gen) (lceImp xi (Formula.snce eta xi))
              exact combineImpConj h1 h2
            have h_left := untlLeftMonoDeriv (Formula.and b χ_gen) γ'
              (Formula.and β' xi) h_bχ_to_β'xi
            have h_chain := impTrans h_ev_untl_γ' h_left
            exact DerivationTree.modus_ponens _ _ _
              (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
              (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp only [lemma_2_7_since_seed, Set.mem_union, Set.mem_setOf_eq,
              Set.mem_singleton_iff] at h_φ_seed
            rcases h_φ_seed with ((h1 | h2) | h5)
            · exact h_B_case h1
            · exact h_eta h2
            · exact h_comp5 h5
    have d_event : DerivationTree FrameClass.Base [event] Formula.bot :=
      derivationFromImplied [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_P_mem h_mcs_C event h_P_event
    exact inconsistent_singleton_false h_event_cons d_event
  -- Prove h_key: BX5'+BX7'+BX13' chain.
  intro b hb h_b_beta0 α_hat hα h_α_alpha0 gamma_list h_gammas
  have h_snce_ba : (α_hat S b) ∈ C := h_r3.2 b hb α_hat hα
  have h_bx5_ba := self_accum_since_mcs h_mcs_C b α_hat h_snce_ba
  let φ_gen := Formula.and b (Formula.snce α_hat b)
  let χ_gen := Formula.and xi (Formula.snce eta xi)
  have h_bx7_gen := linear_since_mcs h_mcs_C φ_gen α_hat χ_gen eta h_bx5_ba h_bx5_xe
  have h_guard_to_b0xi : DerivationTree FrameClass.Base [] ((Formula.and φ_gen χ_gen).imp (Formula.and beta0 xi)) := by
    have h1 : DerivationTree FrameClass.Base [] _ := impTrans (impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.snce α_hat b))) h_b_beta0
    have h2 : DerivationTree FrameClass.Base [] _ := impTrans (rceImp φ_gen χ_gen) (lceImp xi (Formula.snce eta xi))
    exact combineImpConj h1 h2
  have h_guard_to_alpha0 : DerivationTree FrameClass.Base [] ((Formula.and α_hat eta).imp alpha0) :=
    impTrans (lceImp α_hat eta) h_α_alpha0
  have h_D3_gen : Formula.snce (Formula.and φ_gen eta) (Formula.and φ_gen χ_gen) ∈ C := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_rm : DerivationTree FrameClass.Base [] ((Formula.and α_hat eta).imp alpha0) := h_guard_to_alpha0
      have h_contra := right_mono_since_mcs h_mcs_C h_rm
        (snce_left_mono_thm h_mcs_C h_guard_to_b0xi h_D1)
      exact mcs_not_mem_of_neg h_mcs_C h_neg_since_in_C h_contra
    · exfalso
      have h_rm : DerivationTree FrameClass.Base [] ((Formula.and α_hat χ_gen).imp alpha0) :=
        impTrans (lceImp α_hat χ_gen) h_α_alpha0
      have h_contra := right_mono_since_mcs h_mcs_C h_rm
        (snce_left_mono_thm h_mcs_C h_guard_to_b0xi h_D2)
      exact mcs_not_mem_of_neg h_mcs_C h_neg_since_in_C h_contra
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichmentSince h_mcs_C guard gamma_list h_gammas base_event h_D3_gen
  let event := evt.event'
  have h_P_event : (𝐏event) ∈ C := since_implies_P_in_mcs h_mcs_C evt.h_snce
  have h_ev_base := evt.h_impl
  have h_ev_b : DerivationTree FrameClass.Base [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.snce α_hat b)))
  have h_ev_eta : DerivationTree FrameClass.Base [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_snce_ba : DerivationTree FrameClass.Base [] (event.imp (Formula.snce α_hat b)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.snce α_hat b)))
  have h_ev_untl : ∀ γ ∈ gamma_list,
      DerivationTree FrameClass.Base [] (event.imp (Formula.untl γ (Formula.and b χ_gen))) := by
    intro γ hγ
    have h_untl_guard := evt.h_untl γ hγ
    have h_guard_to_bχ : DerivationTree FrameClass.Base [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.snce α_hat b))
      have h2 : DerivationTree FrameClass.Base [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_untl_guard (untlLeftMonoDeriv guard γ (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_P_event, h_ev_b, h_ev_eta, h_ev_snce_ba, h_ev_untl⟩

/-- **Lemma 2.7 (Since direction)**: Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and xi ∉ B, construct MCS D with eta ∈ D splitting the R3 pair.
Returns xi ∈ B'' via DC(B ∪ {xi}) Zorn seed. -/
theorem lemma_2_7_since {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : (eta S xi) ∈ C)
    (h_xi_not_B : xi ∉ B) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal A B' D ∧
      BurgessR3Maximal D B'' C ∧
      Temporal.SetMaximalConsistent D ∧
      eta ∈ D ∧
      B ⊆ B' ∧
      B ⊆ D ∧
      B ⊆ B'' ∧
      xi ∈ B'' := by
  have h_seed_cons := lemma_2_7_since_seed_consistent h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_since h_xi_not_B
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma_2_7_since_seed A B C xi eta
    simp [lemma_2_7_since_seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma_2_7_since_seed A B C xi eta; simp [lemma_2_7_since_seed, hφ]
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, (γ U β) ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, (α S β) ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  have h_untl_conj_xi_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl γ (Formula.and β xi) ∈ D := by
    intro β hβ γ hγ; apply h_sup
    show Formula.untl γ (Formula.and β xi) ∈ lemma_2_7_since_seed A B C xi eta
    simp only [lemma_2_7_since_seed, Set.mem_union, Set.mem_setOf_eq]
    right; exact ⟨β, hβ, γ, hγ, rfl⟩
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (identity' (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_untl_xi_D : ∀ γ ∈ C, (γ U xi) ∈ D := by
    intro γ hγ
    exact untl_left_mono_thm h_D_mcs (rceImp β₀ xi) (h_untl_conj_xi_D β₀ hβ₀ γ hγ)
  have h_burgessR_xi : burgessR D xi C := h_untl_xi_D
  have h_burgessRSince_xi : burgessRSince C xi D :=
    burgessR_implies_burgessRSince h_D_mcs h_mcs_C h_burgessR_xi
  have h_burgessR_conj' : ∀ β ∈ B, burgessR D (Formula.and β xi) C := by
    intro β hβ
    exact burgessR_conj h_D_mcs (h_rSet_D β hβ) h_burgessR_xi
  have h_snce_conj_xi_C : ∀ β ∈ B, ∀ δ ∈ D, Formula.snce δ (Formula.and β xi) ∈ C := by
    intro β hβ δ hδ
    have h_rSince := burgessRSince_conj h_mcs_C (h_rSetSince_D β hβ) h_burgessRSince_xi
    exact h_rSince δ hδ
  have h_r3_DC_DBC : burgessR3 D (deductiveClosure ({xi} ∪ B)) C :=
    dc_delta_B_burgessR3 h_D_mcs h_mcs_C h_B_dcs h_r3_DBC h_untl_conj_xi_D h_snce_conj_xi_C
  have h_DC_cud : ClosedUnderDerivation (deductiveClosure ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation _
  obtain ⟨B', h_B_sub_B', h_B'_max⟩ := burgessR3Maximal_extension_exists h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_DC_sub_B'', h_B''_max⟩ := burgessR3Maximal_extension_exists h_D_mcs h_mcs_C
    h_DC_cud h_r3_DC_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure _ (Set.mem_union_right _ hφ)
  have h_B_sub_B'' : B ⊆ B'' := Set.Subset.trans h_B_sub_DC h_DC_sub_B''
  have h_xi_in_DC : xi ∈ deductiveClosure ({xi} ∪ B) :=
    subset_deductiveClosure _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B'' : xi ∈ B'' := h_DC_sub_B'' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_B', h_B_sub_D,
    h_B_sub_B'', h_xi_in_B''⟩

/-- **Lemma 2.8 (Since direction) seed consistency**: Same seed as lemma_2_7_since
but with ¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A instead of xi ∉ B. -/
theorem lemma_2_8_since_seed_consistent {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : (eta S xi) ∈ C)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.snce eta xi))).neg ∈ A) :
    Temporal.SetConsistent (lemma_2_7_since_seed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  set α' := (Formula.or eta (Formula.and xi (Formula.snce eta xi))).neg with α'_def
  have h_α'_to_neg_eta : DerivationTree FrameClass.Base [] (α'.imp eta.neg) :=
    impTrans (demorganDisjNegForward eta (Formula.and xi (Formula.snce eta xi)))
      (lceImp eta.neg (Formula.and xi (Formula.snce eta xi)).neg)
  have h_α'_to_neg_chi : DerivationTree FrameClass.Base [] (α'.imp (Formula.and xi (Formula.snce eta xi)).neg) :=
    impTrans (demorganDisjNegForward eta (Formula.and xi (Formula.snce eta xi)))
      (rceImp eta.neg (Formula.and xi (Formula.snce eta xi)).neg)
  have h_bx5_xe := self_accum_since_mcs h_mcs_C xi eta h_since
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B)
      (α_hat : Formula Atom) (hα : α_hat ∈ A) (h_α_to_α' : DerivationTree FrameClass.Base [] (α_hat.imp α'))
      (gamma_list : List (Formula Atom)) (h_gammas : ∀ γ ∈ gamma_list, γ ∈ C),
      Σ' (event : Formula Atom),
        (𝐏event) ∈ C ×'
        DerivationTree FrameClass.Base [] (event.imp b) ×'
        DerivationTree FrameClass.Base [] (event.imp eta) ×'
        DerivationTree FrameClass.Base [] (event.imp (Formula.snce α_hat b)) ×'
        (∀ γ ∈ gamma_list, DerivationTree FrameClass.Base [] (event.imp (Formula.untl γ (Formula.and b (Formula.and xi (Formula.snce eta xi)))))) by
    intro L hL ⟨d⟩
    haveI : DecidablePred (· ∈ B) := fun _ => Classical.dec _
    let b_list_5 := l27s_b5_guard_list B C xi L
    have hb_list_5 : ∀ g ∈ b_list_5, g ∈ B := fun g hg => l27s_b5_guard_list_mem hg
    let c_list := l27s_c5_event_list B C xi L
    have hc_list : ∀ γ ∈ c_list, γ ∈ C := fun γ hγ => l27s_c5_event_list_mem hγ
    let b_list_B := L.filter (· ∈ B)
    have hb_list_B : ∀ g ∈ b_list_B, g ∈ B := by
      intro g hg; exact decide_eq_true_eq.mp (List.mem_filter.mp hg).2
    let b_list := (Formula.bot.imp Formula.bot) :: (b_list_B ++ b_list_5)
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact cud_contains_theorems h_B_dcs (identity' (Formula.bot : Formula Atom))
      · rcases List.mem_append.mp h with h1 | h2
        · exact hb_list_B g h1
        · exact hb_list_5 g h2
    let a_list : List (Formula Atom) := [α']
    have ha_list : ∀ α_elem ∈ a_list, α_elem ∈ A := by
      intro α_elem hα_elem; simp [a_list] at hα_elem; subst hα_elem; exact h_neg_disj
    let b := listConj b_list
    let α_hat := listConj a_list
    have hb_B : b ∈ B := list_conj_mem_dcs h_B_dcs b_list hb_list'
    have hα_A : α_hat ∈ A := list_conj_mem_mcs h_mcs_A a_list ha_list
    have h_αhat_to_α' : DerivationTree FrameClass.Base [] (α_hat.imp α') :=
      listConjImpliesElem a_list α' (by simp [a_list])
    obtain ⟨event, h_P_event, h_ev_b, h_ev_eta, _h_ev_snce, h_ev_untl⟩ :=
      h_key b hb_B α_hat hα_A h_αhat_to_α' c_list hc_list
    let χ_gen := Formula.and xi (Formula.snce eta xi)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree FrameClass.Base [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_B_list : φ ∈ b_list_B :=
          List.mem_filter.mpr ⟨hφ, decide_eq_true_eq.mpr h_B_case⟩
        have h_φ_in_b : φ ∈ b_list :=
          List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h_φ_in_B_list)))
        have h_b_to_φ := listConjImpliesElem b_list φ h_φ_in_b
        have h_ev_to_φ := impTrans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta_case : φ = eta
        · subst h_eta_case
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · by_cases h_comp5 : ∃ β' ∈ B, ∃ γ' ∈ C, φ = Formula.untl γ' (Formula.and β' xi)
          · let β' := Classical.choose h_comp5
            have hβ' : β' ∈ B := (Classical.choose_spec h_comp5).1
            let γ' := Classical.choose (Classical.choose_spec h_comp5).2
            have hγ' : γ' ∈ C :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).1
            have h_eq : φ = Formula.untl γ' (Formula.and β' xi) :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).2
            rw [h_eq]
            have h_φ_eq : Formula.untl γ' (Formula.and β' xi) ∈ L := by
              rw [← h_eq]; exact hφ
            have h_β'_in_5 := l27s_b5_β_mem h_φ_eq hβ' hγ'
            have h_β'_in_b : β' ∈ b_list :=
              List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h_β'_in_5)))
            have h_b_to_β' := listConjImpliesElem b_list β' h_β'_in_b
            have h_γ'_in_c := l27s_c5_γ_mem h_φ_eq hβ' hγ'
            have h_ev_untl_γ' := h_ev_untl γ' h_γ'_in_c
            have h_bχ_to_β'xi : DerivationTree FrameClass.Base [] ((Formula.and b χ_gen).imp
                (Formula.and β' xi)) := by
              have h1 := impTrans (lceImp b χ_gen) h_b_to_β'
              have h2 : DerivationTree FrameClass.Base [] ((Formula.and b χ_gen).imp xi) :=
                impTrans (rceImp b χ_gen) (lceImp xi (Formula.snce eta xi))
              exact combineImpConj h1 h2
            have h_left := untlLeftMonoDeriv (Formula.and b χ_gen) γ'
              (Formula.and β' xi) h_bχ_to_β'xi
            have h_chain := impTrans h_ev_untl_γ' h_left
            exact DerivationTree.modus_ponens _ _ _
              (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
              (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp only [lemma_2_7_since_seed, Set.mem_union, Set.mem_setOf_eq,
              Set.mem_singleton_iff] at h_φ_seed
            rcases h_φ_seed with ((h1 | h2) | h5)
            · exact h_B_case h1
            · exact h_eta_case h2
            · exact h_comp5 h5
    have d_event : DerivationTree FrameClass.Base [event] Formula.bot :=
      derivationFromImplied [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_P_mem h_mcs_C event h_P_event
    exact inconsistent_singleton_false h_event_cons d_event
  -- Prove h_key: BX5'+BX7'+BX13' chain with D1/D2 eliminated via α'
  intro b hb α_hat hα h_α_to_α' gamma_list h_gammas
  have h_snce_ba : (α_hat S b) ∈ C := h_r3.2 b hb α_hat hα
  have h_bx5_ba := self_accum_since_mcs h_mcs_C b α_hat h_snce_ba
  let φ_gen := Formula.and b (Formula.snce α_hat b)
  let χ_gen := Formula.and xi (Formula.snce eta xi)
  have h_bx7_gen := linear_since_mcs h_mcs_C φ_gen α_hat χ_gen eta h_bx5_ba h_bx5_xe
  have h_D3_gen : Formula.snce (Formula.and φ_gen eta) (Formula.and φ_gen χ_gen) ∈ C := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_event_to_bot : DerivationTree FrameClass.Base [] ((Formula.and α_hat eta).imp Formula.bot) := by
        have h1 : DerivationTree FrameClass.Base [] ((Formula.and α_hat eta).imp eta.neg) :=
          impTrans (lceImp α_hat eta) (impTrans h_α_to_α' h_α'_to_neg_eta)
        have h2 : DerivationTree FrameClass.Base [] _ := rceImp α_hat eta
        let PConj := Formula.and α_hat eta
        have d1 : DerivationTree FrameClass.Base [PConj] eta.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree FrameClass.Base [PConj] eta := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_P_bot := P_mono_mcs h_mcs_C h_event_to_bot (since_implies_P_in_mcs h_mcs_C h_D1)
      have h_H_top : Formula.allPast (Formula.bot.imp Formula.bot) ∈ C :=
        theoremInMcs h_mcs_C (pastNecessitation _ (identity' (Formula.bot : Formula Atom)))
      exact somePast_allPast_neg_absurd h_mcs_C Formula.bot h_P_bot h_H_top
    · exfalso
      have h_event_to_bot : DerivationTree FrameClass.Base [] ((Formula.and α_hat χ_gen).imp Formula.bot) := by
        have h1 : DerivationTree FrameClass.Base [] ((Formula.and α_hat χ_gen).imp χ_gen.neg) :=
          impTrans (lceImp α_hat χ_gen) (impTrans h_α_to_α' h_α'_to_neg_chi)
        have h2 : DerivationTree FrameClass.Base [] _ := rceImp α_hat χ_gen
        let PConj := Formula.and α_hat χ_gen
        have d1 : DerivationTree FrameClass.Base [PConj] χ_gen.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree FrameClass.Base [PConj] χ_gen := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_P_bot := P_mono_mcs h_mcs_C h_event_to_bot (since_implies_P_in_mcs h_mcs_C h_D2)
      have h_H_top : Formula.allPast (Formula.bot.imp Formula.bot) ∈ C :=
        theoremInMcs h_mcs_C (pastNecessitation _ (identity' (Formula.bot : Formula Atom)))
      exact somePast_allPast_neg_absurd h_mcs_C Formula.bot h_P_bot h_H_top
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichmentSince h_mcs_C guard gamma_list h_gammas base_event h_D3_gen
  let event := evt.event'
  have h_P_event : (𝐏event) ∈ C := since_implies_P_in_mcs h_mcs_C evt.h_snce
  have h_ev_base := evt.h_impl
  have h_ev_b : DerivationTree FrameClass.Base [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.snce α_hat b)))
  have h_ev_eta : DerivationTree FrameClass.Base [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_snce_ba : DerivationTree FrameClass.Base [] (event.imp (Formula.snce α_hat b)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.snce α_hat b)))
  have h_ev_untl : ∀ γ ∈ gamma_list,
      DerivationTree FrameClass.Base [] (event.imp (Formula.untl γ (Formula.and b χ_gen))) := by
    intro γ hγ
    have h_untl_guard := evt.h_untl γ hγ
    have h_guard_to_bχ : DerivationTree FrameClass.Base [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree FrameClass.Base [] _ := impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.snce α_hat b))
      have h2 : DerivationTree FrameClass.Base [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_untl_guard (untlLeftMonoDeriv guard γ (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_P_event, h_ev_b, h_ev_eta, h_ev_snce_ba, h_ev_untl⟩

/-- **Lemma 2.8 (Since direction)**: Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and ¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A. -/
theorem lemma_2_8_since {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    (h_B_dcs : ClosedUnderDerivation B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : (eta S xi) ∈ C)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.snce eta xi))).neg ∈ A) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal A B' D ∧
      BurgessR3Maximal D B'' C ∧
      Temporal.SetMaximalConsistent D ∧
      eta ∈ D ∧
      B ⊆ D ∧
      B ⊆ B' ∧
      B ⊆ B'' ∧
      xi ∈ B'' := by
  have h_seed_cons := lemma_2_8_since_seed_consistent h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_since h_neg_disj
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma_2_7_since_seed A B C xi eta
    simp [lemma_2_7_since_seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma_2_7_since_seed A B C xi eta; simp [lemma_2_7_since_seed, hφ]
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, (γ U β) ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, (α S β) ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  have h_untl_conj_xi_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl γ (Formula.and β xi) ∈ D := by
    intro β hβ γ hγ; apply h_sup
    show Formula.untl γ (Formula.and β xi) ∈ lemma_2_7_since_seed A B C xi eta
    simp only [lemma_2_7_since_seed, Set.mem_union, Set.mem_setOf_eq]
    right; exact ⟨β, hβ, γ, hγ, rfl⟩
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (identity' (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_untl_xi_D : ∀ γ ∈ C, (γ U xi) ∈ D := by
    intro γ hγ
    exact untl_left_mono_thm h_D_mcs (rceImp β₀ xi) (h_untl_conj_xi_D β₀ hβ₀ γ hγ)
  have h_burgessR_xi : burgessR D xi C := h_untl_xi_D
  have h_burgessRSince_xi : burgessRSince C xi D :=
    burgessR_implies_burgessRSince h_D_mcs h_mcs_C h_burgessR_xi
  have h_snce_conj_xi_C : ∀ β ∈ B, ∀ δ ∈ D, Formula.snce δ (Formula.and β xi) ∈ C := by
    intro β hβ δ hδ
    exact (burgessRSince_conj h_mcs_C (h_rSetSince_D β hβ) h_burgessRSince_xi) δ hδ
  have h_r3_DC_DBC : burgessR3 D (deductiveClosure ({xi} ∪ B)) C :=
    dc_delta_B_burgessR3 h_D_mcs h_mcs_C h_B_dcs h_r3_DBC h_untl_conj_xi_D h_snce_conj_xi_C
  have h_DC_cud : ClosedUnderDerivation (deductiveClosure ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation _
  obtain ⟨B', h_B_sub_B', h_B'_max⟩ := burgessR3Maximal_extension_exists h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_DC_sub_B'', h_B''_max⟩ := burgessR3Maximal_extension_exists h_D_mcs h_mcs_C
    h_DC_cud h_r3_DC_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure _ (Set.mem_union_right _ hφ)
  have h_B_sub_B'' : B ⊆ B'' := Set.Subset.trans h_B_sub_DC h_DC_sub_B''
  have h_xi_in_DC : xi ∈ deductiveClosure ({xi} ∪ B) :=
    subset_deductiveClosure _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B'' : xi ∈ B'' := h_DC_sub_B'' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_D, h_B_sub_B',
    h_B_sub_B'', h_xi_in_B''⟩

/-- **Lemma 2.4 (Since direction) with guard**: Strengthened version for Since.
Returns R3M(A, B, C) with γ ∈ B. Note: only guarantees hContent(C) ⊆ A for
the original A from the Lindenbaum extension. -/
noncomputable def lemma_2_4_since_with_guard {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) (γ β : Formula Atom)
    (h_since : (β S γ) ∈ C) :
    ∃ B A : Set (Formula Atom), Temporal.SetMaximalConsistent A ∧
      β ∈ A ∧
      BurgessR3Maximal A B C ∧
      γ ∈ B := by
  have h_P_β : (𝐏β) ∈ C := since_implies_P_in_mcs h_mcs h_since
  have h_seed_cons := past_temporal_witness_seed_consistent C h_mcs β h_P_β
  obtain ⟨A, h_sup, h_A_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_β_A : β ∈ A := h_sup (Set.mem_union_left _ (Set.mem_singleton β))
  have h_h_sub : hContent C ⊆ A := fun χ hχ => h_sup (Set.mem_union_right _ hχ)
  have h_g_sub : gContent A ⊆ C := h_content_sub_imp_g_content_sub' h_A_mcs h_mcs h_h_sub
  obtain ⟨B₀, h_B₀⟩ := burgessR3Maximal_from_g_content_sub' h_A_mcs h_mcs h_g_sub
  by_cases h_γ_B₀ : γ ∈ B₀
  · exact ⟨B₀, A, h_A_mcs, h_β_A, h_B₀, h_γ_B₀⟩
  · obtain ⟨_, D, B'', _, h_R3M_DB''C, h_D_mcs, h_eta_D, _, _, _, h_γ_B''⟩ :=
      lemma_2_7_since h_A_mcs h_mcs h_B₀ h_B₀.1 h_g_sub γ β h_since h_γ_B₀
    exact ⟨B'', D, h_D_mcs, h_eta_D, h_R3M_DB''C, h_γ_B''⟩

end Cslib.Logic.Temporal.Metalogic.Chronicle
