/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.CanonicalChain

/-!
# Ordered Seed Consistency

Proves the Ordered Seed Consistency Theorem for BXCanonical.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/OrderedSeedConsistency.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Theorems.Propositional
open Cslib.Logic.Bimodal.Theorems.Combinators

variable {Atom : Type*}

private noncomputable def theorem_in_mcs_fc {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent FrameClass.Base M)
    (h_deriv : DerivationTree FrameClass.Base [] phi) : phi ∈ M :=
  SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_deriv

/-- The enriched resolving seed: {psi, alpha} union g_content(M). -/
def enriched_resolving_seed (M : Set (Formula Atom)) (ψ α : Formula Atom) : Set (Formula Atom) :=
  {ψ, α} ∪ g_content M

/-- If F(psi and alpha) in M for MCS M, then {psi, alpha} union g_content(M) is consistent. -/
theorem enriched_resolving_seed_consistent {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent (fc := FrameClass.Base) M) (ψ α : Formula Atom)
    (h_F : Formula.someFuture (Formula.and ψ α) ∈ M) :
    SetConsistent (fc := FrameClass.Base) (enriched_resolving_seed M ψ α) := by
  have h_seed_cons := forward_temporal_witness_seed_consistent M h_mcs
    (Formula.and ψ α) h_F
  obtain ⟨M', h_sup, h_M'_mcs⟩ := set_lindenbaum_base h_seed_cons
  have h_conj_in : Formula.and ψ α ∈ M' :=
    h_sup (Set.mem_union_left _ (Set.mem_singleton _))
  have h_ψ_in : ψ ∈ M' :=
    SetMaximalConsistent.implication_property h_M'_mcs
      (theorem_in_mcs_fc h_M'_mcs (lce_imp ψ α)) h_conj_in
  have h_α_in : α ∈ M' :=
    SetMaximalConsistent.implication_property h_M'_mcs
      (theorem_in_mcs_fc h_M'_mcs (rce_imp ψ α)) h_conj_in
  have h_g_sub : g_content M ⊆ M' :=
    fun χ hχ => h_sup (Set.mem_union_right _ hχ)
  have h_seed_sub : enriched_resolving_seed M ψ α ⊆ M' := by
    intro φ hφ
    simp only [enriched_resolving_seed, Set.mem_union, Set.mem_insert_iff,
               Set.mem_singleton_iff] at hφ
    rcases hφ with (rfl | rfl) | hg
    · exact h_ψ_in
    · exact h_α_in
    · exact h_g_sub hg
  intro L hL hd
  exact h_M'_mcs.1 L (fun φ hφ => h_seed_sub (hL φ hφ)) hd

/-- Special case for two defects. -/
theorem ordered_two_defect_seed_consistent {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent (fc := FrameClass.Base) M) (ψ₁ ψ₂ : Formula Atom)
    (h_F : Formula.someFuture (Formula.and ψ₁ (Formula.someFuture ψ₂)) ∈ M) :
    SetConsistent (fc := FrameClass.Base) ({ψ₁, Formula.someFuture ψ₂} ∪ g_content M) :=
  enriched_resolving_seed_consistent h_mcs ψ₁ (Formula.someFuture ψ₂) h_F

/-- BX11 at MCS level. -/
theorem temp_linearity_mcs {M : Set (Formula Atom)} (h_mcs : SetMaximalConsistent (fc := FrameClass.Base) M)
    (A B : Formula Atom)
    (h_FA : Formula.someFuture A ∈ M) (h_FB : Formula.someFuture B ∈ M) :
    Formula.someFuture (Formula.and A B) ∈ M ∨
    Formula.someFuture (Formula.and A (Formula.someFuture B)) ∈ M ∨
    Formula.someFuture (Formula.and (Formula.someFuture A) B) ∈ M := by
  have h_conj : Formula.and (Formula.someFuture A) (Formula.someFuture B) ∈ M := by
    have h_pair : DerivationTree FrameClass.Base [] ((Formula.someFuture A).imp
        ((Formula.someFuture B).imp
          (Formula.and (Formula.someFuture A) (Formula.someFuture B)))) :=
      pairing (Formula.someFuture A) (Formula.someFuture B)
    exact SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs
        (theorem_in_mcs_fc h_mcs h_pair) h_FA) h_FB
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.and (Formula.someFuture A) (Formula.someFuture B)).imp
      (Formula.or (Formula.someFuture (Formula.and A B))
        (Formula.or (Formula.someFuture (Formula.and A (Formula.someFuture B)))
          (Formula.someFuture (Formula.and (Formula.someFuture A) B))))) :=
    DerivationTree.axiom [] _ (Axiom.temp_linearity A B) trivial
  have h_disj := SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs_fc h_mcs h_ax) h_conj
  rcases SetMaximalConsistent.negation_complete h_mcs
    (Formula.someFuture (Formula.and A B)) with h_l | h_neg_l
  · exact Or.inl h_l
  · right
    have h_right : Formula.or (Formula.someFuture (Formula.and A (Formula.someFuture B)))
        (Formula.someFuture (Formula.and (Formula.someFuture A) B)) ∈ M :=
      SetMaximalConsistent.implication_property h_mcs h_disj h_neg_l
    rcases SetMaximalConsistent.negation_complete h_mcs
      (Formula.someFuture (Formula.and A (Formula.someFuture B))) with h_m | h_neg_m
    · exact Or.inl h_m
    · right
      exact SetMaximalConsistent.implication_property h_mcs h_right h_neg_m

/-- Two defect consistent seed. -/
theorem two_defect_consistent_seed {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent (fc := FrameClass.Base) M) (ψ₁ ψ₂ : Formula Atom)
    (h_F1 : Formula.someFuture ψ₁ ∈ M)
    (h_F2 : Formula.someFuture ψ₂ ∈ M) :
    SetConsistent (fc := FrameClass.Base) ({ψ₁, ψ₂} ∪ g_content M) ∨
    SetConsistent (fc := FrameClass.Base) ({ψ₁, Formula.someFuture ψ₂} ∪ g_content M) ∨
    SetConsistent (fc := FrameClass.Base) ({ψ₂, Formula.someFuture ψ₁} ∪ g_content M) := by
  rcases temp_linearity_mcs h_mcs ψ₁ ψ₂ h_F1 h_F2 with h_both | h_1first | h_2first
  · exact Or.inl (enriched_resolving_seed_consistent h_mcs ψ₁ ψ₂ h_both)
  · exact Or.inr (Or.inl (enriched_resolving_seed_consistent h_mcs ψ₁
      (Formula.someFuture ψ₂) h_1first))
  · have h_seed := enriched_resolving_seed_consistent h_mcs
      (Formula.someFuture ψ₁) ψ₂ h_2first
    exact Or.inr (Or.inr (by
      unfold enriched_resolving_seed at h_seed
      have h_eq : ({ψ₂, Formula.someFuture ψ₁} : Set (Formula Atom)) =
          ({Formula.someFuture ψ₁, ψ₂} : Set (Formula Atom)) := Set.pair_comm _ _
      rw [h_eq]; exact h_seed))

/-- No new F-defects in successor. -/
theorem no_new_f_defects {M M' : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent (fc := FrameClass.Base) M) (h_mcs' : SetMaximalConsistent (fc := FrameClass.Base) M')
    (h_g_sub : g_content M ⊆ M')
    (α : Formula Atom) (h_neg : Formula.allFuture (Formula.neg α) ∈ M) :
    Formula.someFuture α ∉ M' := by
  have h_GG : Formula.allFuture (Formula.allFuture (Formula.neg α)) ∈ M :=
    SetMaximalConsistent.allFuture_allFuture h_mcs h_neg
  have h_G_neg_in' : Formula.allFuture (Formula.neg α) ∈ M' := h_g_sub h_GG
  intro h_F
  exact someFuture_allFuture_neg_absurd h_mcs' α h_F h_G_neg_in'

/-- Resolved target is in successor. -/
theorem resolved_target_in_successor {M M' : Set (Formula Atom)}
    {ψ : Formula Atom}
    (h_seed_sub : {ψ} ∪ g_content M ⊆ M') : ψ ∈ M' :=
  h_seed_sub (Set.mem_union_left _ (Set.mem_singleton ψ))

end Cslib.Logic.Bimodal.Metalogic.BXCanonical
