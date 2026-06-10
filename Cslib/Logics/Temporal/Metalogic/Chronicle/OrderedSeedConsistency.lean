/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.Frame
public import Cslib.Logics.Temporal.Metalogic.Chronicle.CanonicalChain

/-!
# Ordered Seed Consistency

Enriched seed consistency, linearity, and two-defect seeds for temporal logic.

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/BXCanonical/OrderedSeedConsistency.lean
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

variable {Atom : Type*}

/-- The enriched resolving seed: {psi, alpha} union g_content(M). -/
def enriched_resolving_seed (M : Set (Formula Atom)) (ψ α : Formula Atom) : Set (Formula Atom) :=
  {ψ, α} ∪ g_content M

/-- If F(psi and alpha) in MCS M, then {psi, alpha} union g_content(M) is consistent. -/
theorem enriched_resolving_seed_consistent {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (ψ α : Formula Atom)
    (h_F : Formula.someFuture (Formula.and ψ α) ∈ M) :
    Temporal.SetConsistent (enriched_resolving_seed M ψ α) := by
  have h_seed_cons := forward_temporal_witness_seed_consistent M h_mcs
    (Formula.and ψ α) h_F
  obtain ⟨M', h_sup, h_M'_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_conj_in : Formula.and ψ α ∈ M' :=
    h_sup (Set.mem_union_left _ (Set.mem_singleton _))
  have h_ψ_in : ψ ∈ M' :=
    temporal_implication_property h_M'_mcs
      (theorem_in_mcs h_M'_mcs (lce_imp ψ α)) h_conj_in
  have h_α_in : α ∈ M' :=
    temporal_implication_property h_M'_mcs
      (theorem_in_mcs h_M'_mcs (rce_imp ψ α)) h_conj_in
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

/-- BX11 at MCS level. -/
theorem temp_linearity_mcs {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (A B : Formula Atom)
    (h_FA : Formula.someFuture A ∈ M) (h_FB : Formula.someFuture B ∈ M) :
    Formula.someFuture (Formula.and A B) ∈ M ∨
    Formula.someFuture (Formula.and A (Formula.someFuture B)) ∈ M ∨
    Formula.someFuture (Formula.and (Formula.someFuture A) B) ∈ M := by
  have h_conj : Formula.and (Formula.someFuture A) (Formula.someFuture B) ∈ M :=
    temporal_implication_property h_mcs
      (temporal_implication_property h_mcs
        (theorem_in_mcs h_mcs (pairing (Formula.someFuture A) (Formula.someFuture B)))
        h_FA)
      h_FB
  have h_ax : DerivationTree FrameClass.Base []
      ((Formula.and (Formula.someFuture A) (Formula.someFuture B)).imp
      (Formula.or (Formula.someFuture (Formula.and A B))
        (Formula.or (Formula.someFuture (Formula.and A (Formula.someFuture B)))
          (Formula.someFuture (Formula.and (Formula.someFuture A) B))))) :=
    DerivationTree.axiom [] _ (Axiom.temp_linearity A B) trivial
  have h_disj := temporal_implication_property h_mcs
    (theorem_in_mcs h_mcs h_ax) h_conj
  rcases temporal_negation_complete h_mcs
    (Formula.someFuture (Formula.and A B)) with h_l | h_neg_l
  · exact Or.inl h_l
  · right
    have h_right := temporal_implication_property h_mcs h_disj h_neg_l
    rcases temporal_negation_complete h_mcs
      (Formula.someFuture (Formula.and A (Formula.someFuture B))) with h_m | h_neg_m
    · exact Or.inl h_m
    · exact Or.inr (temporal_implication_property h_mcs h_right h_neg_m)

/-- Two defect consistent seed. -/
theorem two_defect_consistent_seed {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (ψ₁ ψ₂ : Formula Atom)
    (h_F1 : Formula.someFuture ψ₁ ∈ M)
    (h_F2 : Formula.someFuture ψ₂ ∈ M) :
    Temporal.SetConsistent ({ψ₁, ψ₂} ∪ g_content M) ∨
    Temporal.SetConsistent ({ψ₁, Formula.someFuture ψ₂} ∪ g_content M) ∨
    Temporal.SetConsistent ({ψ₂, Formula.someFuture ψ₁} ∪ g_content M) := by
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
    (h_mcs : Temporal.SetMaximalConsistent M) (h_mcs' : Temporal.SetMaximalConsistent M')
    (h_g_sub : g_content M ⊆ M')
    (α : Formula Atom) (h_neg : Formula.allFuture (Formula.neg α) ∈ M) :
    Formula.someFuture α ∉ M' := by
  have h_GG := mcs_g_trans h_mcs h_neg
  have h_G_neg_in' : Formula.allFuture (Formula.neg α) ∈ M' := h_g_sub h_GG
  intro h_F
  exact someFuture_allFuture_neg_absurd h_mcs' α h_F h_G_neg_in'

/-- Resolved target is in successor. -/
theorem resolved_target_in_successor {M M' : Set (Formula Atom)}
    {ψ : Formula Atom}
    (h_seed_sub : {ψ} ∪ g_content M ⊆ M') : ψ ∈ M' :=
  h_seed_sub (Set.mem_union_left _ (Set.mem_singleton ψ))

end Cslib.Logic.Temporal.Metalogic.Chronicle
