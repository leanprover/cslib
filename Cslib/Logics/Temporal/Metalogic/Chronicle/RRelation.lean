/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes
import Cslib.Logics.Temporal.Metalogic.Chronicle.Frame
import Cslib.Logics.Temporal.Metalogic.Chronicle.CanonicalChain
import Cslib.Logics.Temporal.Metalogic.Chronicle.OrderedSeedConsistency
import Cslib.Logics.Temporal.Metalogic.WitnessSeed
import Mathlib.Order.Zorn

/-!
# r-Relation Lemmas (Burgess 1982, Lemmas 2.2-2.5)

Core r-relation infrastructure for the temporal chronicle construction.

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean
* Burgess 1982: "Axioms for tense logic II: Time periods"
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

private noncomputable def theorem_in_mcs' {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (h_deriv : DerivationTree FrameClass.Base [] phi) : phi ∈ M :=
  temporal_closed_under_derivation h_mcs (L := []) (fun _ h => by simp at h) ⟨h_deriv⟩

/-! ## BX10/BX5 at MCS Level -/

theorem until_implies_F_in_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {γ δ : Formula Atom}
    (h_until : Formula.untl δ γ ∈ A) :
    Formula.some_future δ ∈ A :=
  temporal_implication_property h_mcs
    (theorem_in_mcs' h_mcs (DerivationTree.axiom [] _ (Axiom.until_F γ δ) trivial)) h_until

theorem until_self_accum_in_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {γ δ : Formula Atom}
    (h_until : Formula.untl δ γ ∈ A) :
    Formula.untl δ (Formula.and γ (Formula.untl δ γ)) ∈ A :=
  temporal_implication_property h_mcs
    (theorem_in_mcs' h_mcs (DerivationTree.axiom [] _ (Axiom.self_accum_until γ δ) trivial)) h_until

theorem since_implies_P_in_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {γ δ : Formula Atom}
    (h_since : Formula.snce δ γ ∈ A) :
    Formula.some_past δ ∈ A :=
  temporal_implication_property h_mcs
    (theorem_in_mcs' h_mcs (DerivationTree.axiom [] _ (Axiom.since_P γ δ) trivial)) h_since

/-! ## r-Relation Guard Continues -/

theorem rRelation_guard_continues' {A B : Set (Formula Atom)}
    (h_r : rRelation A B) {γ δ : Formula Atom}
    (h_until : Formula.untl δ γ ∈ A) (h_not_delta : δ ∉ B) :
    γ ∈ B ∧ Formula.untl δ γ ∈ B := by
  rcases h_r γ δ h_until with h_delta | h_guard
  · exact absurd h_delta h_not_delta
  · exact h_guard

/-! ## Deductive Closure -/

noncomputable def deductiveClosure (Sig : Set (Formula Atom)) : Set (Formula Atom) :=
  {φ | ∃ L : List (Formula Atom), (∀ ψ ∈ L, ψ ∈ Sig) ∧ Nonempty (DerivationTree FrameClass.Base L φ)}

theorem subset_deductiveClosure (Sig : Set (Formula Atom)) : Sig ⊆ deductiveClosure Sig := by
  intro φ hφ
  exact ⟨[φ], fun ψ hψ => by simp at hψ; exact hψ ▸ hφ,
         ⟨DerivationTree.assumption _ φ (by simp)⟩⟩

theorem deductiveClosure_closed (Sig : Set (Formula Atom)) :
    ∀ (L : List (Formula Atom)) (φ : Formula Atom),
      (∀ ψ ∈ L, ψ ∈ deductiveClosure Sig) → DerivationTree FrameClass.Base L φ → φ ∈ deductiveClosure Sig := by
  intro L
  induction L with
  | nil =>
    intro φ _ d
    exact ⟨[], fun _ h => absurd h List.not_mem_nil, ⟨d⟩⟩
  | cons ψ L' ih =>
    intro φ hL d
    have d_imp := deduction_theorem L' ψ φ d
    have hψ := hL ψ (List.mem_cons_self)
    have hL' : ∀ χ ∈ L', χ ∈ deductiveClosure Sig :=
      fun χ hχ => hL χ (List.mem_cons_of_mem ψ hχ)
    have h_imp := ih (ψ.imp φ) hL' d_imp
    obtain ⟨M1, hM1_sub, ⟨d1⟩⟩ := h_imp
    obtain ⟨M2, hM2_sub, ⟨d2⟩⟩ := hψ
    refine ⟨M1 ++ M2, fun χ hχ => ?_, ?_⟩
    · rcases List.mem_append.mp hχ with h | h
      · exact hM1_sub χ h
      · exact hM2_sub χ h
    · exact ⟨DerivationTree.modus_ponens (M1 ++ M2) ψ φ
        (DerivationTree.weakening M1 (M1 ++ M2) (ψ.imp φ) d1 (List.subset_append_left M1 M2))
        (DerivationTree.weakening M2 (M1 ++ M2) ψ d2 (List.subset_append_right M1 M2))⟩

theorem deductiveClosure_consistent {Sig : Set (Formula Atom)}
    (h : Temporal.SetConsistent Sig) :
    Temporal.SetConsistent (deductiveClosure Sig) := by
  intro L hL ⟨d⟩
  have h_bot : (Formula.bot : Formula Atom) ∈ deductiveClosure Sig :=
    deductiveClosure_closed Sig L Formula.bot hL d
  obtain ⟨M, hM_sub, ⟨dM⟩⟩ := h_bot
  exact h M hM_sub ⟨dM⟩

theorem deductiveClosure_is_dcs {Sig : Set (Formula Atom)}
    (h : Temporal.SetConsistent Sig) :
    SetDeductivelyClosed (deductiveClosure Sig) :=
  ⟨deductiveClosure_consistent h, deductiveClosure_closed Sig⟩

theorem deductiveClosure_closed_under_derivation (Sig : Set (Formula Atom)) :
    ClosedUnderDerivation (deductiveClosure Sig) :=
  deductiveClosure_closed Sig

/-! ## R-Maximal Extension Existence via Zorn -/

def rDCSExtensions (A Sig : Set (Formula Atom)) : Set (Set (Formula Atom)) :=
  {B | Sig ⊆ B ∧ SetDeductivelyClosed B ∧ rRelation A B}

private theorem chain_finite_subset_in_element {c : Set (Set (Formula Atom))} {T₀ : Set (Formula Atom)}
    (hc_chain : IsChain (· ⊆ ·) c) (hT₀ : T₀ ∈ c)
    (L : List (Formula Atom))
    (hL : ∀ φ ∈ L, φ ∈ ⋃₀ c) :
    ∃ T ∈ c, ∀ φ ∈ L, φ ∈ T := by
  induction L with
  | nil => exact ⟨T₀, hT₀, fun _ h => absurd h List.not_mem_nil⟩
  | cons a L ih =>
    obtain ⟨Ta, hTa, ha⟩ := Set.mem_sUnion.mp (hL a (List.mem_cons_self))
    obtain ⟨TL, hTL, hLTL⟩ := ih (fun φ hφ => hL φ (List.mem_cons_of_mem a hφ))
    rcases hc_chain.total hTa hTL with h_le | h_le
    · exact ⟨TL, hTL, fun φ hφ => by
        rcases List.mem_cons.mp hφ with rfl | h
        · exact h_le ha
        · exact hLTL φ h⟩
    · exact ⟨Ta, hTa, fun φ hφ => by
        rcases List.mem_cons.mp hφ with rfl | h
        · exact ha
        · exact h_le (hLTL φ h)⟩

theorem rMaximal_extension_exists {A : Set (Formula Atom)}
    (_h_mcs : Temporal.SetMaximalConsistent A)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed Sig) (h_r : rRelation A Sig) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ rMaximal A B := by
  have h_S_in : Sig ∈ rDCSExtensions A Sig := ⟨Set.Subset.refl _, h_dcs, h_r⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset (rDCSExtensions A Sig) (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · constructor
        · intro L hL ⟨d⟩
          obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L (fun φ hφ => hL φ hφ)
          exact (hc_sub hTc).2.1.1 L hLT ⟨d⟩
        · intro L φ hL d
          obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L (fun ψ hψ => hL ψ hψ)
          exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1.2 L φ hLT d⟩
      · intro γ δ h_until
        rcases (hc_sub hT₀).2.2 γ δ h_until with h_d | ⟨h_g, h_u⟩
        · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
        · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩, Set.mem_sUnion.mpr ⟨T₀, hT₀, h_u⟩⟩)
  obtain ⟨hSB, hB_dcs, hB_r⟩ := hB_in
  refine ⟨B, hSB, hB_dcs, hB_r, ?_⟩
  intro C hC_dcs hBC hC_r
  exact hBC.2 (hB_max ⟨Set.Subset.trans hSB hBC.1, hC_dcs, hC_r⟩ hBC.1)

/-! ## R3-Maximal Extension Existence -/

def r3DCSExtensions (A Sig C : Set (Formula Atom)) : Set (Set (Formula Atom)) :=
  {B | Sig ⊆ B ∧ SetDeductivelyClosed B ∧ r3Relation A B C}

theorem r3Maximal_extension_exists {A C : Set (Formula Atom)}
    (_h_mcs_A : Temporal.SetMaximalConsistent A) (_h_mcs_C : Temporal.SetMaximalConsistent C)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed Sig) (h_r3 : r3Relation A Sig C) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ R3Maximal A B C := by
  have h_S_in : Sig ∈ r3DCSExtensions A Sig C := ⟨Set.Subset.refl _, h_dcs, h_r3⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset (r3DCSExtensions A Sig C) (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · constructor
        · intro L hL ⟨d⟩
          obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L (fun φ hφ => hL φ hφ)
          exact (hc_sub hTc).2.1.1 L hLT ⟨d⟩
        · intro L φ hL d
          obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L (fun ψ hψ => hL ψ hψ)
          exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1.2 L φ hLT d⟩
      · constructor
        · intro γ δ h_until
          rcases (hc_sub hT₀).2.2.1 γ δ h_until with h_d | ⟨h_g, h_u⟩
          · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
          · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩, Set.mem_sUnion.mpr ⟨T₀, hT₀, h_u⟩⟩
        · intro γ δ h_since
          rcases (hc_sub hT₀).2.2.2 γ δ h_since with h_d | ⟨h_g, h_s⟩
          · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
          · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩, Set.mem_sUnion.mpr ⟨T₀, hT₀, h_s⟩⟩)
  obtain ⟨hSB, hB_dcs, hB_r3⟩ := hB_in
  refine ⟨B, hSB, hB_dcs, hB_r3, ?_⟩
  intro D hD_dcs hBD hD_r3
  exact hBD.2 (hB_max ⟨Set.Subset.trans hSB hBD.1, hD_dcs, hD_r3⟩ hBD.1)

/-! ## Burgess Absorption (Lemma 2.5) -/

/-- burgessR absorption: if burgessR A β D and burgessR D β C, then burgessR A β C.
Uses BX6 (absorb_until): (β ∧ (γ U β)) U β → γ U β. -/
theorem burgessR_absorption {A D C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_D : Temporal.SetMaximalConsistent D)
    (β : Formula Atom)
    (h_β_D : β ∈ D)
    (h_rAD : burgessR A β D)
    (h_rDC : burgessR D β C) :
    burgessR A β C := by
  intro γ h_γ_C
  -- Step 1: γ U β ∈ D (from h_rDC)
  have h1 : Formula.untl γ β ∈ D := h_rDC γ h_γ_C
  -- Step 2: β ∧ (γ U β) ∈ D (conjunction in MCS)
  have h2 : Formula.and β (Formula.untl γ β) ∈ D :=
    dcs_conj_closed (mcs_is_dcs h_mcs_D) h_β_D h1
  -- Step 3: (β ∧ (γ U β)) U β ∈ A (from h_rAD applied to h2)
  have h3 : Formula.untl (Formula.and β (Formula.untl γ β)) β ∈ A :=
    h_rAD (Formula.and β (Formula.untl γ β)) h2
  -- Step 4: BX6 → γ U β ∈ A
  have h_bx6 : DerivationTree FrameClass.Base []
      ((Formula.untl (Formula.and β (Formula.untl γ β)) β).imp (Formula.untl γ β)) :=
    DerivationTree.axiom [] _ (Axiom.absorb_until β γ) trivial
  exact temporal_implication_property h_mcs_A (theorem_in_mcs' h_mcs_A h_bx6) h3

/-- burgessRSince absorption: mirror of burgessR_absorption using BX6'. -/
theorem burgessRSince_absorption {A D C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_D : Temporal.SetMaximalConsistent D)
    (β : Formula Atom)
    (h_β_D : β ∈ D)
    (h_rAD : burgessRSince A β D)
    (h_rDC : burgessRSince D β C) :
    burgessRSince A β C := by
  intro γ h_γ_C
  have h1 : Formula.snce γ β ∈ D := h_rDC γ h_γ_C
  have h2 : Formula.and β (Formula.snce γ β) ∈ D :=
    dcs_conj_closed (mcs_is_dcs h_mcs_D) h_β_D h1
  have h3 : Formula.snce (Formula.and β (Formula.snce γ β)) β ∈ A :=
    h_rAD (Formula.and β (Formula.snce γ β)) h2
  have h_bx6 : DerivationTree FrameClass.Base []
      ((Formula.snce (Formula.and β (Formula.snce γ β)) β).imp (Formula.snce γ β)) :=
    DerivationTree.axiom [] _ (Axiom.absorb_since β γ) trivial
  exact temporal_implication_property h_mcs_A (theorem_in_mcs' h_mcs_A h_bx6) h3

/-- burgessRSet absorption (set version). -/
theorem burgessRSet_absorption {A D C : Set (Formula Atom)} {B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_D : Temporal.SetMaximalConsistent D)
    (h_sub_D : B ⊆ D)
    (h_rAD : burgessRSet A B D)
    (h_rDC : burgessRSet D B C) :
    burgessRSet A B C := by
  intro β h_β_B
  exact burgessR_absorption h_mcs_A h_mcs_D β (h_sub_D h_β_B)
    (h_rAD β h_β_B) (h_rDC β h_β_B)

/-- burgessRSetSince absorption (set version). -/
theorem burgessRSetSince_absorption {A D C : Set (Formula Atom)} {B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_D : Temporal.SetMaximalConsistent D)
    (h_sub_D : B ⊆ D)
    (h_rAD : burgessRSetSince A B D)
    (h_rDC : burgessRSetSince D B C) :
    burgessRSetSince A B C := by
  intro β h_β_B
  exact burgessRSince_absorption h_mcs_A h_mcs_D β (h_sub_D h_β_B)
    (h_rAD β h_β_B) (h_rDC β h_β_B)

/-- burgessR3 absorption: composing r3 through an intermediate MCS. -/
theorem burgessR3_absorption {A D C : Set (Formula Atom)} {B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_D : Temporal.SetMaximalConsistent D)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_sub_D : B ⊆ D)
    (h_r3_AD : burgessR3 A B D)
    (h_r3_DC : burgessR3 D B C) :
    burgessR3 A B C :=
  -- burgessR3 A B C = burgessRSet A B C ∧ burgessRSetSince C B A
  -- burgessR3 A B D = burgessRSet A B D ∧ burgessRSetSince D B A
  -- burgessR3 D B C = burgessRSet D B C ∧ burgessRSetSince C B D
  -- For burgessRSet: compose A→D→C via absorption
  -- For burgessRSetSince: compose C→D→A via absorption
  ⟨burgessRSet_absorption h_mcs_A h_mcs_D h_sub_D h_r3_AD.1 h_r3_DC.1,
   burgessRSetSince_absorption h_mcs_C h_mcs_D h_sub_D h_r3_DC.2 h_r3_AD.2⟩

/-! ## BurgessR3Maximal Existence -/

/-- Helper: deductive closure of {δ} ∪ B inherits ClosedUnderDerivation. -/
theorem deductiveClosure_singleton_imp {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B) {δ φ : Formula Atom}
    (h_delta : δ ∈ B) (h_imp : (δ.imp φ) ∈ deductiveClosure B) :
    φ ∈ B := by
  obtain ⟨L, hL, ⟨d⟩⟩ := h_imp
  exact h_cud (δ :: L) φ
    (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | h
      · exact h_delta
      · exact hL ψ h)
    (DerivationTree.modus_ponens (δ :: L) δ φ
      (DerivationTree.weakening L (δ :: L) (δ.imp φ) d (fun x hx => List.mem_cons_of_mem δ hx))
      (DerivationTree.assumption (δ :: L) δ (List.mem_cons_self)))

/-- dcs_neg_insert_consistent: if B is CUD and φ ∉ B, then {¬φ} ∪ B is consistent. -/
theorem dcs_neg_insert_consistent {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B)
    {φ : Formula Atom} (h_not_mem : φ ∉ B) :
    Temporal.SetConsistent ({Formula.neg φ} ∪ B) := by
  intro L hL ⟨d⟩
  by_cases h_neg_in : Formula.neg φ ∈ L
  · have h_sub_reord : ∀ x, x ∈ L → x ∈ Formula.neg φ :: L.filter (fun y => decide (y ≠ Formula.neg φ)) := by
      intro x hx
      by_cases hxn : x = Formula.neg φ
      · exact List.mem_cons.mpr (Or.inl hxn)
      · exact List.mem_cons.mpr (Or.inr (by simp [List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
    have d_reord := DerivationTree.weakening L _ Formula.bot d h_sub_reord
    have d_negneg := deduction_theorem _ (Formula.neg φ) Formula.bot d_reord
    have h_filt_in_B : ∀ ψ ∈ L.filter (fun y => decide (y ≠ Formula.neg φ)), ψ ∈ B := by
      intro ψ hψ
      have h_and := List.mem_filter.mp hψ
      have h_ne : ψ ≠ Formula.neg φ := by simpa using h_and.2
      have h_mem := hL ψ h_and.1
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
      rcases h_mem with rfl | h
      · exact absurd rfl h_ne
      · exact h
    have h_dne := double_negation φ
    have d_dne_weak := DerivationTree.weakening [] (L.filter (fun y => decide (y ≠ Formula.neg φ))) _
      h_dne (fun _ h => nomatch h)
    have d_phi := DerivationTree.modus_ponens (L.filter (fun y => decide (y ≠ Formula.neg φ))) _ _
      d_dne_weak d_negneg
    exact h_not_mem (h_cud _ φ h_filt_in_B d_phi)
  · have h_L_in_B : ∀ ψ ∈ L, ψ ∈ B := by
      intro ψ hψ
      have h_mem := hL ψ hψ
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
      rcases h_mem with rfl | h
      · exact absurd hψ h_neg_in
      · exact h
    exact (cud_not_mem_is_sdc h_cud h_not_mem).1 L h_L_in_B ⟨d⟩

/-! ## MCS Contrapositive Helper -/

theorem mcs_contrapositive_mem {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M)
    {φ ψ : Formula Atom}
    (h_imp : φ.imp ψ ∈ M) (h_neg_psi : Formula.neg ψ ∈ M) :
    Formula.neg φ ∈ M := by
  by_contra h_not_neg
  have h_phi := (mcs_mem_iff_neg_not_mem h_mcs).mpr h_not_neg
  have h_psi := temporal_implication_property h_mcs h_imp h_phi
  exact mcs_not_mem_of_neg h_mcs h_neg_psi h_psi

/-! ## burgessR3Maximal_extension_exists -/

theorem burgessR3Maximal_extension_exists {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    {Sig : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation Sig)
    (h_br3 : burgessR3 A Sig C) :
    ∃ B, Sig ⊆ B ∧ BurgessR3Maximal A B C := by
  -- Use Zorn's lemma on the set of CUD extensions of Sig satisfying burgessR3 A - C
  have h_S_in : Sig ∈ {B | Sig ⊆ B ∧ ClosedUnderDerivation B ∧ burgessR3 A B C} :=
    ⟨Set.Subset.refl _, h_cud, h_br3⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset {B | Sig ⊆ B ∧ ClosedUnderDerivation B ∧ burgessR3 A B C} (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · -- ⋃₀ c is CUD
        intro L φ hL d
        obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L (fun ψ hψ => hL ψ hψ)
        exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1 L φ hLT d⟩
      · -- burgessR3 A (⋃₀ c) C
        constructor
        · intro β hβ γ hγ
          obtain ⟨T, hTc, hβT⟩ := Set.mem_sUnion.mp hβ
          exact (hc_sub hTc).2.2.1 β hβT γ hγ
        · intro β hβ γ hγ
          obtain ⟨T, hTc, hβT⟩ := Set.mem_sUnion.mp hβ
          exact (hc_sub hTc).2.2.2 β hβT γ hγ)
  obtain ⟨hSB, hB_cud, hB_br3⟩ := hB_in
  refine ⟨B, hSB, hB_cud, hB_br3, ?_⟩
  intro D hD_cud hBD hD_br3
  exact hBD.2 (hB_max ⟨Set.Subset.trans hSB hBD.1, hD_cud, hD_br3⟩ hBD.1)

/-! ## burgessR3Maximal_from_g_content_sub -/

/-- Key infrastructure: if g_content(A) ⊆ B and B is CUD satisfying burgessR3 A B C,
    then there exists a BurgessR3Maximal extension. -/
theorem burgessR3Maximal_from_g_content_sub {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B)
    (h_br3 : burgessR3 A B C) :
    ∃ B', B ⊆ B' ∧ BurgessR3Maximal A B' C :=
  burgessR3Maximal_extension_exists h_mcs_A h_mcs_C h_cud h_br3

end Cslib.Logic.Temporal.Metalogic.Chronicle
