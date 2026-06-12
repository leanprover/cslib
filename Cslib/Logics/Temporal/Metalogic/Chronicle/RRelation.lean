/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes
public import Cslib.Logics.Temporal.Metalogic.Chronicle.Frame
public import Cslib.Logics.Temporal.Metalogic.Chronicle.CanonicalChain
public import Cslib.Logics.Temporal.Metalogic.Chronicle.OrderedSeedConsistency
public import Cslib.Logics.Temporal.Metalogic.WitnessSeed
public import Mathlib.Order.Zorn

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

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## BX10/BX5 at MCS Level -/

theorem until_implies_F_in_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {γ δ : Formula Atom}
    (h_until : (δ U γ) ∈ A) :
    (𝐅δ) ∈ A :=
  temporal_implication_property h_mcs
    (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.until_F γ δ) trivial)) h_until

theorem until_self_accum_in_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {γ δ : Formula Atom}
    (h_until : (δ U γ) ∈ A) :
    Formula.untl δ (Formula.and γ (Formula.untl δ γ)) ∈ A :=
  temporal_implication_property h_mcs
    (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.self_accum_until γ δ) trivial)) h_until

theorem since_implies_P_in_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {γ δ : Formula Atom}
    (h_since : (δ S γ) ∈ A) :
    (𝐏δ) ∈ A :=
  temporal_implication_property h_mcs
    (theoremInMcs h_mcs (DerivationTree.axiom [] _ (Axiom.since_P γ δ) trivial)) h_since

/-! ## r-Relation Guard Continues -/

theorem rRelation_guard_continues' {A B : Set (Formula Atom)}
    (h_r : rRelation A B) {γ δ : Formula Atom}
    (h_until : (δ U γ) ∈ A) (h_not_delta : δ ∉ B) :
    γ ∈ B ∧ (δ U γ) ∈ B := by
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
    have d_imp := deductionTheorem L' ψ φ d
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

theorem chain_finite_subset_in_element {c : Set (Set (Formula Atom))} {T₀ : Set (Formula Atom)}
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
  have h1 : (γ U β) ∈ D := h_rDC γ h_γ_C
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
  exact temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_bx6) h3

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
  have h1 : (γ S β) ∈ D := h_rDC γ h_γ_C
  have h2 : Formula.and β (Formula.snce γ β) ∈ D :=
    dcs_conj_closed (mcs_is_dcs h_mcs_D) h_β_D h1
  have h3 : Formula.snce (Formula.and β (Formula.snce γ β)) β ∈ A :=
    h_rAD (Formula.and β (Formula.snce γ β)) h2
  have h_bx6 : DerivationTree FrameClass.Base []
      ((Formula.snce (Formula.and β (Formula.snce γ β)) β).imp (Formula.snce γ β)) :=
    DerivationTree.axiom [] _ (Axiom.absorb_since β γ) trivial
  exact temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_bx6) h3

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
  by_cases h_neg_in : (¬φ) ∈ L
  · have h_sub_reord : ∀ x, x ∈ L → x ∈ Formula.neg φ :: L.filter (fun y => decide (y ≠ Formula.neg φ)) := by
      intro x hx
      by_cases hxn : x = Formula.neg φ
      · exact List.mem_cons.mpr (Or.inl hxn)
      · exact List.mem_cons.mpr (Or.inr (by simp [List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
    have d_reord := DerivationTree.weakening L _ Formula.bot d h_sub_reord
    have d_negneg := deductionTheorem _ (Formula.neg φ) Formula.bot d_reord
    have h_filt_in_B : ∀ ψ ∈ L.filter (fun y => decide (y ≠ Formula.neg φ)), ψ ∈ B := by
      intro ψ hψ
      have h_and := List.mem_filter.mp hψ
      have h_ne : ψ ≠ Formula.neg φ := by simpa using h_and.2
      have h_mem := hL ψ h_and.1
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
      rcases h_mem with rfl | h
      · exact absurd rfl h_ne
      · exact h
    have h_dne := doubleNegation φ
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
    (h_imp : (φ → ψ) ∈ M) (h_neg_psi : (¬ψ) ∈ M) :
    (¬φ) ∈ M := by
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

/-- Key infrastructure: if gContent(A) ⊆ B and B is CUD satisfying burgessR3 A B C,
    then there exists a BurgessR3Maximal extension. -/
theorem burgessR3Maximal_from_g_content_sub {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B)
    (h_br3 : burgessR3 A B C) :
    ∃ B', B ⊆ B' ∧ BurgessR3Maximal A B' C :=
  burgessR3Maximal_extension_exists h_mcs_A h_mcs_C h_cud h_br3

/-! ## Left Monotonicity Helpers (BX2G/BX2H at MCS Level) -/

/-- Left monotonicity for Until via G: If G(β₁ → β₂) ∈ A and untl(β₁, γ) ∈ A,
then untl(β₂, γ) ∈ A. Uses BX2G (left_mono_until_G). -/
theorem untl_left_mono_G {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (h_G_impl : (β₁.imp β₂).allFuture ∈ A)
    (h_untl : (γ U β₁) ∈ A) :
    (γ U β₂) ∈ A := by
  have h_ax := theoremInMcs h_mcs
    (DerivationTree.axiom [] _ (Axiom.left_mono_until_G β₁ β₂ γ) trivial)
  have h_step := temporal_implication_property h_mcs h_ax h_G_impl
  exact temporal_implication_property h_mcs h_step h_untl

/-- Left monotonicity for Since via H: If H(β₁ → β₂) ∈ A and snce(β₁, γ) ∈ A,
then snce(β₂, γ) ∈ A. Uses BX2H (left_mono_since_H). -/
theorem snce_left_mono_H {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (h_H_impl : (β₁.imp β₂).allPast ∈ A)
    (h_snce : (γ S β₁) ∈ A) :
    (γ S β₂) ∈ A := by
  have h_ax := theoremInMcs h_mcs
    (DerivationTree.axiom [] _ (Axiom.left_mono_since_H β₁ β₂ γ) trivial)
  have h_step := temporal_implication_property h_mcs h_ax h_H_impl
  exact temporal_implication_property h_mcs h_step h_snce

/-- Left monotonicity for Until via theorem: If ⊢ β₁ → β₂ and untl(β₁, γ) ∈ A,
then untl(β₂, γ) ∈ A. Uses BX2G via temporal necessitation. -/
theorem untl_left_mono_thm {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (h_impl : DerivationTree FrameClass.Base [] (β₁.imp β₂))
    (h_untl : (γ U β₁) ∈ A) :
    (γ U β₂) ∈ A := by
  have h_G := theoremInMcs h_mcs (DerivationTree.temporal_necessitation _ h_impl)
  exact untl_left_mono_G h_mcs h_G h_untl

/-- Left monotonicity for Since via theorem (mirror): If ⊢ β₁ → β₂ and snce(β₁, γ) ∈ A,
then snce(β₂, γ) ∈ A. Uses BX2H via past necessitation. -/
theorem snce_left_mono_thm {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A)
    {β₁ β₂ γ : Formula Atom}
    (h_impl : DerivationTree FrameClass.Base [] (β₁.imp β₂))
    (h_snce : (γ S β₁) ∈ A) :
    (γ S β₂) ∈ A := by
  have h_H := theoremInMcs h_mcs (pastNecessitation _ h_impl)
  exact snce_left_mono_H h_mcs h_H h_snce

/-! ## Duality Helpers for Burgess Lemma 2.3 -/

/-- In an MCS, ¬H(¬α) ∈ M implies P(α) ∈ M. -/
theorem neg_allPast_neg_to_somePast {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (α : Formula Atom)
    (h : Formula.neg (Formula.allPast (Formula.neg α)) ∈ M) :
    (𝐏α) ∈ M := by
  -- ¬H(¬α) gives P(¬¬α) by DNE, then BX3' converts to P(α)
  have h_dne_P : Formula.somePast (α.neg.neg) ∈ M := by
    have h_dne : DerivationTree FrameClass.Base [] ((Formula.somePast α.neg.neg).neg.neg.imp (Formula.somePast α.neg.neg)) :=
      doubleNegation (Formula.somePast α.neg.neg)
    exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_dne) h
  have h_dne_ax : DerivationTree FrameClass.Base [] (α.neg.neg.imp α) := doubleNegation α
  have h_H_dne : DerivationTree FrameClass.Base [] ((α.neg.neg.imp α).allPast) :=
    pastNecessitation _ h_dne_ax
  have h_bx3' : DerivationTree FrameClass.Base [] ((α.neg.neg.imp α).allPast.imp
      ((Formula.snce α.neg.neg Formula.top).imp (Formula.snce α Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_since α.neg.neg α Formula.top) trivial
  have h_P_mono : DerivationTree FrameClass.Base [] ((Formula.somePast α.neg.neg).imp (Formula.somePast α)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3' h_H_dne
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_P_mono) h_dne_P

/-- In an MCS, ¬G(¬γ) ∈ M implies F(γ) ∈ M. -/
theorem neg_allFuture_neg_to_someFuture {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (γ : Formula Atom)
    (h : Formula.neg (Formula.allFuture (Formula.neg γ)) ∈ M) :
    (𝐅γ) ∈ M := by
  have h_dne_F : Formula.someFuture (γ.neg.neg) ∈ M := by
    have h_dne : DerivationTree FrameClass.Base [] ((Formula.someFuture γ.neg.neg).neg.neg.imp (Formula.someFuture γ.neg.neg)) :=
      doubleNegation (Formula.someFuture γ.neg.neg)
    exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_dne) h
  have h_dne_ax : DerivationTree FrameClass.Base [] (γ.neg.neg.imp γ) := doubleNegation γ
  have h_G_dne : DerivationTree FrameClass.Base [] ((γ.neg.neg.imp γ).allFuture) :=
    DerivationTree.temporal_necessitation _ h_dne_ax
  have h_bx3 : DerivationTree FrameClass.Base [] ((γ.neg.neg.imp γ).allFuture.imp
      ((Formula.untl γ.neg.neg Formula.top).imp (Formula.untl γ Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_until γ.neg.neg γ Formula.top) trivial
  have h_F_mono : DerivationTree FrameClass.Base [] ((Formula.someFuture γ.neg.neg).imp (Formula.someFuture γ)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dne
  exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_F_mono) h_dne_F

/-- F(H(¬α)) and G(P(α)) are contradictory in an MCS. -/
theorem someFuture_H_neg_G_P_absurd {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (α : Formula Atom)
    (h_F : Formula.someFuture (Formula.allPast (Formula.neg α)) ∈ M)
    (h_GP : Formula.allFuture (Formula.somePast α) ∈ M) : False := by
  -- P(α) → ¬H(¬α) via P(α) → P(¬¬α) → ¬H(¬α)
  have h_dni_ax : DerivationTree FrameClass.Base [] (α.imp α.neg.neg) := dni α
  have h_H_dni : DerivationTree FrameClass.Base [] ((α.imp α.neg.neg).allPast) :=
    pastNecessitation _ h_dni_ax
  have h_bx3' : DerivationTree FrameClass.Base [] ((α.imp α.neg.neg).allPast.imp
      ((Formula.snce α Formula.top).imp (Formula.snce α.neg.neg Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_since α α.neg.neg Formula.top) trivial
  have h_P_to_Pnn : DerivationTree FrameClass.Base [] ((Formula.somePast α).imp (Formula.somePast α.neg.neg)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3' h_H_dni
  have h_dni_P : DerivationTree FrameClass.Base [] ((Formula.somePast α.neg.neg).imp (Formula.somePast α.neg.neg).neg.neg) :=
    dni (Formula.somePast α.neg.neg)
  have h_P_to_neg_H : DerivationTree FrameClass.Base [] ((Formula.somePast α).imp (Formula.neg (Formula.allPast (Formula.neg α)))) :=
    impTrans h_P_to_Pnn h_dni_P
  have h_G_imp : DerivationTree FrameClass.Base [] (Formula.allFuture ((Formula.somePast α).imp (Formula.neg (Formula.allPast (Formula.neg α))))) :=
    DerivationTree.temporal_necessitation _ h_P_to_neg_H
  have h_kd : DerivationTree FrameClass.Base [] (((Formula.somePast α).imp (Formula.neg (Formula.allPast (Formula.neg α)))).allFuture.imp
      ((Formula.somePast α).allFuture.imp (Formula.neg (Formula.allPast (Formula.neg α))).allFuture)) :=
    tempKDistDerived (Formula.somePast α) (Formula.neg (Formula.allPast (Formula.neg α)))
  have h_G_P_imp_G_neg_H : DerivationTree FrameClass.Base [] ((Formula.somePast α).allFuture.imp
      (Formula.neg (Formula.allPast (Formula.neg α))).allFuture) :=
    DerivationTree.modus_ponens [] _ _ h_kd h_G_imp
  have h_G_neg_H : (Formula.neg (Formula.allPast (Formula.neg α))).allFuture ∈ M :=
    temporal_implication_property h_mcs (theoremInMcs h_mcs h_G_P_imp_G_neg_H) h_GP
  exact someFuture_allFuture_neg_absurd h_mcs (Formula.allPast (Formula.neg α)) h_F h_G_neg_H

/-- P(G(¬γ)) and H(F(γ)) are contradictory in an MCS. -/
theorem somePast_G_neg_H_F_absurd {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (γ : Formula Atom)
    (h_P : Formula.somePast (Formula.allFuture (Formula.neg γ)) ∈ M)
    (h_HF : Formula.allPast (Formula.someFuture γ) ∈ M) : False := by
  have h_dni_ax : DerivationTree FrameClass.Base [] (γ.imp γ.neg.neg) := dni γ
  have h_G_dni : DerivationTree FrameClass.Base [] ((γ.imp γ.neg.neg).allFuture) :=
    DerivationTree.temporal_necessitation _ h_dni_ax
  have h_bx3 : DerivationTree FrameClass.Base [] ((γ.imp γ.neg.neg).allFuture.imp
      ((Formula.untl γ Formula.top).imp (Formula.untl γ.neg.neg Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_until γ γ.neg.neg Formula.top) trivial
  have h_F_to_Fnn : DerivationTree FrameClass.Base [] ((Formula.someFuture γ).imp (Formula.someFuture γ.neg.neg)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dni
  have h_dni_F : DerivationTree FrameClass.Base [] ((Formula.someFuture γ.neg.neg).imp (Formula.someFuture γ.neg.neg).neg.neg) :=
    dni (Formula.someFuture γ.neg.neg)
  have h_F_to_neg_G : DerivationTree FrameClass.Base [] ((Formula.someFuture γ).imp (Formula.neg (Formula.allFuture (Formula.neg γ)))) :=
    impTrans h_F_to_Fnn h_dni_F
  have h_H_imp : DerivationTree FrameClass.Base [] (Formula.allPast ((Formula.someFuture γ).imp (Formula.neg (Formula.allFuture (Formula.neg γ))))) :=
    pastNecessitation _ h_F_to_neg_G
  have h_kd : DerivationTree FrameClass.Base [] (((Formula.someFuture γ).imp (Formula.neg (Formula.allFuture (Formula.neg γ)))).allPast.imp
      ((Formula.someFuture γ).allPast.imp (Formula.neg (Formula.allFuture (Formula.neg γ))).allPast)) :=
    pastKDist (Formula.someFuture γ) (Formula.neg (Formula.allFuture (Formula.neg γ)))
  have h_H_F_imp_H_neg_G : DerivationTree FrameClass.Base [] ((Formula.someFuture γ).allPast.imp
      (Formula.neg (Formula.allFuture (Formula.neg γ))).allPast) :=
    DerivationTree.modus_ponens [] _ _ h_kd h_H_imp
  have h_H_neg_G : (Formula.neg (Formula.allFuture (Formula.neg γ))).allPast ∈ M :=
    temporal_implication_property h_mcs (theoremInMcs h_mcs h_H_F_imp_H_neg_G) h_HF
  exact somePast_allPast_neg_absurd h_mcs (Formula.allFuture (Formula.neg γ)) h_P h_H_neg_G

/-! ## Burgess Lemma 2.3: burgessR <-> burgessRSince -/

/-- **Burgess Lemma 2.3 (forward)**: burgessR(A, β, C) implies burgessRSince(C, β, A). -/
theorem burgessR_implies_burgessRSince {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    {β : Formula Atom} (h_burgessR : burgessR A β C) :
    burgessRSince C β A := by
  intro α hα
  -- Step 1: Show P(α) ∈ C
  have h_P : (𝐏α) ∈ C := by
    rcases temporal_negation_complete h_mcs_C (α.neg.allPast) with h_H | h_notH
    · -- H(¬α) ∈ C: derive contradiction via F(H(¬α)) ∈ A and G(P(α)) ∈ A
      have h_untl : Formula.untl (α.neg.allPast) β ∈ A := h_burgessR _ h_H
      have h_ax10 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.until_F β α.neg.allPast) trivial
      have h_F : Formula.someFuture (α.neg.allPast) ∈ A :=
        temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_ax10) h_untl
      have h_bx4 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.connect_future α) trivial
      have h_GP : Formula.allFuture (Formula.somePast α) ∈ A :=
        temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_bx4) hα
      exact False.elim (someFuture_H_neg_G_P_absurd h_mcs_A α h_F h_GP)
    · exact neg_allPast_neg_to_somePast h_mcs_C α h_notH
  -- Step 2: From P(α) ∈ C, derive snce(β, α) ∈ C by contradiction
  by_contra h_not
  have h_neg : (Formula.snce α β).neg ∈ C := mcs_neg_of_not_mem h_mcs_C h_not
  have h_untl : Formula.untl (Formula.snce α β).neg β ∈ A := h_burgessR _ h_neg
  have h_conj : Formula.and α (Formula.untl (Formula.snce α β).neg β) ∈ A :=
    dcs_conj_closed (mcs_is_dcs h_mcs_A) hα h_untl
  -- BX13 (enrichment_until): α ∧ untl(β, ¬snce(β,α)) → untl(β, ¬snce(β,α) ∧ snce(β,α))
  have h_a3a := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.enrichment_until β (Formula.snce α β).neg α) trivial
  have h_enriched : Formula.untl ((Formula.snce α β).neg.and (Formula.snce α β)) β ∈ A :=
    temporal_implication_property h_mcs_A (theoremInMcs h_mcs_A h_a3a) h_conj
  have h_F := until_implies_F_in_mcs h_mcs_A h_enriched
  -- ¬snce(β,α) ∧ snce(β,α) → ⊥ is derivable
  have h_neg_event : DerivationTree FrameClass.Base [] ((Formula.snce α β).neg.and (Formula.snce α β)).neg := by
    have h1 := lceImp (Formula.snce α β).neg (Formula.snce α β)
    have h2 := rceImp (Formula.snce α β).neg (Formula.snce α β)
    have h3 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.imp_k ((Formula.snce α β).neg.and (Formula.snce α β)) (Formula.snce α β) (Formula.bot : Formula Atom)) trivial
    exact DerivationTree.modus_ponens [] _ _ (DerivationTree.modus_ponens [] _ _ h3 h1) h2
  have h_G_neg := theoremInMcs h_mcs_A (DerivationTree.temporal_necessitation _ h_neg_event)
  exact someFuture_allFuture_neg_absurd h_mcs_A _ h_F h_G_neg

/-- **Burgess Lemma 2.3 (backward)**: burgessRSince(C, β, A) implies burgessR(A, β, C). -/
theorem burgessRSince_implies_burgessR {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    {β : Formula Atom} (h_burgessRSince : burgessRSince C β A) :
    burgessR A β C := by
  intro γ hγ
  -- Step 1: Show F(γ) ∈ A
  have h_F : (𝐅γ) ∈ A := by
    rcases temporal_negation_complete h_mcs_A (γ.neg.allFuture) with h_G | h_notG
    · -- G(¬γ) ∈ A: derive contradiction
      have h_snce : Formula.snce (γ.neg.allFuture) β ∈ C := h_burgessRSince _ h_G
      have h_ax10' := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.since_P β γ.neg.allFuture) trivial
      have h_P : Formula.somePast (γ.neg.allFuture) ∈ C :=
        temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_ax10') h_snce
      have h_bx4' := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.connect_past γ) trivial
      have h_HF : Formula.allPast (Formula.someFuture γ) ∈ C :=
        temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_bx4') hγ
      exact False.elim (somePast_G_neg_H_F_absurd h_mcs_C γ h_P h_HF)
    · exact neg_allFuture_neg_to_someFuture h_mcs_A γ h_notG
  -- Step 2: From F(γ) ∈ A, derive untl(β, γ) ∈ A by contradiction
  by_contra h_not
  have h_neg : (Formula.untl γ β).neg ∈ A := mcs_neg_of_not_mem h_mcs_A h_not
  have h_snce : Formula.snce (Formula.untl γ β).neg β ∈ C := h_burgessRSince _ h_neg
  have h_conj : Formula.and γ (Formula.snce (Formula.untl γ β).neg β) ∈ C :=
    dcs_conj_closed (mcs_is_dcs h_mcs_C) hγ h_snce
  -- BX13' (enrichment_since): γ ∧ snce(β, ¬untl(β,γ)) → snce(β, ¬untl(β,γ) ∧ untl(β,γ))
  have h_a3b := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.enrichment_since β (Formula.untl γ β).neg γ) trivial
  have h_enriched : Formula.snce ((Formula.untl γ β).neg.and (Formula.untl γ β)) β ∈ C :=
    temporal_implication_property h_mcs_C (theoremInMcs h_mcs_C h_a3b) h_conj
  have h_P' := since_implies_P_in_mcs h_mcs_C h_enriched
  have h_neg_event : DerivationTree FrameClass.Base [] ((Formula.untl γ β).neg.and (Formula.untl γ β)).neg := by
    have h1 := lceImp (Formula.untl γ β).neg (Formula.untl γ β)
    have h2 := rceImp (Formula.untl γ β).neg (Formula.untl γ β)
    have h3 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.imp_k ((Formula.untl γ β).neg.and (Formula.untl γ β)) (Formula.untl γ β) (Formula.bot : Formula Atom)) trivial
    exact DerivationTree.modus_ponens [] _ _ (DerivationTree.modus_ponens [] _ _ h3 h1) h2
  have h_H_neg := theoremInMcs h_mcs_C (pastNecessitation _ h_neg_event)
  exact somePast_allPast_neg_absurd h_mcs_C _ h_P' h_H_neg

/-! ## Deductive Closure Singleton Propagation -/

/-- If L consists entirely of copies of η and L ⊢ φ, then [η] ⊢ φ. -/
noncomputable def derivationFromSingletonList {η φ : Formula Atom} {L : List (Formula Atom)}
    (hL : ∀ ψ ∈ L, ψ = η) (d : DerivationTree FrameClass.Base L φ) :
    DerivationTree FrameClass.Base [η] φ :=
  DerivationTree.weakening L [η] φ d (fun ψ hψ => by rw [hL ψ hψ]; simp)

/-- If φ ∈ deductiveClosure({η}), then ⊢ η → φ. -/
theorem deductiveClosure_singleton_imp' {η φ : Formula Atom}
    (hφ : φ ∈ deductiveClosure ({η} : Set (Formula Atom))) :
    Nonempty (DerivationTree FrameClass.Base [] (η.imp φ)) := by
  obtain ⟨L, hL_sub, ⟨d⟩⟩ := hφ
  have hL_eq : ∀ ψ ∈ L, ψ = η := fun ψ hψ => Set.mem_singleton_iff.mp (hL_sub ψ hψ)
  exact ⟨deductionTheorem [] η φ (derivationFromSingletonList hL_eq d)⟩

/-- burgessR propagation through deductive closure: If burgessR(A, η, C) and
φ ∈ deductiveClosure({η}), then burgessR(A, φ, C). -/
theorem burgessR_of_deductiveClosure_singleton {A C : Set (Formula Atom)} {η : Formula Atom}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_burgessR : burgessR A η C) (φ : Formula Atom)
    (hφ : φ ∈ deductiveClosure ({η} : Set (Formula Atom))) :
    burgessR A φ C := by
  obtain ⟨d⟩ := deductiveClosure_singleton_imp' hφ
  intro γ hγ
  exact untl_left_mono_thm h_mcs_A d (h_burgessR γ hγ)

/-- burgessRSince propagation through deductive closure (mirror). -/
theorem burgessRSince_of_deductiveClosure_singleton {A C : Set (Formula Atom)} {η : Formula Atom}
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_burgessRSince : burgessRSince C η A) (φ : Formula Atom)
    (hφ : φ ∈ deductiveClosure ({η} : Set (Formula Atom))) :
    burgessRSince C φ A := by
  obtain ⟨d⟩ := deductiveClosure_singleton_imp' hφ
  intro γ hγ
  exact snce_left_mono_thm h_mcs_C d (h_burgessRSince γ hγ)

/-! ## BurgessR3Maximal Existence from Seed -/

/-- BurgessR3Maximal existence from seed: Given η satisfying both burgessR(A, η, C) and
burgessRSince(C, η, A), there exists B with BurgessR3Maximal(A, B, C). -/
theorem burgessR3Maximal_exists_from_seed (A C : Set (Formula Atom)) (η : Formula Atom)
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_burgessR : burgessR A η C)
    (h_burgessRSince : burgessRSince C η A)
    (_h_η_A : η ∈ A) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal A B C := by
  have h_dc_cud : ClosedUnderDerivation (deductiveClosure ({η} : Set (Formula Atom))) :=
    deductiveClosure_closed_under_derivation _
  have h_dc_r3 : burgessR3 A (deductiveClosure ({η} : Set (Formula Atom))) C := by
    constructor
    · intro φ hφ
      exact burgessR_of_deductiveClosure_singleton h_mcs_A h_burgessR φ hφ
    · intro φ hφ
      exact burgessRSince_of_deductiveClosure_singleton h_mcs_C h_burgessRSince φ hφ
  obtain ⟨B, _, h_B3M⟩ := burgessR3Maximal_extension_exists h_mcs_A h_mcs_C h_dc_cud h_dc_r3
  exact ⟨B, h_B3M⟩

end Cslib.Logic.Temporal.Metalogic.Chronicle
