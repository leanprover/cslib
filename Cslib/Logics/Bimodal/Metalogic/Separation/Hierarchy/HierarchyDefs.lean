/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.NormalForm
public import Cslib.Logics.Bimodal.Metalogic.Separation.TemporalClosure
public import Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.Cases
public import Cslib.Logics.Bimodal.Metalogic.Separation.FormulaOps

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false

/-!
# Separation Hierarchy Definitions: U/S-Type Predicates, Abstraction, and Junction-Depth Monotonicity

Single U/S-type predicates, Lemma 10.2.5 (single-U separability), U/S-formula
abstraction, semantic correctness, preservation lemmas, count properties, and
junction-depth monotonicity.
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Helper Lemmas for intTruth -/

theorem int_truth_and_iff {M : IntStructure Atom} {t : ℤ} {φ ψ : Formula Atom} :
    intTruth M t (Formula.and φ ψ) ↔ intTruth M t φ ∧ intTruth M t ψ :=
  int_truth_and M t φ ψ

theorem int_truth_or_iff {M : IntStructure Atom} {t : ℤ} {φ ψ : Formula Atom} :
    intTruth M t (Formula.or φ ψ) ↔ intTruth M t φ ∨ intTruth M t ψ :=
  int_truth_or M t φ ψ

theorem int_truth_neg_iff {M : IntStructure Atom} {t : ℤ} {φ : Formula Atom} :
    intTruth M t (Formula.neg φ) ↔ ¬ intTruth M t φ :=
  int_truth_neg M t φ

/-! ## Predicate: Formula has Single U-Type

A formula has "single U-type U(A,B)" if every `untl` subformula in it
has arguments exactly A and B. This captures the condition for Lemma 10.2.5. -/

/-- A formula has single U-type: every `untl` node has exactly arguments (A, B). -/
def hasSingleUType (φ x y : Formula Atom) : Prop :=
  match φ with
  | .atom _ => True
  | .bot => True
  | .imp ψ₁ ψ₂ => hasSingleUType ψ₁ x y ∧ hasSingleUType ψ₂ x y
  | .box ψ => hasSingleUType ψ x y
  | .untl ψ₁ ψ₂ => ψ₁ = x ∧ ψ₂ = y
  | .snce ψ₁ ψ₂ => hasSingleUType ψ₁ x y ∧ hasSingleUType ψ₂ x y

/-- A formula is U-free implies it trivially has single U-type (vacuously). -/
theorem u_free_has_single_U_type {φ x y : Formula Atom} (h : isUFree φ = true) :
    hasSingleUType φ x y := by
  induction φ with
  | atom _ => trivial
  | bot => trivial
  | imp ψ₁ ψ₂ ih1 ih2 =>
    simp [isUFree] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box ψ ih =>
    simp [isUFree] at h
    exact ih h
  | untl _ _ => simp [isUFree] at h
  | snce ψ₁ ψ₂ ih1 ih2 =>
    simp [isUFree] at h
    exact ⟨ih1 h.1, ih2 h.2⟩

/-! ## Single-S-Type Predicate (dual of hasSingleUType) -/

/-- A formula has single S-type: every `snce` node has exactly arguments (A, B). -/
def hasSingleSType (φ x y : Formula Atom) : Prop :=
  match φ with
  | .atom _ => True
  | .bot => True
  | .imp ψ₁ ψ₂ => hasSingleSType ψ₁ x y ∧ hasSingleSType ψ₂ x y
  | .box ψ => hasSingleSType ψ x y
  | .untl ψ₁ ψ₂ => hasSingleSType ψ₁ x y ∧ hasSingleSType ψ₂ x y
  | .snce ψ₁ ψ₂ => ψ₁ = x ∧ ψ₂ = y

/-- A formula is S-free implies it trivially has single S-type (vacuously). -/
theorem s_free_has_single_S_type {φ x y : Formula Atom} (h : isSFree φ = true) :
    hasSingleSType φ x y := by
  induction φ with
  | atom _ => trivial
  | bot => trivial
  | imp ψ₁ ψ₂ ih1 ih2 =>
    simp [isSFree] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box ψ ih =>
    simp [isSFree] at h
    exact ih h
  | snce _ _ => simp [isSFree] at h
  | untl ψ₁ ψ₂ ih1 ih2 =>
    simp [isSFree] at h
    exact ⟨ih1 h.1, ih2 h.2⟩

/-! ## Lemma 10.2.5: Single-U Formula Separability -/

/-- Helper: Formula.neg preserves hasSingleUType. -/
theorem has_single_U_type_neg {φ x y : Formula Atom} (h : hasSingleUType φ x y) :
    hasSingleUType (Formula.neg φ) x y := by
  simp [Formula.neg, hasSingleUType]
  exact h

/-- Helper: Formula.and preserves hasSingleUType. -/
theorem has_single_U_type_and {φ ψ x y : Formula Atom}
    (h1 : hasSingleUType φ x y) (h2 : hasSingleUType ψ x y) :
    hasSingleUType (Formula.and φ ψ) x y := by
  simp [Formula.and, Formula.neg, hasSingleUType]
  exact ⟨h1, h2⟩

/-- Helper: Formula.or preserves hasSingleUType. -/
theorem has_single_U_type_or {φ ψ x y : Formula Atom}
    (h1 : hasSingleUType φ x y) (h2 : hasSingleUType ψ x y) :
    hasSingleUType (Formula.or φ ψ) x y := by
  simp [Formula.or, Formula.neg, hasSingleUType]
  exact ⟨h1, h2⟩

/-- Helper: U(A,B) trivially has single U-type U(A,B). -/
theorem has_single_U_type_untl (x y : Formula Atom) :
    hasSingleUType (.untl x y) x y :=
  ⟨rfl, rfl⟩

/-- Helper: snce preserves hasSingleUType. -/
theorem has_single_U_type_snce {φ ψ x y : Formula Atom}
    (h1 : hasSingleUType φ x y) (h2 : hasSingleUType ψ x y) :
    hasSingleUType (.snce φ ψ) x y := ⟨h1, h2⟩

/-- Helper: imp preserves hasSingleUType. -/
theorem has_single_U_type_imp {φ ψ x y : Formula Atom}
    (h1 : hasSingleUType φ x y) (h2 : hasSingleUType ψ x y) :
    hasSingleUType (.imp φ ψ) x y := ⟨h1, h2⟩

/-- U(A,B) with S-free A, B is itself syntactically separated. -/
theorem untl_s_free_separated {x y : Formula Atom}
    (hx : isSFree x = true) (hy : isSFree y = true) :
    isSyntacticallySeparated (.untl x y) = true := by
  simp [isSyntacticallySeparated, hx, hy]

/-- U(A,B) with S-free A, B is separable. -/
theorem untl_s_free_separable {x y : Formula Atom}
    (hx : isSFree x = true) (hy : isSFree y = true) :
    isSeparable (.untl x y) :=
  ⟨.untl x y, untl_s_free_separated hx hy, int_equiv_refl _⟩

/-! ## Lemma 10.2.6: Multi-U Induction on Count (GHR94) -/

/-! ### U-Formula Abstraction -/

section DecEq
variable [DecidableEq Atom]

/-- Replace all occurrences of `untl A B` in `phi` with atom `p`. -/
def abstractUntl (phi x y : Formula Atom) (p : Atom) : Formula Atom :=
  match phi with
  | .atom a => .atom a
  | .bot => .bot
  | .imp psi1 psi2 => .imp (abstractUntl psi1 x y p) (abstractUntl psi2 x y p)
  | .box psi => .box (abstractUntl psi x y p)
  | .untl psi1 psi2 =>
    if psi1 = x ∧ psi2 = y then .atom p
    else .untl (abstractUntl psi1 x y p) (abstractUntl psi2 x y p)
  | .snce psi1 psi2 => .snce (abstractUntl psi1 x y p) (abstractUntl psi2 x y p)

/-! ### Syntactic Roundtrip: abstract then substitute back -/

/-- Substituting U(A,B) for atom p in the abstracted formula recovers the original,
    provided p does not appear in the original formula. -/
theorem abstract_subst_roundtrip (phi x y : Formula Atom) (p : Atom)
    (hfresh : ¬ (p ∈ phi.atoms)) :
    substFormula (abstractUntl phi x y p) p (.untl x y) = phi := by
  induction phi with
  | atom a =>
    simp [Formula.atoms, Finset.mem_singleton] at hfresh
    have hne : a ≠ p := Ne.symm hfresh
    simp [abstractUntl, substFormula, hne]
  | bot => simp [abstractUntl, substFormula]
  | imp c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp [abstractUntl, substFormula, ih1 hfresh.1, ih2 hfresh.2]
  | box c ih =>
    simp [Formula.atoms] at hfresh
    simp [abstractUntl, substFormula, ih hfresh]
  | untl c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp only [abstractUntl]
    split
    · next h => simp [substFormula, h.1, h.2]
    · next _ =>
      simp only [substFormula]
      congr 1
      · exact ih1 hfresh.1
      · exact ih2 hfresh.2
  | snce c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp [abstractUntl, substFormula, ih1 hfresh.1, ih2 hfresh.2]

/-! ### Semantic Correctness of Abstraction -/

/-- Semantic correctness: truth of φ in structure M is equivalent to truth of
    the abstracted formula in M with atom p interpreted as the truth set of U(A,B). -/
theorem abstract_untl_correct (phi x y : Formula Atom) (p : Atom)
    (hfresh : ¬ (p ∈ phi.atoms))
    (m : IntStructure Atom) (t : Int) :
    intTruth m t phi ↔
    intTruth (m.withAtom p {s | intTruth m s (.untl x y)}) t
      (abstractUntl phi x y p) := by
  induction phi generalizing t with
  | atom a =>
    simp [Formula.atoms, Finset.mem_singleton] at hfresh
    simp [abstractUntl, intTruth, IntStructure.withAtom, Ne.symm hfresh]
  | bot => simp [abstractUntl, intTruth]
  | imp c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp only [abstractUntl, intTruth]
    constructor
    · intro h hc; exact (ih2 hfresh.2 t).mp (h ((ih1 hfresh.1 t).mpr hc))
    · intro h hc; exact (ih2 hfresh.2 t).mpr (h ((ih1 hfresh.1 t).mp hc))
  | box _ => simp [abstractUntl, intTruth]
  | untl c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp only [abstractUntl]
    split
    · next h =>
      obtain ⟨hc, hd⟩ := h; subst hc; subst hd
      simp [intTruth, IntStructure.withAtom, Set.mem_setOf_eq]
    · next _ =>
      simp only [intTruth]
      constructor
      · rintro ⟨s, hts, hc, hd⟩
        exact ⟨s, hts, (ih1 hfresh.1 s).mp hc,
          fun r hr1 hr2 => (ih2 hfresh.2 r).mp (hd r hr1 hr2)⟩
      · rintro ⟨s, hts, hc, hd⟩
        exact ⟨s, hts, (ih1 hfresh.1 s).mpr hc,
          fun r hr1 hr2 => (ih2 hfresh.2 r).mpr (hd r hr1 hr2)⟩
  | snce c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp only [abstractUntl, intTruth]
    constructor
    · rintro ⟨s, hst, hc, hd⟩
      exact ⟨s, hst, (ih1 hfresh.1 s).mp hc,
        fun r hr1 hr2 => (ih2 hfresh.2 r).mp (hd r hr1 hr2)⟩
    · rintro ⟨s, hst, hc, hd⟩
      exact ⟨s, hst, (ih1 hfresh.1 s).mpr hc,
        fun r hr1 hr2 => (ih2 hfresh.2 r).mpr (hd r hr1 hr2)⟩

/-- The syntactic roundtrip gives intEquiv directly. -/
theorem abstract_untl_equiv (phi x y : Formula Atom) (p : Atom)
    (hfresh : ¬ (p ∈ phi.atoms)) :
    intEquiv phi (substFormula (abstractUntl phi x y p) p (.untl x y)) := by
  rw [abstract_subst_roundtrip phi x y p hfresh]
  exact int_equiv_refl phi

/-! ### Preservation Lemmas -/

/-- abstractUntl preserves isSFree: if φ is S-free, so is the abstracted form. -/
theorem abstract_untl_preserves_S_free (phi x y : Formula Atom) (p : Atom)
    (h : isSFree phi = true) :
    isSFree (abstractUntl phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstractUntl, isSFree]
  | bot => simp [abstractUntl, isSFree]
  | imp c d ih1 ih2 =>
    simp [isSFree] at h
    simp [abstractUntl, isSFree, ih1 h.1, ih2 h.2]
  | box c ih =>
    simp [isSFree] at h
    simp [abstractUntl, isSFree, ih h]
  | untl c d ih1 ih2 =>
    simp [isSFree] at h
    simp only [abstractUntl]
    split
    · simp [isSFree]
    · simp [isSFree, ih1 h.1, ih2 h.2]
  | snce _ _ => simp [isSFree] at h

/-- abstractUntl preserves noSNestedInU. -/
theorem abstract_untl_preserves_no_S_nested (phi x y : Formula Atom) (p : Atom)
    (h : noSNestedInU phi) :
    noSNestedInU (abstractUntl phi x y p) := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp c d ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | box c ih => exact ih h
  | untl c d _ _ =>
    simp only [abstractUntl]
    split
    · trivial
    · have ⟨hc_sf, hd_sf⟩ := h
      exact ⟨abstract_untl_preserves_S_free c x y p hc_sf,
             abstract_untl_preserves_S_free d x y p hd_sf⟩
  | snce c d ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩

/-- If φ has single U-type U(A,B), abstracting it out gives a U-free formula. -/
theorem abstract_untl_makes_U_free (phi x y : Formula Atom) (p : Atom)
    (h : hasSingleUType phi x y) :
    isUFree (abstractUntl phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstractUntl, isUFree]
  | bot => simp [abstractUntl, isUFree]
  | imp c d ih1 ih2 =>
    simp [abstractUntl, isUFree, ih1 h.1, ih2 h.2]
  | box c ih =>
    simp [abstractUntl, isUFree, ih h]
  | untl c d _ _ =>
    obtain ⟨hc, hd⟩ := h; subst hc; subst hd
    simp [abstractUntl, isUFree]
  | snce c d ih1 ih2 =>
    simp [abstractUntl, isUFree, ih1 h.1, ih2 h.2]

/-! ### Count Properties -/

/-- countUSubformulas = 0 iff the formula is U-free. -/
theorem count_U_zero_iff_U_free (phi : Formula Atom) :
    countUSubformulas phi = 0 ↔ isUFree phi = true := by
  induction phi with
  | atom _ => simp [countUSubformulas, isUFree]
  | bot => simp [countUSubformulas, isUFree]
  | imp c d ih1 ih2 =>
    simp [countUSubformulas, isUFree, ih1, ih2]
  | box c ih =>
    simp [countUSubformulas, isUFree, ih]
  | untl c d =>
    simp [countUSubformulas, isUFree]
  | snce c d ih1 ih2 =>
    simp [countUSubformulas, isUFree, ih1, ih2]

/-- abstractUntl does not increase the U-subformula count. -/
theorem abstract_untl_count_le (phi x y : Formula Atom) (p : Atom) :
    countUSubformulas (abstractUntl phi x y p) ≤ countUSubformulas phi := by
  induction phi with
  | atom _ => simp [abstractUntl, countUSubformulas]
  | bot => simp [abstractUntl, countUSubformulas]
  | imp c d ih1 ih2 =>
    simp [abstractUntl, countUSubformulas]
    exact Nat.add_le_add ih1 ih2
  | box c ih =>
    simp [abstractUntl, countUSubformulas]; exact ih
  | untl c d ih1 ih2 =>
    simp only [abstractUntl, countUSubformulas]
    split
    · simp [countUSubformulas]
    · simp only [countUSubformulas]
      have := Nat.add_le_add ih1 ih2
      omega
  | snce c d ih1 ih2 =>
    simp [abstractUntl, countUSubformulas]
    exact Nat.add_le_add ih1 ih2

/-- If φ has single U-type, abstracting it reduces count to 0. -/
theorem abstract_untl_count_zero_of_single (phi x y : Formula Atom) (p : Atom)
    (h : hasSingleUType phi x y) :
    countUSubformulas (abstractUntl phi x y p) = 0 := by
  rw [count_U_zero_iff_U_free]
  exact abstract_untl_makes_U_free phi x y p h

/-! ### S-Formula Abstraction (dual of abstractUntl) -/

/-- Replace all occurrences of `snce A B` in `phi` with atom `p`. -/
def abstractSnce (phi x y : Formula Atom) (p : Atom) : Formula Atom :=
  match phi with
  | .atom a => .atom a
  | .bot => .bot
  | .imp psi1 psi2 => .imp (abstractSnce psi1 x y p) (abstractSnce psi2 x y p)
  | .box psi => .box (abstractSnce psi x y p)
  | .untl psi1 psi2 => .untl (abstractSnce psi1 x y p) (abstractSnce psi2 x y p)
  | .snce psi1 psi2 =>
    if psi1 = x ∧ psi2 = y then .atom p
    else .snce (abstractSnce psi1 x y p) (abstractSnce psi2 x y p)

/-- Semantic correctness of abstractSnce. -/
theorem abstract_snce_correct (phi x y : Formula Atom) (p : Atom)
    (m : IntStructure Atom) (t : ℤ)
    (h_eq : m.val p = {s | intTruth m s (.snce x y)}) :
    intTruth m t (abstractSnce phi x y p) ↔ intTruth m t phi := by
  induction phi generalizing t with
  | atom a =>
    simp only [abstractSnce, intTruth]
  | bot => simp [abstractSnce, intTruth]
  | imp c d ih1 ih2 =>
    simp only [abstractSnce, intTruth]
    exact Iff.imp (ih1 t) (ih2 t)
  | box _ => simp [abstractSnce, intTruth]
  | untl c d ih1 ih2 =>
    simp only [abstractSnce, intTruth]
    constructor
    · rintro ⟨s, hts, hc, hd⟩
      exact ⟨s, hts, (ih1 s).mp hc,
        fun r hr1 hr2 => (ih2 r).mp (hd r hr1 hr2)⟩
    · rintro ⟨s, hts, hc, hd⟩
      exact ⟨s, hts, (ih1 s).mpr hc,
        fun r hr1 hr2 => (ih2 r).mpr (hd r hr1 hr2)⟩
  | snce c d ih1 ih2 =>
    simp only [abstractSnce]
    split
    · next h =>
      obtain ⟨hc, hd⟩ := h; subst hc; subst hd
      simp [intTruth, Set.mem_setOf_eq, h_eq]
    · next hne =>
      simp only [intTruth]
      constructor
      · rintro ⟨s, hst, hc, hd⟩
        exact ⟨s, hst, (ih1 s).mp hc,
          fun r hr1 hr2 => (ih2 r).mp (hd r hr1 hr2)⟩
      · rintro ⟨s, hst, hc, hd⟩
        exact ⟨s, hst, (ih1 s).mpr hc,
          fun r hr1 hr2 => (ih2 r).mpr (hd r hr1 hr2)⟩

/-- Substituting S(A,B) for atom p in the abstracted formula recovers the original. -/
theorem abstract_snce_subst_roundtrip (phi x y : Formula Atom) (p : Atom)
    (hfresh : ¬ (p ∈ phi.atoms)) :
    substFormula (abstractSnce phi x y p) p (.snce x y) = phi := by
  induction phi with
  | atom a =>
    simp [Formula.atoms, Finset.mem_singleton] at hfresh
    have hne : a ≠ p := Ne.symm hfresh
    simp [abstractSnce, substFormula, hne]
  | bot => simp [abstractSnce, substFormula]
  | imp c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp [abstractSnce, substFormula, ih1 hfresh.1, ih2 hfresh.2]
  | box c ih =>
    simp [Formula.atoms] at hfresh
    simp [abstractSnce, substFormula, ih hfresh]
  | untl c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp [abstractSnce, substFormula, ih1 hfresh.1, ih2 hfresh.2]
  | snce c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp only [abstractSnce]
    split
    · next h => simp [substFormula, h.1, h.2]
    · next _ =>
      simp only [substFormula]
      congr 1
      · exact ih1 hfresh.1
      · exact ih2 hfresh.2

/-! ### Preservation Lemmas for abstractSnce -/

/-- abstractSnce preserves isUFree. -/
theorem abstract_snce_preserves_U_free (phi x y : Formula Atom) (p : Atom)
    (h : isUFree phi = true) :
    isUFree (abstractSnce phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstractSnce, isUFree]
  | bot => simp [abstractSnce, isUFree]
  | imp c d ih1 ih2 =>
    simp [isUFree] at h
    simp [abstractSnce, isUFree, ih1 h.1, ih2 h.2]
  | box c ih =>
    simp [isUFree] at h
    simp [abstractSnce, isUFree, ih h]
  | untl _ _ => simp [isUFree] at h
  | snce c d ih1 ih2 =>
    simp [isUFree] at h
    simp only [abstractSnce]
    split
    · simp [isUFree]
    · simp [isUFree, ih1 h.1, ih2 h.2]

/-- abstractSnce preserves isSFree. -/
theorem abstract_snce_preserves_S_free (phi x y : Formula Atom) (p : Atom)
    (h : isSFree phi = true) :
    isSFree (abstractSnce phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstractSnce, isSFree]
  | bot => simp [abstractSnce, isSFree]
  | imp c d ih1 ih2 =>
    simp [isSFree] at h
    simp [abstractSnce, isSFree, ih1 h.1, ih2 h.2]
  | box c ih =>
    simp [isSFree] at h
    simp [abstractSnce, isSFree, ih h]
  | untl c d ih1 ih2 =>
    simp [isSFree] at h
    simp [abstractSnce, isSFree, ih1 h.1, ih2 h.2]
  | snce _ _ => simp [isSFree] at h

/-- If φ has no U nested in S, abstracting S(A,B) preserves this property. -/
theorem abstract_snce_preserves_no_U_nested (phi x y : Formula Atom) (p : Atom)
    (h : noUNestedInS phi) :
    noUNestedInS (abstractSnce phi x y p) := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp c d ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | box c ih => exact ih h
  | untl c d ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | snce c d _ _ =>
    simp only [abstractSnce]
    split
    · trivial
    · have ⟨hc_uf, hd_uf⟩ := h
      exact ⟨abstract_snce_preserves_U_free c x y p hc_uf,
             abstract_snce_preserves_U_free d x y p hd_uf⟩

/-- If φ has single S-type S(A,B), abstracting it gives a S-free formula. -/
theorem abstract_snce_makes_S_free (phi x y : Formula Atom) (p : Atom)
    (h : hasSingleSType phi x y) :
    isSFree (abstractSnce phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstractSnce, isSFree]
  | bot => simp [abstractSnce, isSFree]
  | imp c d ih1 ih2 =>
    simp [abstractSnce, isSFree, ih1 h.1, ih2 h.2]
  | box c ih =>
    simp [abstractSnce, isSFree, ih h]
  | untl c d ih1 ih2 =>
    simp [abstractSnce, isSFree, ih1 h.1, ih2 h.2]
  | snce c d _ _ =>
    obtain ⟨hc, hd⟩ := h; subst hc; subst hd
    simp [abstractSnce, isSFree]

/-! ### Junction-Depth Monotonicity Lemmas -/

/-- joint 4-way bound relating junctionDepth, junctionDepthU, junctionDepthS. -/
theorem junction_depth_bounds (φ : Formula Atom) :
    junctionDepth φ ≤ junctionDepthU φ ∧
    junctionDepth φ ≤ junctionDepthS φ ∧
    junctionDepthU φ ≤ 1 + junctionDepth φ ∧
    junctionDepthS φ ≤ 1 + junctionDepth φ := by
  induction φ with
  | atom _ => simp [junctionDepth, junctionDepthU, junctionDepthS]
  | bot => simp [junctionDepth, junctionDepthU, junctionDepthS]
  | imp a b ih1 ih2 =>
    simp only [junctionDepth, junctionDepthU, junctionDepthS]
    omega
  | box a ih => simp [junctionDepth, junctionDepthU, junctionDepthS, ih.1, ih.2.1, ih.2.2.1, ih.2.2.2]
  | untl a b ih1 ih2 =>
    simp only [junctionDepth, junctionDepthU, junctionDepthS]
    omega
  | snce a b ih1 ih2 =>
    simp only [junctionDepth, junctionDepthU, junctionDepthS]
    omega

/-- junctionDepth is bounded above by junctionDepthU. -/
theorem junction_depth_le_jdU (φ : Formula Atom) : junctionDepth φ ≤ junctionDepthU φ :=
  (junction_depth_bounds φ).1

/-- junctionDepth is bounded above by junctionDepthS. -/
theorem junction_depth_le_jdS (φ : Formula Atom) : junctionDepth φ ≤ junctionDepthS φ :=
  (junction_depth_bounds φ).2.1

theorem jd_imp_le_left (φ ψ : Formula Atom) : junctionDepth φ ≤ junctionDepth (.imp φ ψ) :=
  Nat.le_max_left _ _

theorem jd_imp_le_right (φ ψ : Formula Atom) : junctionDepth ψ ≤ junctionDepth (.imp φ ψ) :=
  Nat.le_max_right _ _

theorem jd_box_le (φ : Formula Atom) : junctionDepth φ ≤ junctionDepth (.box φ) :=
  Nat.le_refl _

theorem jd_untl_le_left (φ ψ : Formula Atom) : junctionDepth φ ≤ junctionDepth (.untl φ ψ) := by
  simp only [junctionDepth]
  exact Nat.le_trans (junction_depth_le_jdU φ) (Nat.le_max_left _ _)

theorem jd_untl_le_right (φ ψ : Formula Atom) : junctionDepth ψ ≤ junctionDepth (.untl φ ψ) := by
  simp only [junctionDepth]
  exact Nat.le_trans (junction_depth_le_jdU ψ) (Nat.le_max_right _ _)

theorem jd_snce_le_left (φ ψ : Formula Atom) : junctionDepth φ ≤ junctionDepth (.snce φ ψ) := by
  simp only [junctionDepth]
  exact Nat.le_trans (junction_depth_le_jdS φ) (Nat.le_max_left _ _)

theorem jd_snce_le_right (φ ψ : Formula Atom) : junctionDepth ψ ≤ junctionDepth (.snce φ ψ) := by
  simp only [junctionDepth]
  exact Nat.le_trans (junction_depth_le_jdS ψ) (Nat.le_max_right _ _)

/-! ### abstractUntl Identity and Preservation -/

/-- abstractUntl is the identity on U-free formulas. -/
theorem abstract_untl_identity_on_U_free (phi x y : Formula Atom) (p : Atom)
    (h : isUFree phi = true) :
    abstractUntl phi x y p = phi := by
  induction phi with
  | atom _ => simp [abstractUntl]
  | bot => simp [abstractUntl]
  | imp c d ih1 ih2 => simp [isUFree] at h; simp [abstractUntl, ih1 h.1, ih2 h.2]
  | box c ih => simp [isUFree] at h; simp [abstractUntl, ih h]
  | untl _ _ => simp [isUFree] at h
  | snce c d ih1 ih2 => simp [isUFree] at h; simp [abstractUntl, ih1 h.1, ih2 h.2]

/-- abstractUntl preserves U-freeness (trivially, since it's identity on U-free). -/
theorem abstract_untl_preserves_U_free (phi x y : Formula Atom) (p : Atom)
    (h : isUFree phi = true) :
    isUFree (abstractUntl phi x y p) = true := by
  rw [abstract_untl_identity_on_U_free phi x y p h]; exact h

/-- abstractUntl preserves syntactic separation. -/
theorem abstract_untl_preserves_separated (phi x y : Formula Atom) (p : Atom)
    (hsep : isSyntacticallySeparated phi = true) :
    isSyntacticallySeparated (abstractUntl phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstractUntl, isSyntacticallySeparated]
  | bot => simp [abstractUntl, isSyntacticallySeparated]
  | imp a b ih1 ih2 =>
    simp [isSyntacticallySeparated] at hsep
    simp [abstractUntl, isSyntacticallySeparated, ih1 hsep.1, ih2 hsep.2]
  | box _ => simp [abstractUntl, isSyntacticallySeparated]
  | untl a b _ih1 _ih2 =>
    simp [isSyntacticallySeparated] at hsep
    simp only [abstractUntl]
    split
    · simp [isSyntacticallySeparated]
    · simp [isSyntacticallySeparated,
            abstract_untl_preserves_S_free a x y p hsep.1,
            abstract_untl_preserves_S_free b x y p hsep.2]
  | snce a b _ih1 _ih2 =>
    simp [isSyntacticallySeparated] at hsep
    simp [abstractUntl, isSyntacticallySeparated]
    exact ⟨by rw [abstract_untl_identity_on_U_free a x y p hsep.1]; exact hsep.1,
           by rw [abstract_untl_identity_on_U_free b x y p hsep.2]; exact hsep.2⟩

/-! ### junctionDepth decrease lemmas for abstractSnce -/

/-- abstractSnce does not increase junctionDepth, junctionDepthU, or junctionDepthS. -/
theorem abstract_snce_jd_le_all (phi x y : Formula Atom) (p : Atom) :
    junctionDepth (abstractSnce phi x y p) ≤ junctionDepth phi ∧
    junctionDepthU (abstractSnce phi x y p) ≤ junctionDepthU phi ∧
    junctionDepthS (abstractSnce phi x y p) ≤ junctionDepthS phi := by
  induction phi with
  | atom _ => simp [abstractSnce, junctionDepth, junctionDepthU, junctionDepthS]
  | bot => simp [abstractSnce, junctionDepth, junctionDepthU, junctionDepthS]
  | imp a b ih1 ih2 =>
    simp only [abstractSnce, junctionDepth, junctionDepthU, junctionDepthS]
    omega
  | box a ih =>
    simp only [abstractSnce, junctionDepth, junctionDepthU, junctionDepthS]
    exact ih
  | untl a b ih1 ih2 =>
    simp only [abstractSnce, junctionDepth, junctionDepthU, junctionDepthS]
    omega
  | snce a b ih1 ih2 =>
    simp only [abstractSnce]
    split
    · simp only [junctionDepth, junctionDepthU, junctionDepthS]
      omega
    · simp only [junctionDepth, junctionDepthU, junctionDepthS]
      obtain ⟨h1a, h1b, h1c⟩ := ih1
      obtain ⟨h2a, h2b, h2c⟩ := ih2
      omega

/-- abstractSnce does not increase junctionDepth. -/
theorem abstract_snce_jd_le (phi x y : Formula Atom) (p : Atom) :
    junctionDepth (abstractSnce phi x y p) ≤ junctionDepth phi :=
  (abstract_snce_jd_le_all phi x y p).1

/-- abstractSnce does not increase junctionDepthU. -/
theorem abstract_snce_jdU_le (phi x y : Formula Atom) (p : Atom) :
    junctionDepthU (abstractSnce phi x y p) ≤ junctionDepthU phi :=
  (abstract_snce_jd_le_all phi x y p).2.1

/-- abstractSnce does not increase junctionDepthS. -/
theorem abstract_snce_jdS_le (phi x y : Formula Atom) (p : Atom) :
    junctionDepthS (abstractSnce phi x y p) ≤ junctionDepthS phi :=
  (abstract_snce_jd_le_all phi x y p).2.2

/-- Abstracting S(A,B) when it occurs directly at the root as a snce node drops jdU. -/
theorem jdU_abstract_snce_snce_lt (x y : Formula Atom) (p : Atom) :
    junctionDepthU (abstractSnce (.snce x y) x y p) < junctionDepthU (.snce x y) := by
  simp only [abstractSnce]
  split
  · simp only [junctionDepthU]; omega
  · next h => exact absurd ⟨trivial, trivial⟩ h

/-- Predicate: S(A,B) appears directly in φ in a position reachable via junctionDepthU
    tracking. -/
def snceAchievesMaxJdU : Formula Atom → Formula Atom → Formula Atom → Prop
  | .untl a b, x, y =>
      (a = .snce x y ∧ junctionDepthU (.snce x y) ≥ junctionDepthU b) ∨
      (b = .snce x y ∧ junctionDepthU (.snce x y) ≥ junctionDepthU a) ∨
      (snceAchievesMaxJdU a x y ∧ junctionDepthU a ≥ junctionDepthU b) ∨
      (snceAchievesMaxJdU b x y ∧ junctionDepthU b ≥ junctionDepthU a)
  | _, _, _ => False

/-- Predicate: S(A,B) appears in the U-argument of a `.untl` node. -/
def snceInsideUArg : Formula Atom → Formula Atom → Formula Atom → Prop
  | .untl a b, x, y =>
      a = .snce x y ∨ b = .snce x y ∨
      snceInsideUArg a x y ∨ snceInsideUArg b x y
  | _, _, _ => False

/-- Key lemma: abstracting S(A,B) from the LEFT U-argument when jdU a STRICTLY exceeds
    jdU b strictly decreases junctionDepthU of `.untl a b`. -/
theorem abstract_snce_untl_jdU_lt_left (a b x y : Formula Atom) (p : Atom)
    (h_a_dec : junctionDepthU (abstractSnce a x y p) < junctionDepthU a)
    (h_max : junctionDepthU a > junctionDepthU b) :
    junctionDepthU (abstractSnce (.untl a b) x y p) < junctionDepthU (.untl a b) := by
  simp only [abstractSnce, junctionDepthU]
  have hle_b := abstract_snce_jdU_le b x y p
  apply Nat.max_lt.mpr; constructor
  · exact Nat.lt_of_lt_of_le h_a_dec (Nat.le_max_left _ _)
  · exact Nat.lt_of_le_of_lt hle_b (Nat.lt_of_lt_of_le h_max (Nat.le_max_left _ _))

/-- Key lemma: abstracting S(A,B) from the RIGHT U-argument. -/
theorem abstract_snce_untl_jdU_lt_right (a b x y : Formula Atom) (p : Atom)
    (h_b_dec : junctionDepthU (abstractSnce b x y p) < junctionDepthU b)
    (h_max : junctionDepthU b > junctionDepthU a) :
    junctionDepthU (abstractSnce (.untl a b) x y p) < junctionDepthU (.untl a b) := by
  simp only [abstractSnce, junctionDepthU]
  have hle_a := abstract_snce_jdU_le a x y p
  apply Nat.max_lt.mpr; constructor
  · exact Nat.lt_of_le_of_lt hle_a (Nat.lt_of_lt_of_le h_max (Nat.le_max_right _ _))
  · exact Nat.lt_of_lt_of_le h_b_dec (Nat.le_max_right _ _)

/-- Version when jdU a = jdU b and BOTH branches decrease. -/
theorem abstract_snce_untl_jdU_lt_both (a b x y : Formula Atom) (p : Atom)
    (h_a_dec : junctionDepthU (abstractSnce a x y p) < junctionDepthU a)
    (h_b_dec : junctionDepthU (abstractSnce b x y p) < junctionDepthU b) :
    junctionDepthU (abstractSnce (.untl a b) x y p) < junctionDepthU (.untl a b) := by
  simp only [abstractSnce, junctionDepthU]
  apply Nat.max_lt.mpr; constructor
  · exact Nat.lt_of_lt_of_le h_a_dec (Nat.le_max_left _ _)
  · exact Nat.lt_of_lt_of_le h_b_dec (Nat.le_max_right _ _)

/-- Direct case: abstracting S(A,B) when it IS the left U-arg and strictly dominates. -/
theorem abstract_snce_untl_left_snce_jdU_lt (b x y : Formula Atom) (p : Atom)
    (h_max : junctionDepthU (.snce x y) > junctionDepthU b) :
    junctionDepthU (abstractSnce (.untl (.snce x y) b) x y p) <
    junctionDepthU (.untl (.snce x y) b) :=
  abstract_snce_untl_jdU_lt_left _ _ _ _ _ (jdU_abstract_snce_snce_lt x y p) h_max

/-- Direct case: abstracting S(A,B) when it IS the right U-arg and strictly dominates. -/
theorem abstract_snce_untl_right_snce_jdU_lt (a x y : Formula Atom) (p : Atom)
    (h_max : junctionDepthU (.snce x y) > junctionDepthU a) :
    junctionDepthU (abstractSnce (.untl a (.snce x y)) x y p) <
    junctionDepthU (.untl a (.snce x y)) :=
  abstract_snce_untl_jdU_lt_right _ _ _ _ _ (jdU_abstract_snce_snce_lt x y p) h_max

/-- Direct case: abstracting S(A,B) from both sides when they are equal. -/
theorem abstract_snce_untl_both_snce_jdU_lt (x y : Formula Atom) (p : Atom) :
    junctionDepthU (abstractSnce (.untl (.snce x y) (.snce x y)) x y p) <
    junctionDepthU (.untl (.snce x y) (.snce x y)) :=
  abstract_snce_untl_jdU_lt_both _ _ _ _ _
    (jdU_abstract_snce_snce_lt x y p) (jdU_abstract_snce_snce_lt x y p)

/-- Key theorem: abstracting S(A,B) from the U-argument that achieves
    the maximum jdU decreases junctionDepth of the whole `.untl` node. -/
theorem abstract_snce_inside_untl_jd_lt (a b x y : Formula Atom) (p : Atom)
    (h : (junctionDepthU (abstractSnce a x y p) < junctionDepthU a ∧
          junctionDepthU a > junctionDepthU b)
      ∨ (junctionDepthU (abstractSnce b x y p) < junctionDepthU b ∧
          junctionDepthU b > junctionDepthU a)
      ∨ (junctionDepthU (abstractSnce a x y p) < junctionDepthU a ∧
          junctionDepthU (abstractSnce b x y p) < junctionDepthU b)) :
    junctionDepth (abstractSnce (.untl a b) x y p) < junctionDepth (.untl a b) := by
  simp only [abstractSnce, junctionDepth]
  rcases h with ⟨hlt_a, hgt⟩ | ⟨hlt_b, hgt⟩ | ⟨hlt_a, hlt_b⟩
  · have := abstract_snce_untl_jdU_lt_left a b x y p hlt_a hgt
    simp only [abstractSnce, junctionDepthU] at this; exact this
  · have := abstract_snce_untl_jdU_lt_right a b x y p hlt_b hgt
    simp only [abstractSnce, junctionDepthU] at this; exact this
  · have := abstract_snce_untl_jdU_lt_both a b x y p hlt_a hlt_b
    simp only [abstractSnce, junctionDepthU] at this; exact this

/-! ### GHR94-Faithful Strengthening: Separation preserving single U-type -/

/-- Stronger separability: separated equivalent with preserved single U-type. -/
def isSeparableWithUType (φ x y : Formula Atom) : Prop :=
  ∃ ψ : Formula Atom, isSyntacticallySeparated ψ = true ∧ intEquiv φ ψ ∧ hasSingleUType ψ x y

/-- isSeparableWithUType implies isSeparable. -/
theorem separable_with_type_imp_separable {φ x y : Formula Atom}
    (h : isSeparableWithUType φ x y) : isSeparable φ := by
  obtain ⟨ψ, hsep, hequiv, _⟩ := h
  exact ⟨ψ, hsep, hequiv⟩

/-- Equivalence transfer for isSeparableWithUType. -/
theorem is_separable_with_U_type_of_equiv {φ χ x y : Formula Atom}
    (hequiv : intEquiv φ χ) (h : isSeparableWithUType χ x y) :
    isSeparableWithUType φ x y := by
  obtain ⟨ψ, hsep, hequiv2, hsingle⟩ := h
  exact ⟨ψ, hsep, int_equiv_trans hequiv hequiv2, hsingle⟩

/-- imp preserves isSeparableWithUType. -/
theorem imp_separable_with_type {a b x y : Formula Atom}
    (ha : isSeparableWithUType a x y) (hb : isSeparableWithUType b x y) :
    isSeparableWithUType (.imp a b) x y := by
  obtain ⟨ψa, hsepa, hequiva, hsinglea⟩ := ha
  obtain ⟨ψb, hsepb, hequivb, hsingleb⟩ := hb
  exact ⟨.imp ψa ψb, by simp [isSyntacticallySeparated, hsepa, hsepb],
         fun m t => ⟨fun h hp => (hequivb m t).mp (h ((hequiva m t).mpr hp)),
                     fun h hp => (hequivb m t).mpr (h ((hequiva m t).mp hp))⟩,
         ⟨hsinglea, hsingleb⟩⟩

/-- U-free formulas are separable_with_U_type (vacuously). -/
theorem u_free_separable_with_type {φ x y : Formula Atom} (h : isUFree φ = true) :
    isSeparableWithUType φ x y := by
  have hsep := separated_imp_separable φ (restricted_u_free_separated φ (has_no_allpast_allfuture_true φ) h)
  obtain ⟨ψ, hsep_ψ, hequiv⟩ := hsep
  exact ⟨φ, by {
    exact restricted_u_free_separated φ (has_no_allpast_allfuture_true φ) h
  }, int_equiv_refl φ, u_free_has_single_U_type h⟩

/-- .untl A B with S-free args is separable_with_U_type. -/
theorem untl_s_free_separable_with_type {x y : Formula Atom}
    (hx_sf : isSFree x = true) (hy_sf : isSFree y = true) :
    isSeparableWithUType (.untl x y) x y := by
  exact ⟨.untl x y, by simp [isSyntacticallySeparated, hx_sf, hy_sf],
         int_equiv_refl _, has_single_U_type_untl x y⟩

/-! ### Combinators for isSeparableWithUType -/

/-- or preserves isSeparableWithUType. -/
theorem or_separable_with_U_type {a b x y : Formula Atom}
    (ha : isSeparableWithUType a x y) (hb : isSeparableWithUType b x y) :
    isSeparableWithUType (Formula.or a b) x y := by
  obtain ⟨ψa, hsepa, hequiva, hsinglea⟩ := ha
  obtain ⟨ψb, hsepb, hequivb, hsingleb⟩ := hb
  refine ⟨Formula.or ψa ψb, ?_, ?_, ?_⟩
  · simp [Formula.or, Formula.neg, isSyntacticallySeparated, hsepa, hsepb]
  · intro m t; constructor
    · intro h; rcases int_truth_or_iff.mp h with hp | hq
      · exact int_truth_or_iff.mpr (Or.inl ((hequiva m t).mp hp))
      · exact int_truth_or_iff.mpr (Or.inr ((hequivb m t).mp hq))
    · intro h; rcases int_truth_or_iff.mp h with hp | hq
      · exact int_truth_or_iff.mpr (Or.inl ((hequiva m t).mpr hp))
      · exact int_truth_or_iff.mpr (Or.inr ((hequivb m t).mpr hq))
  · exact has_single_U_type_or hsinglea hsingleb

/-- and preserves isSeparableWithUType. -/
theorem and_separable_with_U_type {a b x y : Formula Atom}
    (ha : isSeparableWithUType a x y) (hb : isSeparableWithUType b x y) :
    isSeparableWithUType (Formula.and a b) x y := by
  obtain ⟨ψa, hsepa, hequiva, hsinglea⟩ := ha
  obtain ⟨ψb, hsepb, hequivb, hsingleb⟩ := hb
  refine ⟨Formula.and ψa ψb, and_separated hsepa hsepb, ?_, has_single_U_type_and hsinglea hsingleb⟩
  intro m t; constructor
  · intro h; rw [int_truth_and_iff] at h ⊢
    exact ⟨(hequiva m t).mp h.1, (hequivb m t).mp h.2⟩
  · intro h; rw [int_truth_and_iff] at h ⊢
    exact ⟨(hequiva m t).mpr h.1, (hequivb m t).mpr h.2⟩

/-- neg preserves isSeparableWithUType. -/
theorem neg_separable_with_U_type {a x y : Formula Atom}
    (ha : isSeparableWithUType a x y) :
    isSeparableWithUType (Formula.neg a) x y := by
  obtain ⟨ψa, hsepa, hequiva, hsinglea⟩ := ha
  refine ⟨Formula.neg ψa, neg_separated hsepa, ?_, has_single_U_type_neg hsinglea⟩
  intro m t; constructor
  · intro hn hp; exact hn ((hequiva m t).mpr hp)
  · intro hn hp; exact hn ((hequiva m t).mp hp)

/-! ### U-Type Argument Replacement Bridge -/

/-- Replace U-type arguments in a formula: every `.untl _ _` node gets new arguments. -/
def replaceUntlArgs (ψ x_new y_new : Formula Atom) : Formula Atom :=
  match ψ with
  | .atom a => .atom a
  | .bot => .bot
  | .imp p q => .imp (replaceUntlArgs p x_new y_new) (replaceUntlArgs q x_new y_new)
  | .box p => .box (replaceUntlArgs p x_new y_new)
  | .untl _ _ => .untl x_new y_new
  | .snce p q => .snce (replaceUntlArgs p x_new y_new) (replaceUntlArgs q x_new y_new)

/-- `replaceUntlArgs` produces `hasSingleUType _ A_new B_new`. -/
theorem replace_untl_args_has_single_U_type (ψ x_new y_new : Formula Atom) :
    hasSingleUType (replaceUntlArgs ψ x_new y_new) x_new y_new := by
  induction ψ with
  | atom _ => exact trivial
  | bot => exact trivial
  | imp _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | box _ ih => exact ih
  | untl _ _ => exact ⟨rfl, rfl⟩
  | snce _ _ ih1 ih2 => exact ⟨ih1, ih2⟩

/-- For U-free formulas, `replaceUntlArgs` is the identity. -/
theorem replace_untl_args_u_free_eq (ψ x_new y_new : Formula Atom)
    (h : isUFree ψ = true) : replaceUntlArgs ψ x_new y_new = ψ := by
  induction ψ with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ih1 ih2 =>
    simp [isUFree] at h
    simp [replaceUntlArgs, ih1 h.1, ih2 h.2]
  | box _ ih =>
    simp [isUFree] at h
    simp [replaceUntlArgs, ih h]
  | untl _ _ => simp [isUFree] at h
  | snce _ _ ih1 ih2 =>
    simp [isUFree] at h
    simp [replaceUntlArgs, ih1 h.1, ih2 h.2]

/-- `replaceUntlArgs` preserves `isSFree` when the new arguments are S-free. -/
theorem replace_untl_args_preserves_S_free (ψ x_new y_new : Formula Atom)
    (h : isSFree ψ = true) (hx : isSFree x_new = true) (hy : isSFree y_new = true) :
    isSFree (replaceUntlArgs ψ x_new y_new) = true := by
  induction ψ with
  | atom _ => simp [replaceUntlArgs, isSFree]
  | bot => rfl
  | imp _ _ ih1 ih2 =>
    simp [isSFree] at h; simp [replaceUntlArgs, isSFree, ih1 h.1, ih2 h.2]
  | box _ ih =>
    simp [isSFree] at h; simp [replaceUntlArgs, isSFree, ih h]
  | untl _ _ =>
    simp [replaceUntlArgs, isSFree, hx, hy]
  | snce _ _ => simp [isSFree] at h

/-- `replaceUntlArgs` preserves `isSyntacticallySeparated`. -/
theorem replace_untl_args_preserves_separated (ψ x_new y_new : Formula Atom)
    (h_sep : isSyntacticallySeparated ψ = true)
    (hx_sf : isSFree x_new = true) (hy_sf : isSFree y_new = true) :
    isSyntacticallySeparated (replaceUntlArgs ψ x_new y_new) = true := by
  induction ψ with
  | atom _ => simp [replaceUntlArgs, isSyntacticallySeparated]
  | bot => rfl
  | imp _ _ ih1 ih2 =>
    simp [isSyntacticallySeparated] at h_sep
    simp [replaceUntlArgs, isSyntacticallySeparated, ih1 h_sep.1, ih2 h_sep.2]
  | box _ => simp [replaceUntlArgs, isSyntacticallySeparated]
  | untl _ _ =>
    simp [replaceUntlArgs, isSyntacticallySeparated, hx_sf, hy_sf]
  | snce p q ih1 ih2 =>
    simp [isSyntacticallySeparated] at h_sep
    simp only [replaceUntlArgs, isSyntacticallySeparated]
    rw [replace_untl_args_u_free_eq p x_new y_new h_sep.1,
        replace_untl_args_u_free_eq q x_new y_new h_sep.2]
    simp [h_sep.1, h_sep.2]

/-- `replaceUntlArgs` preserves `intEquiv` when `hasSingleUType ψ A_old B_old`
    and `intEquiv A_old A_new` and `intEquiv B_old B_new`. -/
theorem replace_untl_args_equiv (ψ x_old y_old x_new y_new : Formula Atom)
    (h_single : hasSingleUType ψ x_old y_old)
    (hx_equiv : intEquiv x_old x_new) (hy_equiv : intEquiv y_old y_new) :
    intEquiv ψ (replaceUntlArgs ψ x_new y_new) := by
  induction ψ with
  | atom _ => intro m t; rfl
  | bot => intro m t; rfl
  | imp p q ih1 ih2 =>
    obtain ⟨h1, h2⟩ := h_single
    intro m t; simp only [replaceUntlArgs, intTruth]
    exact Iff.imp (ih1 h1 m t) (ih2 h2 m t)
  | box _ ih =>
    intro m t; simp only [replaceUntlArgs, intTruth]
  | untl p q =>
    obtain ⟨hp, hq⟩ := h_single
    subst hp; subst hq
    intro m t; simp only [replaceUntlArgs, intTruth]
    constructor
    · rintro ⟨s, hts, h1, h2⟩
      exact ⟨s, hts, (hx_equiv m s).mp h1,
        fun r hr1 hr2 => (hy_equiv m r).mp (h2 r hr1 hr2)⟩
    · rintro ⟨s, hts, h1, h2⟩
      exact ⟨s, hts, (hx_equiv m s).mpr h1,
        fun r hr1 hr2 => (hy_equiv m r).mpr (h2 r hr1 hr2)⟩
  | snce p q ih1 ih2 =>
    obtain ⟨h1, h2⟩ := h_single
    intro m t; simp only [replaceUntlArgs, intTruth]
    constructor
    · rintro ⟨s, hst, h1', h2'⟩
      exact ⟨s, hst, (ih1 h1 m s).mp h1',
        fun r hr1 hr2 => (ih2 h2 m r).mp (h2' r hr1 hr2)⟩
    · rintro ⟨s, hst, h1', h2'⟩
      exact ⟨s, hst, (ih1 h1 m s).mpr h1',
        fun r hr1 hr2 => (ih2 h2 m r).mpr (h2' r hr1 hr2)⟩

/-- Bridge lemma: convert `isSeparableWithUType φ A' B'` to
    `isSeparableWithUType φ A B`. -/
theorem is_separable_with_U_type_replace_args {φ x x' y y' : Formula Atom}
    (h : isSeparableWithUType φ x' y')
    (hx_equiv : intEquiv x x') (hy_equiv : intEquiv y y')
    (hx_sf : isSFree x = true) (hy_sf : isSFree y = true) :
    isSeparableWithUType φ x y := by
  obtain ⟨ψ, h_sep, h_equiv, h_single⟩ := h
  exact ⟨replaceUntlArgs ψ x y,
    replace_untl_args_preserves_separated ψ x y h_sep hx_sf hy_sf,
    int_equiv_trans h_equiv (replace_untl_args_equiv ψ x' y' x y h_single
      (int_equiv_symm hx_equiv) (int_equiv_symm hy_equiv)),
    replace_untl_args_has_single_U_type ψ x y⟩

end DecEq

end Cslib.Logic.Bimodal.Metalogic.Separation
