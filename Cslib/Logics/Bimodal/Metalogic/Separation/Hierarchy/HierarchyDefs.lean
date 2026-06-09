/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Separation.NormalForm
import Cslib.Logics.Bimodal.Metalogic.Separation.TemporalClosure
import Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.Cases
import Cslib.Logics.Bimodal.Metalogic.Separation.FormulaOps

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

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Helper Lemmas for int_truth -/

theorem int_truth_and_iff {M : IntStructure Atom} {t : ℤ} {φ ψ : Formula Atom} :
    int_truth M t (Formula.and φ ψ) ↔ int_truth M t φ ∧ int_truth M t ψ :=
  int_truth_and M t φ ψ

theorem int_truth_or_iff {M : IntStructure Atom} {t : ℤ} {φ ψ : Formula Atom} :
    int_truth M t (Formula.or φ ψ) ↔ int_truth M t φ ∨ int_truth M t ψ :=
  int_truth_or M t φ ψ

theorem int_truth_neg_iff {M : IntStructure Atom} {t : ℤ} {φ : Formula Atom} :
    int_truth M t (Formula.neg φ) ↔ ¬ int_truth M t φ :=
  int_truth_neg M t φ

/-! ## Predicate: Formula has Single U-Type

A formula has "single U-type U(A,B)" if every `untl` subformula in it
has arguments exactly A and B. This captures the condition for Lemma 10.2.5. -/

/-- A formula has single U-type: every `untl` node has exactly arguments (A, B). -/
def has_single_U_type (φ x y : Formula Atom) : Prop :=
  match φ with
  | .atom _ => True
  | .bot => True
  | .imp ψ₁ ψ₂ => has_single_U_type ψ₁ x y ∧ has_single_U_type ψ₂ x y
  | .box ψ => has_single_U_type ψ x y
  | .untl ψ₁ ψ₂ => ψ₁ = x ∧ ψ₂ = y
  | .snce ψ₁ ψ₂ => has_single_U_type ψ₁ x y ∧ has_single_U_type ψ₂ x y

/-- A formula is U-free implies it trivially has single U-type (vacuously). -/
theorem u_free_has_single_U_type {φ x y : Formula Atom} (h : is_U_free φ = true) :
    has_single_U_type φ x y := by
  induction φ with
  | atom _ => trivial
  | bot => trivial
  | imp ψ₁ ψ₂ ih1 ih2 =>
    simp [is_U_free] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box ψ ih =>
    simp [is_U_free] at h
    exact ih h
  | untl _ _ => simp [is_U_free] at h
  | snce ψ₁ ψ₂ ih1 ih2 =>
    simp [is_U_free] at h
    exact ⟨ih1 h.1, ih2 h.2⟩

/-! ## Single-S-Type Predicate (dual of has_single_U_type) -/

/-- A formula has single S-type: every `snce` node has exactly arguments (A, B). -/
def has_single_S_type (φ x y : Formula Atom) : Prop :=
  match φ with
  | .atom _ => True
  | .bot => True
  | .imp ψ₁ ψ₂ => has_single_S_type ψ₁ x y ∧ has_single_S_type ψ₂ x y
  | .box ψ => has_single_S_type ψ x y
  | .untl ψ₁ ψ₂ => has_single_S_type ψ₁ x y ∧ has_single_S_type ψ₂ x y
  | .snce ψ₁ ψ₂ => ψ₁ = x ∧ ψ₂ = y

/-- A formula is S-free implies it trivially has single S-type (vacuously). -/
theorem s_free_has_single_S_type {φ x y : Formula Atom} (h : is_S_free φ = true) :
    has_single_S_type φ x y := by
  induction φ with
  | atom _ => trivial
  | bot => trivial
  | imp ψ₁ ψ₂ ih1 ih2 =>
    simp [is_S_free] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box ψ ih =>
    simp [is_S_free] at h
    exact ih h
  | snce _ _ => simp [is_S_free] at h
  | untl ψ₁ ψ₂ ih1 ih2 =>
    simp [is_S_free] at h
    exact ⟨ih1 h.1, ih2 h.2⟩

/-! ## Lemma 10.2.5: Single-U Formula Separability -/

/-- Helper: Formula.neg preserves has_single_U_type. -/
theorem has_single_U_type_neg {φ x y : Formula Atom} (h : has_single_U_type φ x y) :
    has_single_U_type (Formula.neg φ) x y := by
  simp [Formula.neg, has_single_U_type]
  exact h

/-- Helper: Formula.and preserves has_single_U_type. -/
theorem has_single_U_type_and {φ ψ x y : Formula Atom}
    (h1 : has_single_U_type φ x y) (h2 : has_single_U_type ψ x y) :
    has_single_U_type (Formula.and φ ψ) x y := by
  simp [Formula.and, Formula.neg, has_single_U_type]
  exact ⟨h1, h2⟩

/-- Helper: Formula.or preserves has_single_U_type. -/
theorem has_single_U_type_or {φ ψ x y : Formula Atom}
    (h1 : has_single_U_type φ x y) (h2 : has_single_U_type ψ x y) :
    has_single_U_type (Formula.or φ ψ) x y := by
  simp [Formula.or, Formula.neg, has_single_U_type]
  exact ⟨h1, h2⟩

/-- Helper: U(A,B) trivially has single U-type U(A,B). -/
theorem has_single_U_type_untl (x y : Formula Atom) :
    has_single_U_type (.untl x y) x y :=
  ⟨rfl, rfl⟩

/-- Helper: snce preserves has_single_U_type. -/
theorem has_single_U_type_snce {φ ψ x y : Formula Atom}
    (h1 : has_single_U_type φ x y) (h2 : has_single_U_type ψ x y) :
    has_single_U_type (.snce φ ψ) x y := ⟨h1, h2⟩

/-- Helper: imp preserves has_single_U_type. -/
theorem has_single_U_type_imp {φ ψ x y : Formula Atom}
    (h1 : has_single_U_type φ x y) (h2 : has_single_U_type ψ x y) :
    has_single_U_type (.imp φ ψ) x y := ⟨h1, h2⟩

/-- U(A,B) with S-free A, B is itself syntactically separated. -/
theorem untl_s_free_separated {x y : Formula Atom}
    (hx : is_S_free x = true) (hy : is_S_free y = true) :
    is_syntactically_separated (.untl x y) = true := by
  simp [is_syntactically_separated, hx, hy]

/-- U(A,B) with S-free A, B is separable. -/
theorem untl_s_free_separable {x y : Formula Atom}
    (hx : is_S_free x = true) (hy : is_S_free y = true) :
    is_separable (.untl x y) :=
  ⟨.untl x y, untl_s_free_separated hx hy, int_equiv_refl _⟩

/-! ## Lemma 10.2.6: Multi-U Induction on Count (GHR94) -/

/-! ### U-Formula Abstraction -/

section DecEq
variable [DecidableEq Atom]

/-- Replace all occurrences of `untl A B` in `phi` with atom `p`. -/
def abstract_untl (phi x y : Formula Atom) (p : Atom) : Formula Atom :=
  match phi with
  | .atom a => .atom a
  | .bot => .bot
  | .imp psi1 psi2 => .imp (abstract_untl psi1 x y p) (abstract_untl psi2 x y p)
  | .box psi => .box (abstract_untl psi x y p)
  | .untl psi1 psi2 =>
    if psi1 = x ∧ psi2 = y then .atom p
    else .untl (abstract_untl psi1 x y p) (abstract_untl psi2 x y p)
  | .snce psi1 psi2 => .snce (abstract_untl psi1 x y p) (abstract_untl psi2 x y p)

/-! ### Syntactic Roundtrip: abstract then substitute back -/

/-- Substituting U(A,B) for atom p in the abstracted formula recovers the original,
    provided p does not appear in the original formula. -/
theorem abstract_subst_roundtrip (phi x y : Formula Atom) (p : Atom)
    (hfresh : ¬ (p ∈ phi.atoms)) :
    subst_formula (abstract_untl phi x y p) p (.untl x y) = phi := by
  induction phi with
  | atom a =>
    simp [Formula.atoms, Finset.mem_singleton] at hfresh
    have hne : a ≠ p := Ne.symm hfresh
    simp [abstract_untl, subst_formula, hne]
  | bot => simp [abstract_untl, subst_formula]
  | imp c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp [abstract_untl, subst_formula, ih1 hfresh.1, ih2 hfresh.2]
  | box c ih =>
    simp [Formula.atoms] at hfresh
    simp [abstract_untl, subst_formula, ih hfresh]
  | untl c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp only [abstract_untl]
    split
    · next h => simp [subst_formula, h.1, h.2]
    · next _ =>
      simp only [subst_formula]
      congr 1
      · exact ih1 hfresh.1
      · exact ih2 hfresh.2
  | snce c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp [abstract_untl, subst_formula, ih1 hfresh.1, ih2 hfresh.2]

/-! ### Semantic Correctness of Abstraction -/

/-- Semantic correctness: truth of φ in structure M is equivalent to truth of
    the abstracted formula in M with atom p interpreted as the truth set of U(A,B). -/
theorem abstract_untl_correct (phi x y : Formula Atom) (p : Atom)
    (hfresh : ¬ (p ∈ phi.atoms))
    (m : IntStructure Atom) (t : Int) :
    int_truth m t phi ↔
    int_truth (m.withAtom p {s | int_truth m s (.untl x y)}) t
      (abstract_untl phi x y p) := by
  induction phi generalizing t with
  | atom a =>
    simp [Formula.atoms, Finset.mem_singleton] at hfresh
    simp [abstract_untl, int_truth, IntStructure.withAtom, Ne.symm hfresh]
  | bot => simp [abstract_untl, int_truth]
  | imp c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp only [abstract_untl, int_truth]
    constructor
    · intro h hc; exact (ih2 hfresh.2 t).mp (h ((ih1 hfresh.1 t).mpr hc))
    · intro h hc; exact (ih2 hfresh.2 t).mpr (h ((ih1 hfresh.1 t).mp hc))
  | box _ => simp [abstract_untl, int_truth]
  | untl c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp only [abstract_untl]
    split
    · next h =>
      obtain ⟨hc, hd⟩ := h; subst hc; subst hd
      simp [int_truth, IntStructure.withAtom, Set.mem_setOf_eq]
    · next _ =>
      simp only [int_truth]
      constructor
      · rintro ⟨s, hts, hc, hd⟩
        exact ⟨s, hts, (ih1 hfresh.1 s).mp hc,
          fun r hr1 hr2 => (ih2 hfresh.2 r).mp (hd r hr1 hr2)⟩
      · rintro ⟨s, hts, hc, hd⟩
        exact ⟨s, hts, (ih1 hfresh.1 s).mpr hc,
          fun r hr1 hr2 => (ih2 hfresh.2 r).mpr (hd r hr1 hr2)⟩
  | snce c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp only [abstract_untl, int_truth]
    constructor
    · rintro ⟨s, hst, hc, hd⟩
      exact ⟨s, hst, (ih1 hfresh.1 s).mp hc,
        fun r hr1 hr2 => (ih2 hfresh.2 r).mp (hd r hr1 hr2)⟩
    · rintro ⟨s, hst, hc, hd⟩
      exact ⟨s, hst, (ih1 hfresh.1 s).mpr hc,
        fun r hr1 hr2 => (ih2 hfresh.2 r).mpr (hd r hr1 hr2)⟩

/-- The syntactic roundtrip gives int_equiv directly. -/
theorem abstract_untl_equiv (phi x y : Formula Atom) (p : Atom)
    (hfresh : ¬ (p ∈ phi.atoms)) :
    int_equiv phi (subst_formula (abstract_untl phi x y p) p (.untl x y)) := by
  rw [abstract_subst_roundtrip phi x y p hfresh]
  exact int_equiv_refl phi

/-! ### Preservation Lemmas -/

/-- abstract_untl preserves is_S_free: if φ is S-free, so is the abstracted form. -/
theorem abstract_untl_preserves_S_free (phi x y : Formula Atom) (p : Atom)
    (h : is_S_free phi = true) :
    is_S_free (abstract_untl phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstract_untl, is_S_free]
  | bot => simp [abstract_untl, is_S_free]
  | imp c d ih1 ih2 =>
    simp [is_S_free] at h
    simp [abstract_untl, is_S_free, ih1 h.1, ih2 h.2]
  | box c ih =>
    simp [is_S_free] at h
    simp [abstract_untl, is_S_free, ih h]
  | untl c d ih1 ih2 =>
    simp [is_S_free] at h
    simp only [abstract_untl]
    split
    · simp [is_S_free]
    · simp [is_S_free, ih1 h.1, ih2 h.2]
  | snce _ _ => simp [is_S_free] at h

/-- abstract_untl preserves no_S_nested_in_U. -/
theorem abstract_untl_preserves_no_S_nested (phi x y : Formula Atom) (p : Atom)
    (h : no_S_nested_in_U phi) :
    no_S_nested_in_U (abstract_untl phi x y p) := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp c d ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | box c ih => exact ih h
  | untl c d _ _ =>
    simp only [abstract_untl]
    split
    · trivial
    · have ⟨hc_sf, hd_sf⟩ := h
      exact ⟨abstract_untl_preserves_S_free c x y p hc_sf,
             abstract_untl_preserves_S_free d x y p hd_sf⟩
  | snce c d ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩

/-- If φ has single U-type U(A,B), abstracting it out gives a U-free formula. -/
theorem abstract_untl_makes_U_free (phi x y : Formula Atom) (p : Atom)
    (h : has_single_U_type phi x y) :
    is_U_free (abstract_untl phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstract_untl, is_U_free]
  | bot => simp [abstract_untl, is_U_free]
  | imp c d ih1 ih2 =>
    simp [abstract_untl, is_U_free, ih1 h.1, ih2 h.2]
  | box c ih =>
    simp [abstract_untl, is_U_free, ih h]
  | untl c d _ _ =>
    obtain ⟨hc, hd⟩ := h; subst hc; subst hd
    simp [abstract_untl, is_U_free]
  | snce c d ih1 ih2 =>
    simp [abstract_untl, is_U_free, ih1 h.1, ih2 h.2]

/-! ### Count Properties -/

/-- count_U_subformulas = 0 iff the formula is U-free. -/
theorem count_U_zero_iff_U_free (phi : Formula Atom) :
    count_U_subformulas phi = 0 ↔ is_U_free phi = true := by
  induction phi with
  | atom _ => simp [count_U_subformulas, is_U_free]
  | bot => simp [count_U_subformulas, is_U_free]
  | imp c d ih1 ih2 =>
    simp [count_U_subformulas, is_U_free, ih1, ih2]
  | box c ih =>
    simp [count_U_subformulas, is_U_free, ih]
  | untl c d =>
    simp [count_U_subformulas, is_U_free]
  | snce c d ih1 ih2 =>
    simp [count_U_subformulas, is_U_free, ih1, ih2]

/-- abstract_untl does not increase the U-subformula count. -/
theorem abstract_untl_count_le (phi x y : Formula Atom) (p : Atom) :
    count_U_subformulas (abstract_untl phi x y p) ≤ count_U_subformulas phi := by
  induction phi with
  | atom _ => simp [abstract_untl, count_U_subformulas]
  | bot => simp [abstract_untl, count_U_subformulas]
  | imp c d ih1 ih2 =>
    simp [abstract_untl, count_U_subformulas]
    exact Nat.add_le_add ih1 ih2
  | box c ih =>
    simp [abstract_untl, count_U_subformulas]; exact ih
  | untl c d ih1 ih2 =>
    simp only [abstract_untl, count_U_subformulas]
    split
    · simp [count_U_subformulas]
    · simp only [count_U_subformulas]
      have := Nat.add_le_add ih1 ih2
      omega
  | snce c d ih1 ih2 =>
    simp [abstract_untl, count_U_subformulas]
    exact Nat.add_le_add ih1 ih2

/-- If φ has single U-type, abstracting it reduces count to 0. -/
theorem abstract_untl_count_zero_of_single (phi x y : Formula Atom) (p : Atom)
    (h : has_single_U_type phi x y) :
    count_U_subformulas (abstract_untl phi x y p) = 0 := by
  rw [count_U_zero_iff_U_free]
  exact abstract_untl_makes_U_free phi x y p h

/-! ### S-Formula Abstraction (dual of abstract_untl) -/

/-- Replace all occurrences of `snce A B` in `phi` with atom `p`. -/
def abstract_snce (phi x y : Formula Atom) (p : Atom) : Formula Atom :=
  match phi with
  | .atom a => .atom a
  | .bot => .bot
  | .imp psi1 psi2 => .imp (abstract_snce psi1 x y p) (abstract_snce psi2 x y p)
  | .box psi => .box (abstract_snce psi x y p)
  | .untl psi1 psi2 => .untl (abstract_snce psi1 x y p) (abstract_snce psi2 x y p)
  | .snce psi1 psi2 =>
    if psi1 = x ∧ psi2 = y then .atom p
    else .snce (abstract_snce psi1 x y p) (abstract_snce psi2 x y p)

/-- Semantic correctness of abstract_snce. -/
theorem abstract_snce_correct (phi x y : Formula Atom) (p : Atom)
    (m : IntStructure Atom) (t : ℤ)
    (h_eq : m.val p = {s | int_truth m s (.snce x y)}) :
    int_truth m t (abstract_snce phi x y p) ↔ int_truth m t phi := by
  induction phi generalizing t with
  | atom a =>
    simp only [abstract_snce, int_truth]
  | bot => simp [abstract_snce, int_truth]
  | imp c d ih1 ih2 =>
    simp only [abstract_snce, int_truth]
    exact Iff.imp (ih1 t) (ih2 t)
  | box _ => simp [abstract_snce, int_truth]
  | untl c d ih1 ih2 =>
    simp only [abstract_snce, int_truth]
    constructor
    · rintro ⟨s, hts, hc, hd⟩
      exact ⟨s, hts, (ih1 s).mp hc,
        fun r hr1 hr2 => (ih2 r).mp (hd r hr1 hr2)⟩
    · rintro ⟨s, hts, hc, hd⟩
      exact ⟨s, hts, (ih1 s).mpr hc,
        fun r hr1 hr2 => (ih2 r).mpr (hd r hr1 hr2)⟩
  | snce c d ih1 ih2 =>
    simp only [abstract_snce]
    split
    · next h =>
      obtain ⟨hc, hd⟩ := h; subst hc; subst hd
      simp [int_truth, Set.mem_setOf_eq, h_eq]
    · next hne =>
      simp only [int_truth]
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
    subst_formula (abstract_snce phi x y p) p (.snce x y) = phi := by
  induction phi with
  | atom a =>
    simp [Formula.atoms, Finset.mem_singleton] at hfresh
    have hne : a ≠ p := Ne.symm hfresh
    simp [abstract_snce, subst_formula, hne]
  | bot => simp [abstract_snce, subst_formula]
  | imp c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp [abstract_snce, subst_formula, ih1 hfresh.1, ih2 hfresh.2]
  | box c ih =>
    simp [Formula.atoms] at hfresh
    simp [abstract_snce, subst_formula, ih hfresh]
  | untl c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp [abstract_snce, subst_formula, ih1 hfresh.1, ih2 hfresh.2]
  | snce c d ih1 ih2 =>
    simp [Formula.atoms, Finset.mem_union] at hfresh
    simp only [abstract_snce]
    split
    · next h => simp [subst_formula, h.1, h.2]
    · next _ =>
      simp only [subst_formula]
      congr 1
      · exact ih1 hfresh.1
      · exact ih2 hfresh.2

/-! ### Preservation Lemmas for abstract_snce -/

/-- abstract_snce preserves is_U_free. -/
theorem abstract_snce_preserves_U_free (phi x y : Formula Atom) (p : Atom)
    (h : is_U_free phi = true) :
    is_U_free (abstract_snce phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstract_snce, is_U_free]
  | bot => simp [abstract_snce, is_U_free]
  | imp c d ih1 ih2 =>
    simp [is_U_free] at h
    simp [abstract_snce, is_U_free, ih1 h.1, ih2 h.2]
  | box c ih =>
    simp [is_U_free] at h
    simp [abstract_snce, is_U_free, ih h]
  | untl _ _ => simp [is_U_free] at h
  | snce c d ih1 ih2 =>
    simp [is_U_free] at h
    simp only [abstract_snce]
    split
    · simp [is_U_free]
    · simp [is_U_free, ih1 h.1, ih2 h.2]

/-- abstract_snce preserves is_S_free. -/
theorem abstract_snce_preserves_S_free (phi x y : Formula Atom) (p : Atom)
    (h : is_S_free phi = true) :
    is_S_free (abstract_snce phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstract_snce, is_S_free]
  | bot => simp [abstract_snce, is_S_free]
  | imp c d ih1 ih2 =>
    simp [is_S_free] at h
    simp [abstract_snce, is_S_free, ih1 h.1, ih2 h.2]
  | box c ih =>
    simp [is_S_free] at h
    simp [abstract_snce, is_S_free, ih h]
  | untl c d ih1 ih2 =>
    simp [is_S_free] at h
    simp [abstract_snce, is_S_free, ih1 h.1, ih2 h.2]
  | snce _ _ => simp [is_S_free] at h

/-- If φ has no U nested in S, abstracting S(A,B) preserves this property. -/
theorem abstract_snce_preserves_no_U_nested (phi x y : Formula Atom) (p : Atom)
    (h : no_U_nested_in_S phi) :
    no_U_nested_in_S (abstract_snce phi x y p) := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp c d ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | box c ih => exact ih h
  | untl c d ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | snce c d _ _ =>
    simp only [abstract_snce]
    split
    · trivial
    · have ⟨hc_uf, hd_uf⟩ := h
      exact ⟨abstract_snce_preserves_U_free c x y p hc_uf,
             abstract_snce_preserves_U_free d x y p hd_uf⟩

/-- If φ has single S-type S(A,B), abstracting it gives a S-free formula. -/
theorem abstract_snce_makes_S_free (phi x y : Formula Atom) (p : Atom)
    (h : has_single_S_type phi x y) :
    is_S_free (abstract_snce phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstract_snce, is_S_free]
  | bot => simp [abstract_snce, is_S_free]
  | imp c d ih1 ih2 =>
    simp [abstract_snce, is_S_free, ih1 h.1, ih2 h.2]
  | box c ih =>
    simp [abstract_snce, is_S_free, ih h]
  | untl c d ih1 ih2 =>
    simp [abstract_snce, is_S_free, ih1 h.1, ih2 h.2]
  | snce c d _ _ =>
    obtain ⟨hc, hd⟩ := h; subst hc; subst hd
    simp [abstract_snce, is_S_free]

/-! ### Junction-Depth Monotonicity Lemmas -/

/-- joint 4-way bound relating junction_depth, junction_depth_U, junction_depth_S. -/
private theorem junction_depth_bounds (φ : Formula Atom) :
    junction_depth φ ≤ junction_depth_U φ ∧
    junction_depth φ ≤ junction_depth_S φ ∧
    junction_depth_U φ ≤ 1 + junction_depth φ ∧
    junction_depth_S φ ≤ 1 + junction_depth φ := by
  induction φ with
  | atom _ => simp [junction_depth, junction_depth_U, junction_depth_S]
  | bot => simp [junction_depth, junction_depth_U, junction_depth_S]
  | imp a b ih1 ih2 =>
    simp only [junction_depth, junction_depth_U, junction_depth_S]
    omega
  | box a ih => simp [junction_depth, junction_depth_U, junction_depth_S, ih.1, ih.2.1, ih.2.2.1, ih.2.2.2]
  | untl a b ih1 ih2 =>
    simp only [junction_depth, junction_depth_U, junction_depth_S]
    omega
  | snce a b ih1 ih2 =>
    simp only [junction_depth, junction_depth_U, junction_depth_S]
    omega

/-- junction_depth is bounded above by junction_depth_U. -/
theorem junction_depth_le_jdU (φ : Formula Atom) : junction_depth φ ≤ junction_depth_U φ :=
  (junction_depth_bounds φ).1

/-- junction_depth is bounded above by junction_depth_S. -/
theorem junction_depth_le_jdS (φ : Formula Atom) : junction_depth φ ≤ junction_depth_S φ :=
  (junction_depth_bounds φ).2.1

theorem jd_imp_le_left (φ ψ : Formula Atom) : junction_depth φ ≤ junction_depth (.imp φ ψ) :=
  Nat.le_max_left _ _

theorem jd_imp_le_right (φ ψ : Formula Atom) : junction_depth ψ ≤ junction_depth (.imp φ ψ) :=
  Nat.le_max_right _ _

theorem jd_box_le (φ : Formula Atom) : junction_depth φ ≤ junction_depth (.box φ) :=
  Nat.le_refl _

theorem jd_untl_le_left (φ ψ : Formula Atom) : junction_depth φ ≤ junction_depth (.untl φ ψ) := by
  simp only [junction_depth]
  exact Nat.le_trans (junction_depth_le_jdU φ) (Nat.le_max_left _ _)

theorem jd_untl_le_right (φ ψ : Formula Atom) : junction_depth ψ ≤ junction_depth (.untl φ ψ) := by
  simp only [junction_depth]
  exact Nat.le_trans (junction_depth_le_jdU ψ) (Nat.le_max_right _ _)

theorem jd_snce_le_left (φ ψ : Formula Atom) : junction_depth φ ≤ junction_depth (.snce φ ψ) := by
  simp only [junction_depth]
  exact Nat.le_trans (junction_depth_le_jdS φ) (Nat.le_max_left _ _)

theorem jd_snce_le_right (φ ψ : Formula Atom) : junction_depth ψ ≤ junction_depth (.snce φ ψ) := by
  simp only [junction_depth]
  exact Nat.le_trans (junction_depth_le_jdS ψ) (Nat.le_max_right _ _)

/-! ### abstract_untl Identity and Preservation -/

/-- abstract_untl is the identity on U-free formulas. -/
theorem abstract_untl_identity_on_U_free (phi x y : Formula Atom) (p : Atom)
    (h : is_U_free phi = true) :
    abstract_untl phi x y p = phi := by
  induction phi with
  | atom _ => simp [abstract_untl]
  | bot => simp [abstract_untl]
  | imp c d ih1 ih2 => simp [is_U_free] at h; simp [abstract_untl, ih1 h.1, ih2 h.2]
  | box c ih => simp [is_U_free] at h; simp [abstract_untl, ih h]
  | untl _ _ => simp [is_U_free] at h
  | snce c d ih1 ih2 => simp [is_U_free] at h; simp [abstract_untl, ih1 h.1, ih2 h.2]

/-- abstract_untl preserves U-freeness (trivially, since it's identity on U-free). -/
theorem abstract_untl_preserves_U_free (phi x y : Formula Atom) (p : Atom)
    (h : is_U_free phi = true) :
    is_U_free (abstract_untl phi x y p) = true := by
  rw [abstract_untl_identity_on_U_free phi x y p h]; exact h

/-- abstract_untl preserves syntactic separation. -/
theorem abstract_untl_preserves_separated (phi x y : Formula Atom) (p : Atom)
    (hsep : is_syntactically_separated phi = true) :
    is_syntactically_separated (abstract_untl phi x y p) = true := by
  induction phi with
  | atom _ => simp [abstract_untl, is_syntactically_separated]
  | bot => simp [abstract_untl, is_syntactically_separated]
  | imp a b ih1 ih2 =>
    simp [is_syntactically_separated] at hsep
    simp [abstract_untl, is_syntactically_separated, ih1 hsep.1, ih2 hsep.2]
  | box _ => simp [abstract_untl, is_syntactically_separated]
  | untl a b _ih1 _ih2 =>
    simp [is_syntactically_separated] at hsep
    simp only [abstract_untl]
    split
    · simp [is_syntactically_separated]
    · simp [is_syntactically_separated,
            abstract_untl_preserves_S_free a x y p hsep.1,
            abstract_untl_preserves_S_free b x y p hsep.2]
  | snce a b _ih1 _ih2 =>
    simp [is_syntactically_separated] at hsep
    simp [abstract_untl, is_syntactically_separated]
    exact ⟨by rw [abstract_untl_identity_on_U_free a x y p hsep.1]; exact hsep.1,
           by rw [abstract_untl_identity_on_U_free b x y p hsep.2]; exact hsep.2⟩

/-! ### junction_depth decrease lemmas for abstract_snce -/

/-- abstract_snce does not increase junction_depth, junction_depth_U, or junction_depth_S. -/
private theorem abstract_snce_jd_le_all (phi x y : Formula Atom) (p : Atom) :
    junction_depth (abstract_snce phi x y p) ≤ junction_depth phi ∧
    junction_depth_U (abstract_snce phi x y p) ≤ junction_depth_U phi ∧
    junction_depth_S (abstract_snce phi x y p) ≤ junction_depth_S phi := by
  induction phi with
  | atom _ => simp [abstract_snce, junction_depth, junction_depth_U, junction_depth_S]
  | bot => simp [abstract_snce, junction_depth, junction_depth_U, junction_depth_S]
  | imp a b ih1 ih2 =>
    simp only [abstract_snce, junction_depth, junction_depth_U, junction_depth_S]
    omega
  | box a ih =>
    simp only [abstract_snce, junction_depth, junction_depth_U, junction_depth_S]
    exact ih
  | untl a b ih1 ih2 =>
    simp only [abstract_snce, junction_depth, junction_depth_U, junction_depth_S]
    omega
  | snce a b ih1 ih2 =>
    simp only [abstract_snce]
    split
    · simp only [junction_depth, junction_depth_U, junction_depth_S]
      omega
    · simp only [junction_depth, junction_depth_U, junction_depth_S]
      obtain ⟨h1a, h1b, h1c⟩ := ih1
      obtain ⟨h2a, h2b, h2c⟩ := ih2
      omega

/-- abstract_snce does not increase junction_depth. -/
theorem abstract_snce_jd_le (phi x y : Formula Atom) (p : Atom) :
    junction_depth (abstract_snce phi x y p) ≤ junction_depth phi :=
  (abstract_snce_jd_le_all phi x y p).1

/-- abstract_snce does not increase junction_depth_U. -/
theorem abstract_snce_jdU_le (phi x y : Formula Atom) (p : Atom) :
    junction_depth_U (abstract_snce phi x y p) ≤ junction_depth_U phi :=
  (abstract_snce_jd_le_all phi x y p).2.1

/-- abstract_snce does not increase junction_depth_S. -/
theorem abstract_snce_jdS_le (phi x y : Formula Atom) (p : Atom) :
    junction_depth_S (abstract_snce phi x y p) ≤ junction_depth_S phi :=
  (abstract_snce_jd_le_all phi x y p).2.2

/-- Abstracting S(A,B) when it occurs directly at the root as a snce node drops jdU. -/
theorem jdU_abstract_snce_snce_lt (x y : Formula Atom) (p : Atom) :
    junction_depth_U (abstract_snce (.snce x y) x y p) < junction_depth_U (.snce x y) := by
  simp only [abstract_snce]
  split
  · simp only [junction_depth_U]; omega
  · next h => exact absurd ⟨trivial, trivial⟩ h

/-- Predicate: S(A,B) appears directly in φ in a position reachable via junction_depth_U
    tracking. -/
def snce_achieves_max_jdU : Formula Atom → Formula Atom → Formula Atom → Prop
  | .untl a b, x, y =>
      (a = .snce x y ∧ junction_depth_U (.snce x y) ≥ junction_depth_U b) ∨
      (b = .snce x y ∧ junction_depth_U (.snce x y) ≥ junction_depth_U a) ∨
      (snce_achieves_max_jdU a x y ∧ junction_depth_U a ≥ junction_depth_U b) ∨
      (snce_achieves_max_jdU b x y ∧ junction_depth_U b ≥ junction_depth_U a)
  | _, _, _ => False

/-- Predicate: S(A,B) appears in the U-argument of a `.untl` node. -/
def snce_inside_U_arg : Formula Atom → Formula Atom → Formula Atom → Prop
  | .untl a b, x, y =>
      a = .snce x y ∨ b = .snce x y ∨
      snce_inside_U_arg a x y ∨ snce_inside_U_arg b x y
  | _, _, _ => False

/-- Key lemma: abstracting S(A,B) from the LEFT U-argument when jdU a STRICTLY exceeds
    jdU b strictly decreases junction_depth_U of `.untl a b`. -/
theorem abstract_snce_untl_jdU_lt_left (a b x y : Formula Atom) (p : Atom)
    (h_a_dec : junction_depth_U (abstract_snce a x y p) < junction_depth_U a)
    (h_max : junction_depth_U a > junction_depth_U b) :
    junction_depth_U (abstract_snce (.untl a b) x y p) < junction_depth_U (.untl a b) := by
  simp only [abstract_snce, junction_depth_U]
  have hle_b := abstract_snce_jdU_le b x y p
  apply Nat.max_lt.mpr; constructor
  · exact Nat.lt_of_lt_of_le h_a_dec (Nat.le_max_left _ _)
  · exact Nat.lt_of_le_of_lt hle_b (Nat.lt_of_lt_of_le h_max (Nat.le_max_left _ _))

/-- Key lemma: abstracting S(A,B) from the RIGHT U-argument. -/
theorem abstract_snce_untl_jdU_lt_right (a b x y : Formula Atom) (p : Atom)
    (h_b_dec : junction_depth_U (abstract_snce b x y p) < junction_depth_U b)
    (h_max : junction_depth_U b > junction_depth_U a) :
    junction_depth_U (abstract_snce (.untl a b) x y p) < junction_depth_U (.untl a b) := by
  simp only [abstract_snce, junction_depth_U]
  have hle_a := abstract_snce_jdU_le a x y p
  apply Nat.max_lt.mpr; constructor
  · exact Nat.lt_of_le_of_lt hle_a (Nat.lt_of_lt_of_le h_max (Nat.le_max_right _ _))
  · exact Nat.lt_of_lt_of_le h_b_dec (Nat.le_max_right _ _)

/-- Version when jdU a = jdU b and BOTH branches decrease. -/
theorem abstract_snce_untl_jdU_lt_both (a b x y : Formula Atom) (p : Atom)
    (h_a_dec : junction_depth_U (abstract_snce a x y p) < junction_depth_U a)
    (h_b_dec : junction_depth_U (abstract_snce b x y p) < junction_depth_U b) :
    junction_depth_U (abstract_snce (.untl a b) x y p) < junction_depth_U (.untl a b) := by
  simp only [abstract_snce, junction_depth_U]
  apply Nat.max_lt.mpr; constructor
  · exact Nat.lt_of_lt_of_le h_a_dec (Nat.le_max_left _ _)
  · exact Nat.lt_of_lt_of_le h_b_dec (Nat.le_max_right _ _)

/-- Direct case: abstracting S(A,B) when it IS the left U-arg and strictly dominates. -/
theorem abstract_snce_untl_left_snce_jdU_lt (b x y : Formula Atom) (p : Atom)
    (h_max : junction_depth_U (.snce x y) > junction_depth_U b) :
    junction_depth_U (abstract_snce (.untl (.snce x y) b) x y p) <
    junction_depth_U (.untl (.snce x y) b) :=
  abstract_snce_untl_jdU_lt_left _ _ _ _ _ (jdU_abstract_snce_snce_lt x y p) h_max

/-- Direct case: abstracting S(A,B) when it IS the right U-arg and strictly dominates. -/
theorem abstract_snce_untl_right_snce_jdU_lt (a x y : Formula Atom) (p : Atom)
    (h_max : junction_depth_U (.snce x y) > junction_depth_U a) :
    junction_depth_U (abstract_snce (.untl a (.snce x y)) x y p) <
    junction_depth_U (.untl a (.snce x y)) :=
  abstract_snce_untl_jdU_lt_right _ _ _ _ _ (jdU_abstract_snce_snce_lt x y p) h_max

/-- Direct case: abstracting S(A,B) from both sides when they are equal. -/
theorem abstract_snce_untl_both_snce_jdU_lt (x y : Formula Atom) (p : Atom) :
    junction_depth_U (abstract_snce (.untl (.snce x y) (.snce x y)) x y p) <
    junction_depth_U (.untl (.snce x y) (.snce x y)) :=
  abstract_snce_untl_jdU_lt_both _ _ _ _ _
    (jdU_abstract_snce_snce_lt x y p) (jdU_abstract_snce_snce_lt x y p)

/-- Key theorem: abstracting S(A,B) from the U-argument that achieves
    the maximum jdU decreases junction_depth of the whole `.untl` node. -/
theorem abstract_snce_inside_untl_jd_lt (a b x y : Formula Atom) (p : Atom)
    (h : (junction_depth_U (abstract_snce a x y p) < junction_depth_U a ∧
          junction_depth_U a > junction_depth_U b)
      ∨ (junction_depth_U (abstract_snce b x y p) < junction_depth_U b ∧
          junction_depth_U b > junction_depth_U a)
      ∨ (junction_depth_U (abstract_snce a x y p) < junction_depth_U a ∧
          junction_depth_U (abstract_snce b x y p) < junction_depth_U b)) :
    junction_depth (abstract_snce (.untl a b) x y p) < junction_depth (.untl a b) := by
  simp only [abstract_snce, junction_depth]
  rcases h with ⟨hlt_a, hgt⟩ | ⟨hlt_b, hgt⟩ | ⟨hlt_a, hlt_b⟩
  · have := abstract_snce_untl_jdU_lt_left a b x y p hlt_a hgt
    simp only [abstract_snce, junction_depth_U] at this; exact this
  · have := abstract_snce_untl_jdU_lt_right a b x y p hlt_b hgt
    simp only [abstract_snce, junction_depth_U] at this; exact this
  · have := abstract_snce_untl_jdU_lt_both a b x y p hlt_a hlt_b
    simp only [abstract_snce, junction_depth_U] at this; exact this

/-! ### GHR94-Faithful Strengthening: Separation preserving single U-type -/

/-- Stronger separability: separated equivalent with preserved single U-type. -/
def is_separable_with_U_type (φ x y : Formula Atom) : Prop :=
  ∃ ψ : Formula Atom, is_syntactically_separated ψ = true ∧ int_equiv φ ψ ∧ has_single_U_type ψ x y

/-- is_separable_with_U_type implies is_separable. -/
theorem separable_with_type_imp_separable {φ x y : Formula Atom}
    (h : is_separable_with_U_type φ x y) : is_separable φ := by
  obtain ⟨ψ, hsep, hequiv, _⟩ := h
  exact ⟨ψ, hsep, hequiv⟩

/-- Equivalence transfer for is_separable_with_U_type. -/
theorem is_separable_with_U_type_of_equiv {φ χ x y : Formula Atom}
    (hequiv : int_equiv φ χ) (h : is_separable_with_U_type χ x y) :
    is_separable_with_U_type φ x y := by
  obtain ⟨ψ, hsep, hequiv2, hsingle⟩ := h
  exact ⟨ψ, hsep, int_equiv_trans hequiv hequiv2, hsingle⟩

/-- imp preserves is_separable_with_U_type. -/
theorem imp_separable_with_type {a b x y : Formula Atom}
    (ha : is_separable_with_U_type a x y) (hb : is_separable_with_U_type b x y) :
    is_separable_with_U_type (.imp a b) x y := by
  obtain ⟨ψa, hsepa, hequiva, hsinglea⟩ := ha
  obtain ⟨ψb, hsepb, hequivb, hsingleb⟩ := hb
  exact ⟨.imp ψa ψb, by simp [is_syntactically_separated, hsepa, hsepb],
         fun m t => ⟨fun h hp => (hequivb m t).mp (h ((hequiva m t).mpr hp)),
                     fun h hp => (hequivb m t).mpr (h ((hequiva m t).mp hp))⟩,
         ⟨hsinglea, hsingleb⟩⟩

/-- U-free formulas are separable_with_U_type (vacuously). -/
theorem u_free_separable_with_type {φ x y : Formula Atom} (h : is_U_free φ = true) :
    is_separable_with_U_type φ x y := by
  have hsep := separated_imp_separable φ (restricted_u_free_separated φ (has_no_allpast_allfuture_true φ) h)
  obtain ⟨ψ, hsep_ψ, hequiv⟩ := hsep
  exact ⟨φ, by {
    exact restricted_u_free_separated φ (has_no_allpast_allfuture_true φ) h
  }, int_equiv_refl φ, u_free_has_single_U_type h⟩

/-- .untl A B with S-free args is separable_with_U_type. -/
theorem untl_s_free_separable_with_type {x y : Formula Atom}
    (hx_sf : is_S_free x = true) (hy_sf : is_S_free y = true) :
    is_separable_with_U_type (.untl x y) x y := by
  exact ⟨.untl x y, by simp [is_syntactically_separated, hx_sf, hy_sf],
         int_equiv_refl _, has_single_U_type_untl x y⟩

/-! ### Combinators for is_separable_with_U_type -/

/-- or preserves is_separable_with_U_type. -/
theorem or_separable_with_U_type {a b x y : Formula Atom}
    (ha : is_separable_with_U_type a x y) (hb : is_separable_with_U_type b x y) :
    is_separable_with_U_type (Formula.or a b) x y := by
  obtain ⟨ψa, hsepa, hequiva, hsinglea⟩ := ha
  obtain ⟨ψb, hsepb, hequivb, hsingleb⟩ := hb
  refine ⟨Formula.or ψa ψb, ?_, ?_, ?_⟩
  · simp [Formula.or, Formula.neg, is_syntactically_separated, hsepa, hsepb]
  · intro m t; constructor
    · intro h; rcases int_truth_or_iff.mp h with hp | hq
      · exact int_truth_or_iff.mpr (Or.inl ((hequiva m t).mp hp))
      · exact int_truth_or_iff.mpr (Or.inr ((hequivb m t).mp hq))
    · intro h; rcases int_truth_or_iff.mp h with hp | hq
      · exact int_truth_or_iff.mpr (Or.inl ((hequiva m t).mpr hp))
      · exact int_truth_or_iff.mpr (Or.inr ((hequivb m t).mpr hq))
  · exact has_single_U_type_or hsinglea hsingleb

/-- and preserves is_separable_with_U_type. -/
theorem and_separable_with_U_type {a b x y : Formula Atom}
    (ha : is_separable_with_U_type a x y) (hb : is_separable_with_U_type b x y) :
    is_separable_with_U_type (Formula.and a b) x y := by
  obtain ⟨ψa, hsepa, hequiva, hsinglea⟩ := ha
  obtain ⟨ψb, hsepb, hequivb, hsingleb⟩ := hb
  refine ⟨Formula.and ψa ψb, and_separated hsepa hsepb, ?_, has_single_U_type_and hsinglea hsingleb⟩
  intro m t; constructor
  · intro h; rw [int_truth_and_iff] at h ⊢
    exact ⟨(hequiva m t).mp h.1, (hequivb m t).mp h.2⟩
  · intro h; rw [int_truth_and_iff] at h ⊢
    exact ⟨(hequiva m t).mpr h.1, (hequivb m t).mpr h.2⟩

/-- neg preserves is_separable_with_U_type. -/
theorem neg_separable_with_U_type {a x y : Formula Atom}
    (ha : is_separable_with_U_type a x y) :
    is_separable_with_U_type (Formula.neg a) x y := by
  obtain ⟨ψa, hsepa, hequiva, hsinglea⟩ := ha
  refine ⟨Formula.neg ψa, neg_separated hsepa, ?_, has_single_U_type_neg hsinglea⟩
  intro m t; constructor
  · intro hn hp; exact hn ((hequiva m t).mpr hp)
  · intro hn hp; exact hn ((hequiva m t).mp hp)

/-! ### U-Type Argument Replacement Bridge -/

/-- Replace U-type arguments in a formula: every `.untl _ _` node gets new arguments. -/
def replace_untl_args (ψ x_new y_new : Formula Atom) : Formula Atom :=
  match ψ with
  | .atom a => .atom a
  | .bot => .bot
  | .imp p q => .imp (replace_untl_args p x_new y_new) (replace_untl_args q x_new y_new)
  | .box p => .box (replace_untl_args p x_new y_new)
  | .untl _ _ => .untl x_new y_new
  | .snce p q => .snce (replace_untl_args p x_new y_new) (replace_untl_args q x_new y_new)

/-- `replace_untl_args` produces `has_single_U_type _ A_new B_new`. -/
theorem replace_untl_args_has_single_U_type (ψ x_new y_new : Formula Atom) :
    has_single_U_type (replace_untl_args ψ x_new y_new) x_new y_new := by
  induction ψ with
  | atom _ => exact trivial
  | bot => exact trivial
  | imp _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | box _ ih => exact ih
  | untl _ _ => exact ⟨rfl, rfl⟩
  | snce _ _ ih1 ih2 => exact ⟨ih1, ih2⟩

/-- For U-free formulas, `replace_untl_args` is the identity. -/
theorem replace_untl_args_u_free_eq (ψ x_new y_new : Formula Atom)
    (h : is_U_free ψ = true) : replace_untl_args ψ x_new y_new = ψ := by
  induction ψ with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ih1 ih2 =>
    simp [is_U_free] at h
    simp [replace_untl_args, ih1 h.1, ih2 h.2]
  | box _ ih =>
    simp [is_U_free] at h
    simp [replace_untl_args, ih h]
  | untl _ _ => simp [is_U_free] at h
  | snce _ _ ih1 ih2 =>
    simp [is_U_free] at h
    simp [replace_untl_args, ih1 h.1, ih2 h.2]

/-- `replace_untl_args` preserves `is_S_free` when the new arguments are S-free. -/
private theorem replace_untl_args_preserves_S_free (ψ x_new y_new : Formula Atom)
    (h : is_S_free ψ = true) (hx : is_S_free x_new = true) (hy : is_S_free y_new = true) :
    is_S_free (replace_untl_args ψ x_new y_new) = true := by
  induction ψ with
  | atom _ => simp [replace_untl_args, is_S_free]
  | bot => rfl
  | imp _ _ ih1 ih2 =>
    simp [is_S_free] at h; simp [replace_untl_args, is_S_free, ih1 h.1, ih2 h.2]
  | box _ ih =>
    simp [is_S_free] at h; simp [replace_untl_args, is_S_free, ih h]
  | untl _ _ =>
    simp [replace_untl_args, is_S_free, hx, hy]
  | snce _ _ => simp [is_S_free] at h

/-- `replace_untl_args` preserves `is_syntactically_separated`. -/
theorem replace_untl_args_preserves_separated (ψ x_new y_new : Formula Atom)
    (h_sep : is_syntactically_separated ψ = true)
    (hx_sf : is_S_free x_new = true) (hy_sf : is_S_free y_new = true) :
    is_syntactically_separated (replace_untl_args ψ x_new y_new) = true := by
  induction ψ with
  | atom _ => simp [replace_untl_args, is_syntactically_separated]
  | bot => rfl
  | imp _ _ ih1 ih2 =>
    simp [is_syntactically_separated] at h_sep
    simp [replace_untl_args, is_syntactically_separated, ih1 h_sep.1, ih2 h_sep.2]
  | box _ => simp [replace_untl_args, is_syntactically_separated]
  | untl _ _ =>
    simp [replace_untl_args, is_syntactically_separated, hx_sf, hy_sf]
  | snce p q ih1 ih2 =>
    simp [is_syntactically_separated] at h_sep
    simp only [replace_untl_args, is_syntactically_separated]
    rw [replace_untl_args_u_free_eq p x_new y_new h_sep.1,
        replace_untl_args_u_free_eq q x_new y_new h_sep.2]
    simp [h_sep.1, h_sep.2]

/-- `replace_untl_args` preserves `int_equiv` when `has_single_U_type ψ A_old B_old`
    and `int_equiv A_old A_new` and `int_equiv B_old B_new`. -/
theorem replace_untl_args_equiv (ψ x_old y_old x_new y_new : Formula Atom)
    (h_single : has_single_U_type ψ x_old y_old)
    (hx_equiv : int_equiv x_old x_new) (hy_equiv : int_equiv y_old y_new) :
    int_equiv ψ (replace_untl_args ψ x_new y_new) := by
  induction ψ with
  | atom _ => intro m t; rfl
  | bot => intro m t; rfl
  | imp p q ih1 ih2 =>
    obtain ⟨h1, h2⟩ := h_single
    intro m t; simp only [replace_untl_args, int_truth]
    exact Iff.imp (ih1 h1 m t) (ih2 h2 m t)
  | box _ ih =>
    intro m t; simp only [replace_untl_args, int_truth]
  | untl p q =>
    obtain ⟨hp, hq⟩ := h_single
    subst hp; subst hq
    intro m t; simp only [replace_untl_args, int_truth]
    constructor
    · rintro ⟨s, hts, h1, h2⟩
      exact ⟨s, hts, (hx_equiv m s).mp h1,
        fun r hr1 hr2 => (hy_equiv m r).mp (h2 r hr1 hr2)⟩
    · rintro ⟨s, hts, h1, h2⟩
      exact ⟨s, hts, (hx_equiv m s).mpr h1,
        fun r hr1 hr2 => (hy_equiv m r).mpr (h2 r hr1 hr2)⟩
  | snce p q ih1 ih2 =>
    obtain ⟨h1, h2⟩ := h_single
    intro m t; simp only [replace_untl_args, int_truth]
    constructor
    · rintro ⟨s, hst, h1', h2'⟩
      exact ⟨s, hst, (ih1 h1 m s).mp h1',
        fun r hr1 hr2 => (ih2 h2 m r).mp (h2' r hr1 hr2)⟩
    · rintro ⟨s, hst, h1', h2'⟩
      exact ⟨s, hst, (ih1 h1 m s).mpr h1',
        fun r hr1 hr2 => (ih2 h2 m r).mpr (h2' r hr1 hr2)⟩

/-- Bridge lemma: convert `is_separable_with_U_type φ A' B'` to
    `is_separable_with_U_type φ A B`. -/
theorem is_separable_with_U_type_replace_args {φ x x' y y' : Formula Atom}
    (h : is_separable_with_U_type φ x' y')
    (hx_equiv : int_equiv x x') (hy_equiv : int_equiv y y')
    (hx_sf : is_S_free x = true) (hy_sf : is_S_free y = true) :
    is_separable_with_U_type φ x y := by
  obtain ⟨ψ, h_sep, h_equiv, h_single⟩ := h
  exact ⟨replace_untl_args ψ x y,
    replace_untl_args_preserves_separated ψ x y h_sep hx_sf hy_sf,
    int_equiv_trans h_equiv (replace_untl_args_equiv ψ x' y' x y h_single
      (int_equiv_symm hx_equiv) (int_equiv_symm hy_equiv)),
    replace_untl_args_has_single_U_type ψ x y⟩

end DecEq

end Cslib.Logic.Bimodal.Metalogic.Separation
