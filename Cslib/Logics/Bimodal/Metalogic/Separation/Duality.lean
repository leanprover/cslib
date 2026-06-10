/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Separation.Defs

set_option linter.style.emptyLine false

/-!
# Temporal Duality for Integer Semantics

Establishes the `swap_temporal` duality principle for integer semantics,
enabling automatic derivation of "S out of U" cases from "U out of S"
cases.

## Key Results

- `IntStructure.reverse`: Flip time direction
- `swapTemporal_int_truth`: Truth preserved under reversal + swap
- `dual_equiv`: If phi equiv psi then swap(phi) equiv swap(psi)
- `dual_U_free_iff_S_free`: U-free after swap iff S-free before
- `dual_separated`: Separation is preserved by swap

## References

- GHR94 Chapter 10.2: duality halves the proof burden
-/

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Time Reversal -/

/-- Reverse an integer structure: flip the time direction. -/
def IntStructure.reverse
    (M : IntStructure Atom) : IntStructure Atom where
  val a := {t | -t ∈ M.val a}

/-- Reversing twice gives back the original structure. -/
theorem IntStructure.reverse_reverse
    (M : IntStructure Atom) :
    M.reverse.reverse = M := by
  cases M with | mk val =>
  simp only [IntStructure.reverse]
  congr 1; funext a; ext t
  simp [Set.mem_setOf_eq, neg_neg]

/-! ## Duality Theorem -/

/-- The core duality theorem: truth of swap_temporal phi in M
    at t is equivalent to truth of phi in M.reverse at -t. -/
theorem swapTemporal_int_truth
    (M : IntStructure Atom) (t : Int)
    (phi : Formula Atom) :
    int_truth M t phi.swap_temporal ↔
      int_truth M.reverse (-t) phi := by
  induction phi generalizing t with
  | atom a =>
    simp [Formula.swap_temporal, int_truth,
      IntStructure.reverse, Set.mem_setOf_eq, neg_neg]
  | bot => simp [Formula.swap_temporal, int_truth]
  | imp phi psi ih1 ih2 =>
    simp only [Formula.swap_temporal, int_truth]
    rw [ih1, ih2]
  | box phi _ih =>
    simp [Formula.swap_temporal, int_truth]
  | untl phi psi ih1 ih2 =>
    simp only [Formula.swap_temporal, int_truth]
    constructor
    · rintro ⟨s, hst, h1, h2⟩
      refine ⟨-s, by omega, ?_, ?_⟩
      · rw [ih1] at h1; simpa [neg_neg] using h1
      · intro r hr1 hr2
        have := h2 (-r) (by omega) (by omega)
        rw [ih2] at this
        simpa [neg_neg] using this
    · rintro ⟨s, hts, h1, h2⟩
      refine ⟨-s, by omega, ?_, ?_⟩
      · rw [ih1]; simpa [neg_neg] using h1
      · intro r hr1 hr2
        rw [ih2]
        have := h2 (-r) (by omega) (by omega)
        simpa [neg_neg] using this
  | snce phi psi ih1 ih2 =>
    simp only [Formula.swap_temporal, int_truth]
    constructor
    · rintro ⟨s, hts, h1, h2⟩
      refine ⟨-s, by omega, ?_, ?_⟩
      · rw [ih1] at h1; simpa [neg_neg] using h1
      · intro r hr1 hr2
        have := h2 (-r) (by omega) (by omega)
        rw [ih2] at this
        simpa [neg_neg] using this
    · rintro ⟨s, hst, h1, h2⟩
      refine ⟨-s, by omega, ?_, ?_⟩
      · rw [ih1]; simpa [neg_neg] using h1
      · intro r hr1 hr2
        rw [ih2]
        have := h2 (-r) (by omega) (by omega)
        simpa [neg_neg] using this

/-! ## Derived Duality Results -/

/-- If phi equiv psi over Z, then swap(phi) equiv swap(psi). -/
theorem dual_equiv (phi psi : Formula Atom)
    (h : int_equiv phi psi) :
    int_equiv phi.swap_temporal psi.swap_temporal := by
  intro M t
  constructor
  · intro h1
    exact (swapTemporal_int_truth M t psi).mpr
      ((h M.reverse (-t)).mp
        ((swapTemporal_int_truth M t phi).mp h1))
  · intro h2
    exact (swapTemporal_int_truth M t phi).mpr
      ((h M.reverse (-t)).mpr
        ((swapTemporal_int_truth M t psi).mp h2))

/-- U-free after swap is the same as S-free before swap. -/
theorem dual_U_free_iff_S_free (phi : Formula Atom) :
    is_U_free phi.swap_temporal = is_S_free phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swap_temporal, is_U_free,
      is_S_free, ih1, ih2]
  | box a ih =>
    simp [Formula.swap_temporal, is_U_free,
      is_S_free, ih]
  | untl a b ih1 ih2 =>
    simp [Formula.swap_temporal, is_U_free,
      is_S_free, ih1, ih2]
  | snce a b _ih1 _ih2 =>
    simp [Formula.swap_temporal, is_U_free, is_S_free]

/-- S-free after swap is the same as U-free before swap. -/
theorem dual_S_free_iff_U_free (phi : Formula Atom) :
    is_S_free phi.swap_temporal = is_U_free phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swap_temporal, is_U_free,
      is_S_free, ih1, ih2]
  | box a ih =>
    simp [Formula.swap_temporal, is_U_free,
      is_S_free, ih]
  | untl a b _ih1 _ih2 =>
    simp [Formula.swap_temporal, is_U_free, is_S_free]
  | snce a b ih1 ih2 =>
    simp [Formula.swap_temporal, is_U_free,
      is_S_free, ih1, ih2]

/-- Syntactic separation is preserved by swap_temporal. -/
theorem dual_separated (phi : Formula Atom) :
    is_syntactically_separated phi.swap_temporal =
      is_syntactically_separated phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swap_temporal,
      is_syntactically_separated, ih1, ih2]
  | box _a =>
    simp [Formula.swap_temporal,
      is_syntactically_separated]
  | untl a b _ih1 _ih2 =>
    simp [Formula.swap_temporal,
      is_syntactically_separated]
    rw [dual_U_free_iff_S_free a,
      dual_U_free_iff_S_free b]
  | snce a b _ih1 _ih2 =>
    simp [Formula.swap_temporal,
      is_syntactically_separated]
    rw [dual_S_free_iff_U_free a,
      dual_S_free_iff_U_free b]

/-- If phi is separable, then swap(phi) is also separable. -/
theorem dual_separable (phi : Formula Atom)
    (h : is_separable phi) :
    is_separable phi.swap_temporal := by
  obtain ⟨psi, hsep, hequiv⟩ := h
  refine ⟨psi.swap_temporal, ?_,
    dual_equiv phi psi hequiv⟩
  rw [dual_separated]; exact hsep

/-! ## Duality for Proper Purity Predicates -/

/-- future_only after swap = past_only before swap. -/
theorem dual_future_only_iff_past_only
    (phi : Formula Atom) :
    is_future_only phi.swap_temporal =
      is_past_only phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swap_temporal, is_future_only,
      is_past_only, ih1, ih2]
  | box a ih =>
    simp [Formula.swap_temporal, is_future_only,
      is_past_only, ih]
  | untl a b _ih1 _ih2 =>
    simp [Formula.swap_temporal, is_future_only,
      is_past_only]
  | snce a b ih1 ih2 =>
    simp [Formula.swap_temporal, is_future_only,
      is_past_only, ih1, ih2]

/-- past_only after swap = future_only before swap. -/
theorem dual_past_only_iff_future_only
    (phi : Formula Atom) :
    is_past_only phi.swap_temporal =
      is_future_only phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swap_temporal, is_future_only,
      is_past_only, ih1, ih2]
  | box a ih =>
    simp [Formula.swap_temporal, is_future_only,
      is_past_only, ih]
  | untl a b ih1 ih2 =>
    simp [Formula.swap_temporal, is_future_only,
      is_past_only, ih1, ih2]
  | snce a b _ih1 _ih2 =>
    simp [Formula.swap_temporal, is_future_only,
      is_past_only]

/-- Proper separation is preserved by swap_temporal. -/
theorem dual_properly_separated (phi : Formula Atom) :
    is_properly_separated phi.swap_temporal =
      is_properly_separated phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swap_temporal,
      is_properly_separated, ih1, ih2]
  | box _a =>
    simp [Formula.swap_temporal,
      is_properly_separated]
  | untl a b _ih1 _ih2 =>
    simp [Formula.swap_temporal,
      is_properly_separated]
    rw [dual_past_only_iff_future_only a,
      dual_past_only_iff_future_only b]
  | snce a b _ih1 _ih2 =>
    simp [Formula.swap_temporal,
      is_properly_separated]
    rw [dual_future_only_iff_past_only a,
      dual_future_only_iff_past_only b]

/-- If phi is properly separable, swap(phi) is too. -/
theorem dual_properly_separable
    (phi : Formula Atom)
    (h : is_properly_separable phi) :
    is_properly_separable phi.swap_temporal := by
  obtain ⟨psi, hsep, hequiv⟩ := h
  refine ⟨psi.swap_temporal, ?_,
    dual_equiv phi psi hequiv⟩
  rw [dual_properly_separated]; exact hsep

/-! ## Relationship Between Proper and Weak Predicates -/

/-- future_only implies S-free. -/
theorem future_only_imp_S_free
    {φ : Formula Atom}
    (h : is_future_only φ = true) :
    is_S_free φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_future_only] at h
    simp [is_S_free, ih1 h.1, ih2 h.2]
  | box a ih =>
    simp [is_future_only] at h
    simp [is_S_free, ih h]
  | untl a b ih1 ih2 =>
    simp [is_future_only] at h
    simp [is_S_free, ih1 h.1, ih2 h.2]
  | snce _ _ => simp [is_future_only] at h

/-- past_only implies U-free. -/
theorem past_only_imp_U_free
    {φ : Formula Atom}
    (h : is_past_only φ = true) :
    is_U_free φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_past_only] at h
    simp [is_U_free, ih1 h.1, ih2 h.2]
  | box a ih =>
    simp [is_past_only] at h
    simp [is_U_free, ih h]
  | untl _ _ => simp [is_past_only] at h
  | snce a b ih1 ih2 =>
    simp [is_past_only] at h
    simp [is_U_free, ih1 h.1, ih2 h.2]

/-- Proper separation implies syntactic separation. -/
theorem properly_separated_imp_syntactically_separated
    {φ : Formula Atom}
    (h : is_properly_separated φ = true) :
    is_syntactically_separated φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_properly_separated] at h
    simp [is_syntactically_separated,
      ih1 h.1, ih2 h.2]
  | box _ => rfl
  | untl a b _ih1 _ih2 =>
    simp [is_properly_separated] at h
    simp [is_syntactically_separated,
      future_only_imp_S_free h.1,
      future_only_imp_S_free h.2]
  | snce a b _ih1 _ih2 =>
    simp [is_properly_separated] at h
    simp [is_syntactically_separated,
      past_only_imp_U_free h.1,
      past_only_imp_U_free h.2]

/-- Proper separability implies separability. -/
theorem properly_separable_imp_separable
    {φ : Formula Atom}
    (h : is_properly_separable φ) :
    is_separable φ := by
  obtain ⟨ψ, hψ, hequiv⟩ := h
  exact ⟨ψ,
    properly_separated_imp_syntactically_separated hψ,
    hequiv⟩

/-! ## Boolean Closure for Purity Predicates -/

theorem neg_future_only {φ : Formula Atom}
    (h : is_future_only φ = true) :
    is_future_only (Formula.neg φ) = true := by
  simp [Formula.neg, is_future_only, h]

theorem neg_past_only {φ : Formula Atom}
    (h : is_past_only φ = true) :
    is_past_only (Formula.neg φ) = true := by
  simp [Formula.neg, is_past_only, h]

theorem and_future_only {φ ψ : Formula Atom}
    (h1 : is_future_only φ = true)
    (h2 : is_future_only ψ = true) :
    is_future_only (Formula.and φ ψ) = true := by
  simp [Formula.and, Formula.neg, is_future_only,
    h1, h2]

theorem and_past_only {φ ψ : Formula Atom}
    (h1 : is_past_only φ = true)
    (h2 : is_past_only ψ = true) :
    is_past_only (Formula.and φ ψ) = true := by
  simp [Formula.and, Formula.neg, is_past_only,
    h1, h2]

theorem or_future_only {φ ψ : Formula Atom}
    (h1 : is_future_only φ = true)
    (h2 : is_future_only ψ = true) :
    is_future_only (Formula.or φ ψ) = true := by
  simp [Formula.or, Formula.neg, is_future_only,
    h1, h2]

theorem or_past_only {φ ψ : Formula Atom}
    (h1 : is_past_only φ = true)
    (h2 : is_past_only ψ = true) :
    is_past_only (Formula.or φ ψ) = true := by
  simp [Formula.or, Formula.neg, is_past_only,
    h1, h2]

theorem imp_future_only {φ ψ : Formula Atom}
    (h1 : is_future_only φ = true)
    (h2 : is_future_only ψ = true) :
    is_future_only (Formula.imp φ ψ) = true := by
  simp [is_future_only, h1, h2]

theorem imp_past_only {φ ψ : Formula Atom}
    (h1 : is_past_only φ = true)
    (h2 : is_past_only ψ = true) :
    is_past_only (Formula.imp φ ψ) = true := by
  simp [is_past_only, h1, h2]

theorem atom_future_only (a : Atom) :
    is_future_only (.atom a : Formula Atom) = true :=
  rfl

theorem atom_past_only (a : Atom) :
    is_past_only (.atom a : Formula Atom) = true :=
  rfl

theorem bot_future_only :
    is_future_only (.bot : Formula Atom) = true :=
  rfl

theorem bot_past_only :
    is_past_only (.bot : Formula Atom) = true :=
  rfl

end Cslib.Logic.Bimodal.Metalogic.Separation
