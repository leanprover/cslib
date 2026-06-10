/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Defs

set_option linter.style.emptyLine false

/-!
# Temporal Duality for Integer Semantics

Establishes the `swapTemporal` duality principle for integer semantics,
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

@[expose] public section

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

/-- The core duality theorem: truth of swapTemporal phi in M
    at t is equivalent to truth of phi in M.reverse at -t. -/
theorem swapTemporal_int_truth
    (M : IntStructure Atom) (t : Int)
    (phi : Formula Atom) :
    intTruth M t phi.swapTemporal ↔
      intTruth M.reverse (-t) phi := by
  induction phi generalizing t with
  | atom a =>
    simp [Formula.swapTemporal, intTruth,
      IntStructure.reverse, Set.mem_setOf_eq, neg_neg]
  | bot => simp [Formula.swapTemporal, intTruth]
  | imp phi psi ih1 ih2 =>
    simp only [Formula.swapTemporal, intTruth]
    rw [ih1, ih2]
  | box phi _ih =>
    simp [Formula.swapTemporal, intTruth]
  | untl phi psi ih1 ih2 =>
    simp only [Formula.swapTemporal, intTruth]
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
    simp only [Formula.swapTemporal, intTruth]
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
    (h : intEquiv phi psi) :
    intEquiv phi.swapTemporal psi.swapTemporal := by
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
    isUFree phi.swapTemporal = isSFree phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swapTemporal, isUFree,
      isSFree, ih1, ih2]
  | box a ih =>
    simp [Formula.swapTemporal, isUFree,
      isSFree, ih]
  | untl a b ih1 ih2 =>
    simp [Formula.swapTemporal, isUFree,
      isSFree, ih1, ih2]
  | snce a b _ih1 _ih2 =>
    simp [Formula.swapTemporal, isUFree, isSFree]

/-- S-free after swap is the same as U-free before swap. -/
theorem dual_S_free_iff_U_free (phi : Formula Atom) :
    isSFree phi.swapTemporal = isUFree phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swapTemporal, isUFree,
      isSFree, ih1, ih2]
  | box a ih =>
    simp [Formula.swapTemporal, isUFree,
      isSFree, ih]
  | untl a b _ih1 _ih2 =>
    simp [Formula.swapTemporal, isUFree, isSFree]
  | snce a b ih1 ih2 =>
    simp [Formula.swapTemporal, isUFree,
      isSFree, ih1, ih2]

/-- Syntactic separation is preserved by swapTemporal. -/
theorem dual_separated (phi : Formula Atom) :
    isSyntacticallySeparated phi.swapTemporal =
      isSyntacticallySeparated phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swapTemporal,
      isSyntacticallySeparated, ih1, ih2]
  | box _a =>
    simp [Formula.swapTemporal,
      isSyntacticallySeparated]
  | untl a b _ih1 _ih2 =>
    simp [Formula.swapTemporal,
      isSyntacticallySeparated]
    rw [dual_U_free_iff_S_free a,
      dual_U_free_iff_S_free b]
  | snce a b _ih1 _ih2 =>
    simp [Formula.swapTemporal,
      isSyntacticallySeparated]
    rw [dual_S_free_iff_U_free a,
      dual_S_free_iff_U_free b]

/-- If phi is separable, then swap(phi) is also separable. -/
theorem dual_separable (phi : Formula Atom)
    (h : isSeparable phi) :
    isSeparable phi.swapTemporal := by
  obtain ⟨psi, hsep, hequiv⟩ := h
  refine ⟨psi.swapTemporal, ?_,
    dual_equiv phi psi hequiv⟩
  rw [dual_separated]; exact hsep

/-! ## Duality for Proper Purity Predicates -/

/-- future_only after swap = past_only before swap. -/
theorem dual_future_only_iff_past_only
    (phi : Formula Atom) :
    isFutureOnly phi.swapTemporal =
      isPastOnly phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swapTemporal, isFutureOnly,
      isPastOnly, ih1, ih2]
  | box a ih =>
    simp [Formula.swapTemporal, isFutureOnly,
      isPastOnly, ih]
  | untl a b _ih1 _ih2 =>
    simp [Formula.swapTemporal, isFutureOnly,
      isPastOnly]
  | snce a b ih1 ih2 =>
    simp [Formula.swapTemporal, isFutureOnly,
      isPastOnly, ih1, ih2]

/-- past_only after swap = future_only before swap. -/
theorem dual_past_only_iff_future_only
    (phi : Formula Atom) :
    isPastOnly phi.swapTemporal =
      isFutureOnly phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swapTemporal, isFutureOnly,
      isPastOnly, ih1, ih2]
  | box a ih =>
    simp [Formula.swapTemporal, isFutureOnly,
      isPastOnly, ih]
  | untl a b ih1 ih2 =>
    simp [Formula.swapTemporal, isFutureOnly,
      isPastOnly, ih1, ih2]
  | snce a b _ih1 _ih2 =>
    simp [Formula.swapTemporal, isFutureOnly,
      isPastOnly]

/-- Proper separation is preserved by swapTemporal. -/
theorem dual_properly_separated (phi : Formula Atom) :
    isProperlySeparated phi.swapTemporal =
      isProperlySeparated phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [Formula.swapTemporal,
      isProperlySeparated, ih1, ih2]
  | box _a =>
    simp [Formula.swapTemporal,
      isProperlySeparated]
  | untl a b _ih1 _ih2 =>
    simp [Formula.swapTemporal,
      isProperlySeparated]
    rw [dual_past_only_iff_future_only a,
      dual_past_only_iff_future_only b]
  | snce a b _ih1 _ih2 =>
    simp [Formula.swapTemporal,
      isProperlySeparated]
    rw [dual_future_only_iff_past_only a,
      dual_future_only_iff_past_only b]

/-- If phi is properly separable, swap(phi) is too. -/
theorem dual_properly_separable
    (phi : Formula Atom)
    (h : isProperlySeparable phi) :
    isProperlySeparable phi.swapTemporal := by
  obtain ⟨psi, hsep, hequiv⟩ := h
  refine ⟨psi.swapTemporal, ?_,
    dual_equiv phi psi hequiv⟩
  rw [dual_properly_separated]; exact hsep

/-! ## Relationship Between Proper and Weak Predicates -/

/-- future_only implies S-free. -/
theorem future_only_imp_S_free
    {φ : Formula Atom}
    (h : isFutureOnly φ = true) :
    isSFree φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [isFutureOnly] at h
    simp [isSFree, ih1 h.1, ih2 h.2]
  | box a ih =>
    simp [isFutureOnly] at h
    simp [isSFree, ih h]
  | untl a b ih1 ih2 =>
    simp [isFutureOnly] at h
    simp [isSFree, ih1 h.1, ih2 h.2]
  | snce _ _ => simp [isFutureOnly] at h

/-- past_only implies U-free. -/
theorem past_only_imp_U_free
    {φ : Formula Atom}
    (h : isPastOnly φ = true) :
    isUFree φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [isPastOnly] at h
    simp [isUFree, ih1 h.1, ih2 h.2]
  | box a ih =>
    simp [isPastOnly] at h
    simp [isUFree, ih h]
  | untl _ _ => simp [isPastOnly] at h
  | snce a b ih1 ih2 =>
    simp [isPastOnly] at h
    simp [isUFree, ih1 h.1, ih2 h.2]

/-- Proper separation implies syntactic separation. -/
theorem properly_separated_imp_syntactically_separated
    {φ : Formula Atom}
    (h : isProperlySeparated φ = true) :
    isSyntacticallySeparated φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [isProperlySeparated] at h
    simp [isSyntacticallySeparated,
      ih1 h.1, ih2 h.2]
  | box _ => rfl
  | untl a b _ih1 _ih2 =>
    simp [isProperlySeparated] at h
    simp [isSyntacticallySeparated,
      future_only_imp_S_free h.1,
      future_only_imp_S_free h.2]
  | snce a b _ih1 _ih2 =>
    simp [isProperlySeparated] at h
    simp [isSyntacticallySeparated,
      past_only_imp_U_free h.1,
      past_only_imp_U_free h.2]

/-- Proper separability implies separability. -/
theorem properly_separable_imp_separable
    {φ : Formula Atom}
    (h : isProperlySeparable φ) :
    isSeparable φ := by
  obtain ⟨ψ, hψ, hequiv⟩ := h
  exact ⟨ψ,
    properly_separated_imp_syntactically_separated hψ,
    hequiv⟩

/-! ## Boolean Closure for Purity Predicates -/

theorem neg_future_only {φ : Formula Atom}
    (h : isFutureOnly φ = true) :
    isFutureOnly (Formula.neg φ) = true := by
  simp [Formula.neg, isFutureOnly, h]

theorem neg_past_only {φ : Formula Atom}
    (h : isPastOnly φ = true) :
    isPastOnly (Formula.neg φ) = true := by
  simp [Formula.neg, isPastOnly, h]

theorem and_future_only {φ ψ : Formula Atom}
    (h1 : isFutureOnly φ = true)
    (h2 : isFutureOnly ψ = true) :
    isFutureOnly (Formula.and φ ψ) = true := by
  simp [Formula.and, Formula.neg, isFutureOnly,
    h1, h2]

theorem and_past_only {φ ψ : Formula Atom}
    (h1 : isPastOnly φ = true)
    (h2 : isPastOnly ψ = true) :
    isPastOnly (Formula.and φ ψ) = true := by
  simp [Formula.and, Formula.neg, isPastOnly,
    h1, h2]

theorem or_future_only {φ ψ : Formula Atom}
    (h1 : isFutureOnly φ = true)
    (h2 : isFutureOnly ψ = true) :
    isFutureOnly (Formula.or φ ψ) = true := by
  simp [Formula.or, Formula.neg, isFutureOnly,
    h1, h2]

theorem or_past_only {φ ψ : Formula Atom}
    (h1 : isPastOnly φ = true)
    (h2 : isPastOnly ψ = true) :
    isPastOnly (Formula.or φ ψ) = true := by
  simp [Formula.or, Formula.neg, isPastOnly,
    h1, h2]

theorem imp_future_only {φ ψ : Formula Atom}
    (h1 : isFutureOnly φ = true)
    (h2 : isFutureOnly ψ = true) :
    isFutureOnly (Formula.imp φ ψ) = true := by
  simp [isFutureOnly, h1, h2]

theorem imp_past_only {φ ψ : Formula Atom}
    (h1 : isPastOnly φ = true)
    (h2 : isPastOnly ψ = true) :
    isPastOnly (Formula.imp φ ψ) = true := by
  simp [isPastOnly, h1, h2]

theorem atom_future_only (a : Atom) :
    isFutureOnly (.atom a : Formula Atom) = true :=
  rfl

theorem atom_past_only (a : Atom) :
    isPastOnly (.atom a : Formula Atom) = true :=
  rfl

theorem bot_future_only :
    isFutureOnly (.bot : Formula Atom) = true :=
  rfl

theorem bot_past_only :
    isPastOnly (.bot : Formula Atom) = true :=
  rfl

end Cslib.Logic.Bimodal.Metalogic.Separation
