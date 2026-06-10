/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Syntax.Formula
public import Mathlib.Algebra.Order.Group.Int

set_option linter.style.emptyLine false

/-!
# Separation Definitions: Integer Temporal Semantics

Core definitions for the separation theorem over integer time (GHR94 Chapter 10.2).

## Key Definitions

- `IntStructure`: A temporal structure over integers (valuation on Z)
- `intTruth`: Recursive truth evaluation for formulas over Z
- `intEquiv`: Semantic equivalence over integer time
- `isPurePast`, `isPureFuture`, `isPurePresent`: Semantic purity predicates
- `isUFree`, `isSFree`: Syntactic absence predicates (decidable)
- `isSyntacticallySeparated`: Recursive syntactic separation check
- `isSeparable`: Existential separation predicate
- `junctionDepth`, `U_depth_under_S`, `countUSubformulas`: Structural measures

## References

- GHR94, Chapter 10, Section 10.2 (pp. 569-592)
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Integer Temporal Structure -/

/-- A temporal structure over integers: a valuation mapping atoms to sets of Z.
    This is GHR94's "linear temporal structure" (T, <, h) specialized to T = Z. -/
structure IntStructure (Atom : Type*) where
  val : Atom → Set ℤ

/-! ## Truth Evaluation -/

/-- Truth of a formula at time t in an integer temporal structure.
    Note: box is treated as True (degenerate: modal component irrelevant
    for separation).
    This matches GHR94's "linear temporal structure" setup. -/
def intTruth (M : IntStructure Atom) (t : ℤ) : Formula Atom → Prop
  | .atom a => t ∈ M.val a
  | .bot => False
  | .imp φ ψ => intTruth M t φ → intTruth M t ψ
  | .box _ => True
  | .untl φ ψ => ∃ s : ℤ, t < s ∧ intTruth M s φ ∧
      ∀ r : ℤ, t < r → r < s → intTruth M r ψ
  | .snce φ ψ => ∃ s : ℤ, s < t ∧ intTruth M s φ ∧
      ∀ r : ℤ, s < r → r < t → intTruth M r ψ

/-! ## intTruth simp lemmas for derived temporal operators -/

@[simp] theorem int_truth_allPast
    (M : IntStructure Atom) (t : ℤ) (φ : Formula Atom) :
    intTruth M t (Formula.allPast φ) ↔
      ∀ s : ℤ, s < t → intTruth M s φ := by
  simp only [intTruth]
  constructor
  · intro h s hs
    by_contra hns
    exact h ⟨s, hs, hns, fun _ _ _ h => h⟩
  · rintro h ⟨s, hs, hns, _⟩
    exact hns (h s hs)

@[simp] theorem int_truth_allFuture
    (M : IntStructure Atom) (t : ℤ) (φ : Formula Atom) :
    intTruth M t (Formula.allFuture φ) ↔
      ∀ s : ℤ, t < s → intTruth M s φ := by
  simp only [intTruth]
  constructor
  · intro h s hs
    by_contra hns
    exact h ⟨s, hs, hns, fun _ _ _ h => h⟩
  · rintro h ⟨s, hs, hns, _⟩
    exact hns (h s hs)

@[simp] theorem int_truth_somePast
    (M : IntStructure Atom) (t : ℤ) (φ : Formula Atom) :
    intTruth M t (Formula.somePast φ) ↔
      ∃ s : ℤ, s < t ∧ intTruth M s φ := by
  simp only [intTruth]
  constructor
  · rintro ⟨s, hs, hphi, _⟩
    exact ⟨s, hs, hphi⟩
  · rintro ⟨s, hs, hphi⟩
    exact ⟨s, hs, hphi, fun _ _ _ h => h⟩

@[simp] theorem int_truth_someFuture
    (M : IntStructure Atom) (t : ℤ) (φ : Formula Atom) :
    intTruth M t (Formula.someFuture φ) ↔
      ∃ s : ℤ, t < s ∧ intTruth M s φ := by
  simp only [intTruth]
  constructor
  · rintro ⟨s, hs, hphi, _⟩
    exact ⟨s, hs, hphi⟩
  · rintro ⟨s, hs, hphi⟩
    exact ⟨s, hs, hphi, fun _ _ _ h => h⟩

@[simp] theorem int_truth_neg
    (M : IntStructure Atom) (t : ℤ) (φ : Formula Atom) :
    intTruth M t (Formula.neg φ) ↔ ¬ intTruth M t φ := by
  simp only [intTruth]

@[simp] theorem int_truth_and
    (M : IntStructure Atom) (t : ℤ) (φ ψ : Formula Atom) :
    intTruth M t (Formula.and φ ψ) ↔
      intTruth M t φ ∧ intTruth M t ψ := by
  simp only [intTruth]; tauto

@[simp] theorem int_truth_or
    (M : IntStructure Atom) (t : ℤ) (φ ψ : Formula Atom) :
    intTruth M t (Formula.or φ ψ) ↔
      intTruth M t φ ∨ intTruth M t ψ := by
  simp only [intTruth]; tauto

@[simp] theorem int_truth_top (M : IntStructure Atom) (t : ℤ) :
    intTruth M t (Formula.top : Formula Atom) ↔ True := by
  simp only [intTruth]; tauto

/-! ## Formula Atoms -/

/-- Collect all atoms occurring in a formula (as a `Set Atom`). -/
def formulaAtoms : Formula Atom → Set Atom
  | .atom a => {a}
  | .bot => ∅
  | .imp φ ψ => formulaAtoms φ ∪ formulaAtoms ψ
  | .box φ => formulaAtoms φ
  | .untl φ ψ => formulaAtoms φ ∪ formulaAtoms ψ
  | .snce φ ψ => formulaAtoms φ ∪ formulaAtoms ψ

@[simp] theorem formula_atoms_allPast (φ : Formula Atom) :
    formulaAtoms (Formula.allPast φ) = formulaAtoms φ := by
  simp only [formulaAtoms]
  ext a; simp only [Set.mem_union, Set.mem_empty_iff_false, or_false]

@[simp] theorem formula_atoms_allFuture (φ : Formula Atom) :
    formulaAtoms (Formula.allFuture φ) = formulaAtoms φ := by
  simp only [formulaAtoms]
  ext a; simp only [Set.mem_union, Set.mem_empty_iff_false, or_false]

/-! ## Semantic Equivalence -/

/-- Semantic equivalence of formulas over integer time. -/
def intEquiv (φ ψ : Formula Atom) : Prop :=
  ∀ (M : IntStructure Atom) (t : ℤ), intTruth M t φ ↔ intTruth M t ψ

/-- intEquiv is reflexive. -/
theorem int_equiv_refl (φ : Formula Atom) : intEquiv φ φ :=
  fun _ _ => Iff.rfl

/-- intEquiv is symmetric. -/
theorem int_equiv_symm {φ ψ : Formula Atom}
    (h : intEquiv φ ψ) : intEquiv ψ φ :=
  fun M t => (h M t).symm

/-- intEquiv is transitive. -/
theorem int_equiv_trans {φ ψ χ : Formula Atom}
    (h1 : intEquiv φ ψ) (h2 : intEquiv ψ χ) :
    intEquiv φ χ :=
  fun M t => (h1 M t).trans (h2 M t)

/-! ## Semantic Purity Predicates -/

/-- A formula is "pure past" if its truth at t depends only on
    the past of t. -/
def isPurePast (φ : Formula Atom) : Prop :=
  ∀ (M₁ M₂ : IntStructure Atom) (t : ℤ),
    (∀ (a : Atom) (s : ℤ),
      s < t → (s ∈ M₁.val a ↔ s ∈ M₂.val a)) →
    (intTruth M₁ t φ ↔ intTruth M₂ t φ)

/-- A formula is "pure future" if its truth at t depends only on
    the future of t. -/
def isPureFuture (φ : Formula Atom) : Prop :=
  ∀ (M₁ M₂ : IntStructure Atom) (t : ℤ),
    (∀ (a : Atom) (s : ℤ),
      t < s → (s ∈ M₁.val a ↔ s ∈ M₂.val a)) →
    (intTruth M₁ t φ ↔ intTruth M₂ t φ)

/-- A formula is "pure present" if its truth at t depends only on
    time t. -/
def isPurePresent (φ : Formula Atom) : Prop :=
  ∀ (M₁ M₂ : IntStructure Atom) (t : ℤ),
    (∀ (a : Atom), (t ∈ M₁.val a ↔ t ∈ M₂.val a)) →
    (intTruth M₁ t φ ↔ intTruth M₂ t φ)

/-! ## Syntactic Predicates -/

/-- A formula is "syntactically U-free": no `untl` constructor. -/
def isUFree : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ => isUFree φ && isUFree ψ
  | .box φ => isUFree φ
  | .untl _ _ => false
  | .snce φ ψ => isUFree φ && isUFree ψ

/-- A formula is "syntactically S-free": no `snce` constructor. -/
def isSFree : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ => isSFree φ && isSFree ψ
  | .box φ => isSFree φ
  | .untl φ ψ => isSFree φ && isSFree ψ
  | .snce _ _ => false

/-! ### Simp lemmas for isUFree and isSFree -/

@[simp] theorem is_U_free_allPast (φ : Formula Atom) :
    isUFree (Formula.allPast φ) = isUFree φ := by
  simp only [isUFree, Bool.and_true]

@[simp] theorem is_U_free_allFuture (φ : Formula Atom) :
    isUFree (Formula.allFuture φ) = false := by
  simp only [isUFree, Bool.false_and]

@[simp] theorem is_S_free_allPast (φ : Formula Atom) :
    isSFree (Formula.allPast φ) = false := by
  simp only [isSFree, Bool.false_and]

@[simp] theorem is_S_free_allFuture (φ : Formula Atom) :
    isSFree (Formula.allFuture φ) = isSFree φ := by
  simp only [isSFree, Bool.and_true]

/-- A formula is "syntactically separated" if it is a boolean combination
    of atoms, U-formulas with S-free arguments, S-formulas with U-free
    arguments, and box formulas. -/
def isSyntacticallySeparated : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ =>
    isSyntacticallySeparated φ && isSyntacticallySeparated ψ
  | .box _ => true
  | .untl φ ψ => isSFree φ && isSFree ψ
  | .snce φ ψ => isUFree φ && isUFree ψ

@[simp] theorem is_syntactically_separated_allPast
    (φ : Formula Atom) :
    isSyntacticallySeparated (Formula.allPast φ) =
      isUFree φ := by
  simp only [isSyntacticallySeparated, isUFree, Bool.and_true]

@[simp] theorem is_syntactically_separated_allFuture
    (φ : Formula Atom) :
    isSyntacticallySeparated (Formula.allFuture φ) =
      isSFree φ := by
  simp only [isSyntacticallySeparated, isSFree, Bool.and_true]

/-- A formula is "separable" if it is integer-equivalent to a
    syntactically separated formula. -/
def isSeparable (φ : Formula Atom) : Prop :=
  ∃ ψ : Formula Atom,
    isSyntacticallySeparated ψ = true ∧ intEquiv φ ψ

/-! ## Proper Purity Predicates -/

/-- A formula is "future-only": no `snce` constructor. -/
def isFutureOnly : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ => isFutureOnly φ && isFutureOnly ψ
  | .box φ => isFutureOnly φ
  | .untl φ ψ => isFutureOnly φ && isFutureOnly ψ
  | .snce _ _ => false

@[simp] theorem is_future_only_allPast (φ : Formula Atom) :
    isFutureOnly (Formula.allPast φ) = false := by
  simp only [isFutureOnly, Bool.false_and]

@[simp] theorem is_future_only_allFuture (φ : Formula Atom) :
    isFutureOnly (Formula.allFuture φ) = isFutureOnly φ := by
  simp only [isFutureOnly, Bool.and_true]

/-- A formula is "past-only": no `untl` constructor. -/
def isPastOnly : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ => isPastOnly φ && isPastOnly ψ
  | .box φ => isPastOnly φ
  | .untl _ _ => false
  | .snce φ ψ => isPastOnly φ && isPastOnly ψ

@[simp] theorem is_past_only_allPast (φ : Formula Atom) :
    isPastOnly (Formula.allPast φ) = isPastOnly φ := by
  simp only [isPastOnly, Bool.and_true]

@[simp] theorem is_past_only_allFuture (φ : Formula Atom) :
    isPastOnly (Formula.allFuture φ) = false := by
  simp only [isPastOnly, Bool.false_and]

/-- A formula is "properly separated" if it is a boolean combination of
    atoms, future-only formulas under `untl`, past-only formulas under
    `snce`, and box formulas. -/
def isProperlySeparated : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ =>
    isProperlySeparated φ && isProperlySeparated ψ
  | .box _ => true
  | .untl φ ψ => isFutureOnly φ && isFutureOnly ψ
  | .snce φ ψ => isPastOnly φ && isPastOnly ψ

@[simp] theorem is_properly_separated_allPast
    (φ : Formula Atom) :
    isProperlySeparated (Formula.allPast φ) =
      isPastOnly φ := by
  simp only [isProperlySeparated, isPastOnly, Bool.and_true]

@[simp] theorem is_properly_separated_allFuture
    (φ : Formula Atom) :
    isProperlySeparated (Formula.allFuture φ) =
      isFutureOnly φ := by
  simp only [isProperlySeparated, isFutureOnly, Bool.and_true]

/-- A formula is "properly separable" if it is integer-equivalent to a
    properly separated formula. -/
def isProperlySeparable (φ : Formula Atom) : Prop :=
  ∃ ψ : Formula Atom,
    isProperlySeparated ψ = true ∧ intEquiv φ ψ

/-! ## Structural Measures for Induction -/

mutual
/-- Junction depth: maximum alternation depth of U/S nesting. -/
def junctionDepth : Formula Atom -> Nat
  | .atom _ => 0
  | .bot => 0
  | .imp phi psi =>
    max (junctionDepth phi) (junctionDepth psi)
  | .box phi => junctionDepth phi
  | .untl phi psi =>
    max (junctionDepthU phi) (junctionDepthU psi)
  | .snce phi psi =>
    max (junctionDepthS phi) (junctionDepthS psi)

def junctionDepthU : Formula Atom -> Nat
  | .atom _ => 0
  | .bot => 0
  | .imp phi psi =>
    max (junctionDepthU phi) (junctionDepthU psi)
  | .box phi => junctionDepthU phi
  | .untl phi psi =>
    max (junctionDepthU phi) (junctionDepthU psi)
  | .snce phi psi =>
    1 + max (junctionDepth phi) (junctionDepth psi)

def junctionDepthS : Formula Atom -> Nat
  | .atom _ => 0
  | .bot => 0
  | .imp phi psi =>
    max (junctionDepthS phi) (junctionDepthS psi)
  | .box phi => junctionDepthS phi
  | .untl phi psi =>
    1 + max (junctionDepth phi) (junctionDepth psi)
  | .snce phi psi =>
    max (junctionDepthS phi) (junctionDepthS psi)
end

/-! ### Simp lemmas for junctionDepth -/

@[simp] theorem junction_depth_allPast (φ : Formula Atom) :
    junctionDepth (Formula.allPast φ) =
      junctionDepthS φ := by
  simp only [junctionDepth, junctionDepthS]; omega

@[simp] theorem junction_depth_allFuture (φ : Formula Atom) :
    junctionDepth (Formula.allFuture φ) =
      junctionDepthU φ := by
  simp only [junctionDepth, junctionDepthU]; omega

/-- U-nesting depth beneath S. -/
def U_depth_under_S : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => max (U_depth_under_S φ) (U_depth_under_S ψ)
  | .box φ => U_depth_under_S φ
  | .untl φ ψ =>
    1 + max (U_depth_under_S φ) (U_depth_under_S ψ)
  | .snce _ _ => 0

/-- Count of maximal U-subformulas in a formula. -/
def countUSubformulas : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ =>
    countUSubformulas φ + countUSubformulas ψ
  | .box φ => countUSubformulas φ
  | .untl _ _ => 1
  | .snce φ ψ =>
    countUSubformulas φ + countUSubformulas ψ

/-- Total count of ALL `.untl` nodes at ALL depths. -/
def countUTotal : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => countUTotal φ + countUTotal ψ
  | .box φ => countUTotal φ
  | .untl φ ψ => 1 + countUTotal φ + countUTotal ψ
  | .snce φ ψ => countUTotal φ + countUTotal ψ

/-- `countUTotal phi = 0` iff the formula is U-free. -/
theorem count_U_total_zero_iff_U_free
    (phi : Formula Atom) :
    countUTotal phi = 0 ↔ isUFree phi = true := by
  induction phi with
  | atom _ => simp [countUTotal, isUFree]
  | bot => simp [countUTotal, isUFree]
  | imp a b ih1 ih2 =>
    simp only [countUTotal, isUFree,
      Nat.add_eq_zero_iff, Bool.and_eq_true, ih1, ih2]
  | box a ih =>
    simp only [countUTotal, isUFree]; exact ih
  | untl _ _ =>
    simp only [countUTotal, isUFree]
    exact iff_of_false (by omega) (by decide)
  | snce a b ih1 ih2 =>
    simp only [countUTotal, isUFree,
      Nat.add_eq_zero_iff, Bool.and_eq_true, ih1, ih2]

/-- S-nesting depth above U occurrences. -/
def S_nesting_above_U : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ =>
    max (S_nesting_above_U φ) (S_nesting_above_U ψ)
  | .box φ => S_nesting_above_U φ
  | .untl _ _ => 0
  | .snce φ ψ =>
    let sub := max (S_nesting_above_U_inner φ)
      (S_nesting_above_U_inner ψ)
    if sub > 0 then 1 + sub else 0
where
  /-- Helper: counts S-nesting above U inside an S context. -/
  S_nesting_above_U_inner : Formula Atom → Nat
    | .atom _ => 0
    | .bot => 0
    | .imp φ ψ =>
      max (S_nesting_above_U_inner φ)
        (S_nesting_above_U_inner ψ)
    | .box φ => S_nesting_above_U_inner φ
    | .untl _ _ => 1
    | .snce φ ψ =>
      let sub := max (S_nesting_above_U_inner φ)
        (S_nesting_above_U_inner ψ)
      if sub > 0 then 1 + sub else 0

/-! ## Auxiliary Predicates for Elimination Cases -/

/-- Predicate: U only appears as the specific subformula U(A,B),
    not under any S. -/
def uAppearancesTopLevelOnly :
    Formula Atom → Formula Atom → Formula Atom → Prop
  | .atom _, _, _ => True
  | .bot, _, _ => True
  | .imp φ ψ, A, B =>
    uAppearancesTopLevelOnly φ A B ∧
      uAppearancesTopLevelOnly ψ A B
  | .box φ, A, B => uAppearancesTopLevelOnly φ A B
  | .untl φ ψ, A, B => φ = A ∧ ψ = B
  | .snce φ ψ, _, _ =>
    isUFree φ = true ∧ isUFree ψ = true

/-- Predicate: U(A,B) appears only at top level (not under S). -/
def uAppearsOnlyAsTopLevel :
    Formula Atom → Formula Atom → Formula Atom → Prop
  | .atom _, _, _ => True
  | .bot, _, _ => True
  | .imp φ ψ, A, B =>
    uAppearsOnlyAsTopLevel φ A B ∧
      uAppearsOnlyAsTopLevel ψ A B
  | .box φ, A, B => uAppearsOnlyAsTopLevel φ A B
  | .untl φ ψ, A, B =>
    uAppearsOnlyAsTopLevel φ A B ∧
      uAppearsOnlyAsTopLevel ψ A B
  | .snce φ ψ, _, _ =>
    isUFree φ = true ∧ isUFree ψ = true

/-- Predicate: the formula has no S nested within any U. -/
def noSNestedInU : Formula Atom -> Prop
  | .atom _ => True
  | .bot => True
  | .imp phi psi =>
    noSNestedInU phi ∧ noSNestedInU psi
  | .box phi => noSNestedInU phi
  | .untl phi psi =>
    isSFree phi = true ∧ isSFree psi = true
  | .snce phi psi =>
    noSNestedInU phi ∧ noSNestedInU psi

@[simp] theorem no_S_nested_in_U_allPast
    (φ : Formula Atom) :
    noSNestedInU (Formula.allPast φ) ↔
      noSNestedInU φ := by
  simp only [noSNestedInU, and_true]

@[simp] theorem no_S_nested_in_U_allFuture
    (φ : Formula Atom) :
    noSNestedInU (Formula.allFuture φ) ↔
      (isSFree φ = true) := by
  simp only [noSNestedInU, isSFree,
    Bool.and_true, and_true]

/-! ## Semantic Atom Dependence -/

/-- Truth of a formula depends only on atoms in `formulaAtoms`. -/
theorem int_truth_depends_only_on_atoms
    (φ : Formula Atom) (M₁ M₂ : IntStructure Atom) (t : ℤ)
    (h : ∀ a ∈ formulaAtoms φ, M₁.val a = M₂.val a) :
    intTruth M₁ t φ ↔ intTruth M₂ t φ := by
  induction φ generalizing t with
  | atom a =>
    simp only [formulaAtoms, Set.mem_singleton_iff] at h
    simp only [intTruth]; rw [h a rfl]
  | bot => rfl
  | imp c d ih1 ih2 =>
    simp only [intTruth]; exact Iff.imp
      (ih1 t (fun a ha =>
        h a (Set.mem_union_left _ ha)))
      (ih2 t (fun a ha =>
        h a (Set.mem_union_right _ ha)))
  | box _ => rfl
  | untl c d ih1 ih2 =>
    simp only [intTruth]; constructor
    · rintro ⟨s, hts, hc, hd⟩
      exact ⟨s, hts,
        (ih1 s (fun a ha =>
          h a (Set.mem_union_left _ ha))).mp hc,
        fun r hr1 hr2 =>
          (ih2 r (fun a ha =>
            h a (Set.mem_union_right _ ha))).mp
          (hd r hr1 hr2)⟩
    · rintro ⟨s, hts, hc, hd⟩
      exact ⟨s, hts,
        (ih1 s (fun a ha =>
          h a (Set.mem_union_left _ ha))).mpr hc,
        fun r hr1 hr2 =>
          (ih2 r (fun a ha =>
            h a (Set.mem_union_right _ ha))).mpr
          (hd r hr1 hr2)⟩
  | snce c d ih1 ih2 =>
    simp only [intTruth]; constructor
    · rintro ⟨s, hst, hc, hd⟩
      exact ⟨s, hst,
        (ih1 s (fun a ha =>
          h a (Set.mem_union_left _ ha))).mp hc,
        fun r hr1 hr2 =>
          (ih2 r (fun a ha =>
            h a (Set.mem_union_right _ ha))).mp
          (hd r hr1 hr2)⟩
    · rintro ⟨s, hst, hc, hd⟩
      exact ⟨s, hst,
        (ih1 s (fun a ha =>
          h a (Set.mem_union_left _ ha))).mpr hc,
        fun r hr1 hr2 =>
          (ih2 r (fun a ha =>
            h a (Set.mem_union_right _ ha))).mpr
          (hd r hr1 hr2)⟩

/-! ## Predicate Equivalence: Syntactic vs. Proper Separation -/

/-- `isSFree` and `isFutureOnly` are identical predicates. -/
theorem s_free_eq_future_only (φ : Formula Atom) :
    isSFree φ = isFutureOnly φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [isSFree, isFutureOnly, ih1, ih2]
  | box a ih => simp [isSFree, isFutureOnly, ih]
  | untl a b ih1 ih2 =>
    simp [isSFree, isFutureOnly, ih1, ih2]
  | snce _ _ => rfl

/-- `isUFree` and `isPastOnly` are identical predicates. -/
theorem u_free_eq_past_only (φ : Formula Atom) :
    isUFree φ = isPastOnly φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [isUFree, isPastOnly, ih1, ih2]
  | box a ih => simp [isUFree, isPastOnly, ih]
  | untl _ _ => rfl
  | snce a b ih1 ih2 =>
    simp [isUFree, isPastOnly, ih1, ih2]

/-- `isSyntacticallySeparated` and `isProperlySeparated`
    are identical predicates. -/
theorem syn_sep_eq_proper_sep (φ : Formula Atom) :
    isSyntacticallySeparated φ =
      isProperlySeparated φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [isSyntacticallySeparated,
      isProperlySeparated, ih1, ih2]
  | box _ => rfl
  | untl a b _ _ =>
    simp [isSyntacticallySeparated,
      isProperlySeparated, s_free_eq_future_only]
  | snce a b _ _ =>
    simp [isSyntacticallySeparated,
      isProperlySeparated, u_free_eq_past_only]

/-- A formula is separable iff it is properly separable. -/
theorem separable_iff_properly_separable
    (φ : Formula Atom) :
    isSeparable φ ↔ isProperlySeparable φ := by
  constructor
  · rintro ⟨ψ, hsep, hequiv⟩
    exact ⟨ψ, (syn_sep_eq_proper_sep ψ) ▸ hsep, hequiv⟩
  · rintro ⟨ψ, hpsep, hequiv⟩
    exact ⟨ψ,
      (syn_sep_eq_proper_sep ψ).symm ▸ hpsep, hequiv⟩

end Cslib.Logic.Bimodal.Metalogic.Separation
