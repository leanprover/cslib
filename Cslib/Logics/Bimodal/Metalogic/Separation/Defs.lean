/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Syntax.Formula
import Mathlib.Algebra.Order.Group.Int

set_option linter.style.emptyLine false

/-!
# Separation Definitions: Integer Temporal Semantics

Core definitions for the separation theorem over integer time (GHR94 Chapter 10.2).

## Key Definitions

- `IntStructure`: A temporal structure over integers (valuation on Z)
- `int_truth`: Recursive truth evaluation for formulas over Z
- `int_equiv`: Semantic equivalence over integer time
- `is_pure_past`, `is_pure_future`, `is_pure_present`: Semantic purity predicates
- `is_U_free`, `is_S_free`: Syntactic absence predicates (decidable)
- `is_syntactically_separated`: Recursive syntactic separation check
- `is_separable`: Existential separation predicate
- `junction_depth`, `U_depth_under_S`, `count_U_subformulas`: Structural measures

## References

- GHR94, Chapter 10, Section 10.2 (pp. 569-592)
-/

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
def int_truth (M : IntStructure Atom) (t : ℤ) : Formula Atom → Prop
  | .atom a => t ∈ M.val a
  | .bot => False
  | .imp φ ψ => int_truth M t φ → int_truth M t ψ
  | .box _ => True
  | .untl φ ψ => ∃ s : ℤ, t < s ∧ int_truth M s φ ∧
      ∀ r : ℤ, t < r → r < s → int_truth M r ψ
  | .snce φ ψ => ∃ s : ℤ, s < t ∧ int_truth M s φ ∧
      ∀ r : ℤ, s < r → r < t → int_truth M r ψ

/-! ## int_truth simp lemmas for derived temporal operators -/

@[simp] theorem int_truth_allPast
    (M : IntStructure Atom) (t : ℤ) (φ : Formula Atom) :
    int_truth M t (Formula.allPast φ) ↔
      ∀ s : ℤ, s < t → int_truth M s φ := by
  simp only [int_truth]
  constructor
  · intro h s hs
    by_contra hns
    exact h ⟨s, hs, hns, fun _ _ _ h => h⟩
  · rintro h ⟨s, hs, hns, _⟩
    exact hns (h s hs)

@[simp] theorem int_truth_allFuture
    (M : IntStructure Atom) (t : ℤ) (φ : Formula Atom) :
    int_truth M t (Formula.allFuture φ) ↔
      ∀ s : ℤ, t < s → int_truth M s φ := by
  simp only [int_truth]
  constructor
  · intro h s hs
    by_contra hns
    exact h ⟨s, hs, hns, fun _ _ _ h => h⟩
  · rintro h ⟨s, hs, hns, _⟩
    exact hns (h s hs)

@[simp] theorem int_truth_somePast
    (M : IntStructure Atom) (t : ℤ) (φ : Formula Atom) :
    int_truth M t (Formula.somePast φ) ↔
      ∃ s : ℤ, s < t ∧ int_truth M s φ := by
  simp only [int_truth]
  constructor
  · rintro ⟨s, hs, hphi, _⟩
    exact ⟨s, hs, hphi⟩
  · rintro ⟨s, hs, hphi⟩
    exact ⟨s, hs, hphi, fun _ _ _ h => h⟩

@[simp] theorem int_truth_someFuture
    (M : IntStructure Atom) (t : ℤ) (φ : Formula Atom) :
    int_truth M t (Formula.someFuture φ) ↔
      ∃ s : ℤ, t < s ∧ int_truth M s φ := by
  simp only [int_truth]
  constructor
  · rintro ⟨s, hs, hphi, _⟩
    exact ⟨s, hs, hphi⟩
  · rintro ⟨s, hs, hphi⟩
    exact ⟨s, hs, hphi, fun _ _ _ h => h⟩

@[simp] theorem int_truth_neg
    (M : IntStructure Atom) (t : ℤ) (φ : Formula Atom) :
    int_truth M t (Formula.neg φ) ↔ ¬ int_truth M t φ := by
  simp only [int_truth]

@[simp] theorem int_truth_and
    (M : IntStructure Atom) (t : ℤ) (φ ψ : Formula Atom) :
    int_truth M t (Formula.and φ ψ) ↔
      int_truth M t φ ∧ int_truth M t ψ := by
  simp only [int_truth]; tauto

@[simp] theorem int_truth_or
    (M : IntStructure Atom) (t : ℤ) (φ ψ : Formula Atom) :
    int_truth M t (Formula.or φ ψ) ↔
      int_truth M t φ ∨ int_truth M t ψ := by
  simp only [int_truth]; tauto

@[simp] theorem int_truth_top (M : IntStructure Atom) (t : ℤ) :
    int_truth M t (Formula.top : Formula Atom) ↔ True := by
  simp only [int_truth]; tauto

/-! ## Formula Atoms -/

/-- Collect all atoms occurring in a formula (as a `Set Atom`). -/
def formula_atoms : Formula Atom → Set Atom
  | .atom a => {a}
  | .bot => ∅
  | .imp φ ψ => formula_atoms φ ∪ formula_atoms ψ
  | .box φ => formula_atoms φ
  | .untl φ ψ => formula_atoms φ ∪ formula_atoms ψ
  | .snce φ ψ => formula_atoms φ ∪ formula_atoms ψ

@[simp] theorem formula_atoms_allPast (φ : Formula Atom) :
    formula_atoms (Formula.allPast φ) = formula_atoms φ := by
  simp only [formula_atoms]
  ext a; simp only [Set.mem_union, Set.mem_empty_iff_false, or_false]

@[simp] theorem formula_atoms_allFuture (φ : Formula Atom) :
    formula_atoms (Formula.allFuture φ) = formula_atoms φ := by
  simp only [formula_atoms]
  ext a; simp only [Set.mem_union, Set.mem_empty_iff_false, or_false]

/-! ## Semantic Equivalence -/

/-- Semantic equivalence of formulas over integer time. -/
def int_equiv (φ ψ : Formula Atom) : Prop :=
  ∀ (M : IntStructure Atom) (t : ℤ), int_truth M t φ ↔ int_truth M t ψ

/-- int_equiv is reflexive. -/
theorem int_equiv_refl (φ : Formula Atom) : int_equiv φ φ :=
  fun _ _ => Iff.rfl

/-- int_equiv is symmetric. -/
theorem int_equiv_symm {φ ψ : Formula Atom}
    (h : int_equiv φ ψ) : int_equiv ψ φ :=
  fun M t => (h M t).symm

/-- int_equiv is transitive. -/
theorem int_equiv_trans {φ ψ χ : Formula Atom}
    (h1 : int_equiv φ ψ) (h2 : int_equiv ψ χ) :
    int_equiv φ χ :=
  fun M t => (h1 M t).trans (h2 M t)

/-! ## Semantic Purity Predicates -/

/-- A formula is "pure past" if its truth at t depends only on
    the past of t. -/
def is_pure_past (φ : Formula Atom) : Prop :=
  ∀ (M₁ M₂ : IntStructure Atom) (t : ℤ),
    (∀ (a : Atom) (s : ℤ),
      s < t → (s ∈ M₁.val a ↔ s ∈ M₂.val a)) →
    (int_truth M₁ t φ ↔ int_truth M₂ t φ)

/-- A formula is "pure future" if its truth at t depends only on
    the future of t. -/
def is_pure_future (φ : Formula Atom) : Prop :=
  ∀ (M₁ M₂ : IntStructure Atom) (t : ℤ),
    (∀ (a : Atom) (s : ℤ),
      t < s → (s ∈ M₁.val a ↔ s ∈ M₂.val a)) →
    (int_truth M₁ t φ ↔ int_truth M₂ t φ)

/-- A formula is "pure present" if its truth at t depends only on
    time t. -/
def is_pure_present (φ : Formula Atom) : Prop :=
  ∀ (M₁ M₂ : IntStructure Atom) (t : ℤ),
    (∀ (a : Atom), (t ∈ M₁.val a ↔ t ∈ M₂.val a)) →
    (int_truth M₁ t φ ↔ int_truth M₂ t φ)

/-! ## Syntactic Predicates -/

/-- A formula is "syntactically U-free": no `untl` constructor. -/
def is_U_free : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ => is_U_free φ && is_U_free ψ
  | .box φ => is_U_free φ
  | .untl _ _ => false
  | .snce φ ψ => is_U_free φ && is_U_free ψ

/-- A formula is "syntactically S-free": no `snce` constructor. -/
def is_S_free : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ => is_S_free φ && is_S_free ψ
  | .box φ => is_S_free φ
  | .untl φ ψ => is_S_free φ && is_S_free ψ
  | .snce _ _ => false

/-! ### Simp lemmas for is_U_free and is_S_free -/

@[simp] theorem is_U_free_allPast (φ : Formula Atom) :
    is_U_free (Formula.allPast φ) = is_U_free φ := by
  simp only [is_U_free, Bool.and_true]

@[simp] theorem is_U_free_allFuture (φ : Formula Atom) :
    is_U_free (Formula.allFuture φ) = false := by
  simp only [is_U_free, Bool.false_and]

@[simp] theorem is_S_free_allPast (φ : Formula Atom) :
    is_S_free (Formula.allPast φ) = false := by
  simp only [is_S_free, Bool.false_and]

@[simp] theorem is_S_free_allFuture (φ : Formula Atom) :
    is_S_free (Formula.allFuture φ) = is_S_free φ := by
  simp only [is_S_free, Bool.and_true]

/-- A formula is "syntactically separated" if it is a boolean combination
    of atoms, U-formulas with S-free arguments, S-formulas with U-free
    arguments, and box formulas. -/
def is_syntactically_separated : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ =>
    is_syntactically_separated φ && is_syntactically_separated ψ
  | .box _ => true
  | .untl φ ψ => is_S_free φ && is_S_free ψ
  | .snce φ ψ => is_U_free φ && is_U_free ψ

@[simp] theorem is_syntactically_separated_allPast
    (φ : Formula Atom) :
    is_syntactically_separated (Formula.allPast φ) =
      is_U_free φ := by
  simp only [is_syntactically_separated, is_U_free, Bool.and_true]

@[simp] theorem is_syntactically_separated_allFuture
    (φ : Formula Atom) :
    is_syntactically_separated (Formula.allFuture φ) =
      is_S_free φ := by
  simp only [is_syntactically_separated, is_S_free, Bool.and_true]

/-- A formula is "separable" if it is integer-equivalent to a
    syntactically separated formula. -/
def is_separable (φ : Formula Atom) : Prop :=
  ∃ ψ : Formula Atom,
    is_syntactically_separated ψ = true ∧ int_equiv φ ψ

/-! ## Proper Purity Predicates -/

/-- A formula is "future-only": no `snce` constructor. -/
def is_future_only : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ => is_future_only φ && is_future_only ψ
  | .box φ => is_future_only φ
  | .untl φ ψ => is_future_only φ && is_future_only ψ
  | .snce _ _ => false

@[simp] theorem is_future_only_allPast (φ : Formula Atom) :
    is_future_only (Formula.allPast φ) = false := by
  simp only [is_future_only, Bool.false_and]

@[simp] theorem is_future_only_allFuture (φ : Formula Atom) :
    is_future_only (Formula.allFuture φ) = is_future_only φ := by
  simp only [is_future_only, Bool.and_true]

/-- A formula is "past-only": no `untl` constructor. -/
def is_past_only : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ => is_past_only φ && is_past_only ψ
  | .box φ => is_past_only φ
  | .untl _ _ => false
  | .snce φ ψ => is_past_only φ && is_past_only ψ

@[simp] theorem is_past_only_allPast (φ : Formula Atom) :
    is_past_only (Formula.allPast φ) = is_past_only φ := by
  simp only [is_past_only, Bool.and_true]

@[simp] theorem is_past_only_allFuture (φ : Formula Atom) :
    is_past_only (Formula.allFuture φ) = false := by
  simp only [is_past_only, Bool.false_and]

/-- A formula is "properly separated" if it is a boolean combination of
    atoms, future-only formulas under `untl`, past-only formulas under
    `snce`, and box formulas. -/
def is_properly_separated : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ =>
    is_properly_separated φ && is_properly_separated ψ
  | .box _ => true
  | .untl φ ψ => is_future_only φ && is_future_only ψ
  | .snce φ ψ => is_past_only φ && is_past_only ψ

@[simp] theorem is_properly_separated_allPast
    (φ : Formula Atom) :
    is_properly_separated (Formula.allPast φ) =
      is_past_only φ := by
  simp only [is_properly_separated, is_past_only, Bool.and_true]

@[simp] theorem is_properly_separated_allFuture
    (φ : Formula Atom) :
    is_properly_separated (Formula.allFuture φ) =
      is_future_only φ := by
  simp only [is_properly_separated, is_future_only, Bool.and_true]

/-- A formula is "properly separable" if it is integer-equivalent to a
    properly separated formula. -/
def is_properly_separable (φ : Formula Atom) : Prop :=
  ∃ ψ : Formula Atom,
    is_properly_separated ψ = true ∧ int_equiv φ ψ

/-! ## Structural Measures for Induction -/

mutual
/-- Junction depth: maximum alternation depth of U/S nesting. -/
def junction_depth : Formula Atom -> Nat
  | .atom _ => 0
  | .bot => 0
  | .imp phi psi =>
    max (junction_depth phi) (junction_depth psi)
  | .box phi => junction_depth phi
  | .untl phi psi =>
    max (junction_depth_U phi) (junction_depth_U psi)
  | .snce phi psi =>
    max (junction_depth_S phi) (junction_depth_S psi)

def junction_depth_U : Formula Atom -> Nat
  | .atom _ => 0
  | .bot => 0
  | .imp phi psi =>
    max (junction_depth_U phi) (junction_depth_U psi)
  | .box phi => junction_depth_U phi
  | .untl phi psi =>
    max (junction_depth_U phi) (junction_depth_U psi)
  | .snce phi psi =>
    1 + max (junction_depth phi) (junction_depth psi)

def junction_depth_S : Formula Atom -> Nat
  | .atom _ => 0
  | .bot => 0
  | .imp phi psi =>
    max (junction_depth_S phi) (junction_depth_S psi)
  | .box phi => junction_depth_S phi
  | .untl phi psi =>
    1 + max (junction_depth phi) (junction_depth psi)
  | .snce phi psi =>
    max (junction_depth_S phi) (junction_depth_S psi)
end

/-! ### Simp lemmas for junction_depth -/

@[simp] theorem junction_depth_allPast (φ : Formula Atom) :
    junction_depth (Formula.allPast φ) =
      junction_depth_S φ := by
  simp only [junction_depth, junction_depth_S]; omega

@[simp] theorem junction_depth_allFuture (φ : Formula Atom) :
    junction_depth (Formula.allFuture φ) =
      junction_depth_U φ := by
  simp only [junction_depth, junction_depth_U]; omega

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
def count_U_subformulas : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ =>
    count_U_subformulas φ + count_U_subformulas ψ
  | .box φ => count_U_subformulas φ
  | .untl _ _ => 1
  | .snce φ ψ =>
    count_U_subformulas φ + count_U_subformulas ψ

/-- Total count of ALL `.untl` nodes at ALL depths. -/
def count_U_total : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => count_U_total φ + count_U_total ψ
  | .box φ => count_U_total φ
  | .untl φ ψ => 1 + count_U_total φ + count_U_total ψ
  | .snce φ ψ => count_U_total φ + count_U_total ψ

/-- `count_U_total phi = 0` iff the formula is U-free. -/
theorem count_U_total_zero_iff_U_free
    (phi : Formula Atom) :
    count_U_total phi = 0 ↔ is_U_free phi = true := by
  induction phi with
  | atom _ => simp [count_U_total, is_U_free]
  | bot => simp [count_U_total, is_U_free]
  | imp a b ih1 ih2 =>
    simp only [count_U_total, is_U_free,
      Nat.add_eq_zero_iff, Bool.and_eq_true, ih1, ih2]
  | box a ih =>
    simp only [count_U_total, is_U_free]; exact ih
  | untl _ _ =>
    simp only [count_U_total, is_U_free]
    exact iff_of_false (by omega) (by decide)
  | snce a b ih1 ih2 =>
    simp only [count_U_total, is_U_free,
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
def u_appearances_top_level_only :
    Formula Atom → Formula Atom → Formula Atom → Prop
  | .atom _, _, _ => True
  | .bot, _, _ => True
  | .imp φ ψ, A, B =>
    u_appearances_top_level_only φ A B ∧
      u_appearances_top_level_only ψ A B
  | .box φ, A, B => u_appearances_top_level_only φ A B
  | .untl φ ψ, A, B => φ = A ∧ ψ = B
  | .snce φ ψ, _, _ =>
    is_U_free φ = true ∧ is_U_free ψ = true

/-- Predicate: U(A,B) appears only at top level (not under S). -/
def u_appears_only_as_top_level :
    Formula Atom → Formula Atom → Formula Atom → Prop
  | .atom _, _, _ => True
  | .bot, _, _ => True
  | .imp φ ψ, A, B =>
    u_appears_only_as_top_level φ A B ∧
      u_appears_only_as_top_level ψ A B
  | .box φ, A, B => u_appears_only_as_top_level φ A B
  | .untl φ ψ, A, B =>
    u_appears_only_as_top_level φ A B ∧
      u_appears_only_as_top_level ψ A B
  | .snce φ ψ, _, _ =>
    is_U_free φ = true ∧ is_U_free ψ = true

/-- Predicate: the formula has no S nested within any U. -/
def no_S_nested_in_U : Formula Atom -> Prop
  | .atom _ => True
  | .bot => True
  | .imp phi psi =>
    no_S_nested_in_U phi ∧ no_S_nested_in_U psi
  | .box phi => no_S_nested_in_U phi
  | .untl phi psi =>
    is_S_free phi = true ∧ is_S_free psi = true
  | .snce phi psi =>
    no_S_nested_in_U phi ∧ no_S_nested_in_U psi

@[simp] theorem no_S_nested_in_U_allPast
    (φ : Formula Atom) :
    no_S_nested_in_U (Formula.allPast φ) ↔
      no_S_nested_in_U φ := by
  simp only [no_S_nested_in_U, and_true]

@[simp] theorem no_S_nested_in_U_allFuture
    (φ : Formula Atom) :
    no_S_nested_in_U (Formula.allFuture φ) ↔
      (is_S_free φ = true) := by
  simp only [no_S_nested_in_U, is_S_free,
    Bool.and_true, and_true]

/-! ## Semantic Atom Dependence -/

/-- Truth of a formula depends only on atoms in `formula_atoms`. -/
theorem int_truth_depends_only_on_atoms
    (φ : Formula Atom) (M₁ M₂ : IntStructure Atom) (t : ℤ)
    (h : ∀ a ∈ formula_atoms φ, M₁.val a = M₂.val a) :
    int_truth M₁ t φ ↔ int_truth M₂ t φ := by
  induction φ generalizing t with
  | atom a =>
    simp only [formula_atoms, Set.mem_singleton_iff] at h
    simp only [int_truth]; rw [h a rfl]
  | bot => rfl
  | imp c d ih1 ih2 =>
    simp only [int_truth]; exact Iff.imp
      (ih1 t (fun a ha =>
        h a (Set.mem_union_left _ ha)))
      (ih2 t (fun a ha =>
        h a (Set.mem_union_right _ ha)))
  | box _ => rfl
  | untl c d ih1 ih2 =>
    simp only [int_truth]; constructor
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
    simp only [int_truth]; constructor
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

/-- `is_S_free` and `is_future_only` are identical predicates. -/
theorem s_free_eq_future_only (φ : Formula Atom) :
    is_S_free φ = is_future_only φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_S_free, is_future_only, ih1, ih2]
  | box a ih => simp [is_S_free, is_future_only, ih]
  | untl a b ih1 ih2 =>
    simp [is_S_free, is_future_only, ih1, ih2]
  | snce _ _ => rfl

/-- `is_U_free` and `is_past_only` are identical predicates. -/
theorem u_free_eq_past_only (φ : Formula Atom) :
    is_U_free φ = is_past_only φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_U_free, is_past_only, ih1, ih2]
  | box a ih => simp [is_U_free, is_past_only, ih]
  | untl _ _ => rfl
  | snce a b ih1 ih2 =>
    simp [is_U_free, is_past_only, ih1, ih2]

/-- `is_syntactically_separated` and `is_properly_separated`
    are identical predicates. -/
theorem syn_sep_eq_proper_sep (φ : Formula Atom) :
    is_syntactically_separated φ =
      is_properly_separated φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_syntactically_separated,
      is_properly_separated, ih1, ih2]
  | box _ => rfl
  | untl a b _ _ =>
    simp [is_syntactically_separated,
      is_properly_separated, s_free_eq_future_only]
  | snce a b _ _ =>
    simp [is_syntactically_separated,
      is_properly_separated, u_free_eq_past_only]

/-- A formula is separable iff it is properly separable. -/
theorem separable_iff_properly_separable
    (φ : Formula Atom) :
    is_separable φ ↔ is_properly_separable φ := by
  constructor
  · rintro ⟨ψ, hsep, hequiv⟩
    exact ⟨ψ, (syn_sep_eq_proper_sep ψ) ▸ hsep, hequiv⟩
  · rintro ⟨ψ, hpsep, hequiv⟩
    exact ⟨ψ,
      (syn_sep_eq_proper_sep ψ).symm ▸ hpsep, hequiv⟩

end Cslib.Logic.Bimodal.Metalogic.Separation
