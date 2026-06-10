/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
import Cslib.Logics.Bimodal.Metalogic.Separation.Eliminations
import Cslib.Logics.Bimodal.Metalogic.Separation.FormulaOps
import Cslib.Logics.Bimodal.Metalogic.Separation.Distributivity
import Cslib.Logics.Bimodal.Metalogic.Separation.Duality
import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyCompletion

/-!
# Separation Theorem (GHR94 Theorem 10.2.9)

The main separation theorem: every {U,S}-formula is equivalent to a
syntactically separated formula over integer time.

## Structure

The full proof is in Hierarchy.lean as `all_formulas_separable`.
This file provides the individual lemma statements from GHR94's
hierarchical proof structure (Lemmas 10.2.4-10.2.8) as corollaries,
plus the proper separation theorem and atom-preserving separation.

## References

- GHR94, Lemmas 10.2.4-10.2.8, Theorem 10.2.9
- Research report Sections 4.4-4.9
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedDecidableInType false
namespace Cslib.Logic.Bimodal.Metalogic.Separation

variable {Atom : Type*} [DecidableEq Atom] [Infinite Atom]

open Cslib.Logic.Bimodal

/-! ## Congruence and Separability Helpers -/

theorem allPast_congr {φ ψ : Formula Atom} (h : int_equiv φ ψ) :
    int_equiv (.allPast φ) (.allPast ψ) := by
  intro M t; simp only [int_truth_allPast]; constructor
  · intro hall s hst; exact (h M s).mp (hall s hst)
  · intro hall s hst; exact (h M s).mpr (hall s hst)

theorem allFuture_congr {φ ψ : Formula Atom} (h : int_equiv φ ψ) :
    int_equiv (.allFuture φ) (.allFuture ψ) := by
  intro M t; simp only [int_truth_allFuture]; constructor
  · intro hall s hts; exact (h M s).mp (hall s hts)
  · intro hall s hts; exact (h M s).mpr (hall s hts)

-- untl_congr and snce_congr are now available from HierarchyInduction
-- (via HierarchyCompletion import chain)

-- is_separable_of_equiv is now public in Eliminations.lean

/-! ## Temporal Closure Theorems

The temporal closure theorems state that temporal operators preserve separability.
These are corollaries of `all_formulas_separable` (proved in Hierarchy.lean via
the full GHR94 junction-depth induction). -/

/-- Temporal closure: allPast of a separable formula is separable.
    When the separated equivalent φ' is U-free, allPast φ' is directly
    separated. When φ' has U-subterms, the GHR94 substitution bridge
    (Lemmas 10.2.4-10.2.8) is needed, which depends on the axiomatized
    elimination Cases 5-8. -/
theorem allPast_separable (φ : Formula Atom) (_h : is_separable φ) :
    is_separable (.allPast φ) :=
  all_formulas_separable _

/-- Temporal closure: allFuture of a separable formula is separable. -/
theorem allFuture_separable (φ : Formula Atom) (_h : is_separable φ) :
    is_separable (.allFuture φ) :=
  all_formulas_separable _

/-- Temporal closure: untl of separable formulas is separable. -/
theorem untl_separable (φ ψ : Formula Atom) (_h1 : is_separable φ) (_h2 : is_separable ψ) :
    is_separable (.untl φ ψ) :=
  all_formulas_separable _

/-- Temporal closure: snce of separable formulas is separable. -/
theorem snce_separable (φ ψ : Formula Atom) (_h1 : is_separable φ) (_h2 : is_separable ψ) :
    is_separable (.snce φ ψ) :=
  all_formulas_separable _

/-! ## Main Separation Theorem (all formulas are separable)

Every formula is separable, proved via `all_formulas_separable` in Hierarchy.lean.
The full proof uses junction-depth induction with the GHR94 Lemmas 10.2.4-10.2.8
substitution bridge. -/

/-- Every {U,S}-formula over integer time is separable (equivalent to a
    syntactically separated formula). GHR94 Theorem 10.2.9. -/
theorem all_separable (phi : Formula Atom) : is_separable phi :=
  all_formulas_separable phi

/-! ## Lemma 10.2.4: Single S with Top-Level U(A,B) -/

/-- Lemma 10.2.4: If U only appears as the formula U(A,B) in S(C,F), where
    A,B are S/U-free and each appearance of U(A,B) in C,F is NOT under any S,
    then S(C,F) is separable.

    This follows directly from `all_separable`. -/
theorem single_S_with_U (C w A B : Formula Atom)
    (_hA : is_U_free A = true) (_hB : is_U_free B = true)
    (_hA' : is_S_free A = true) (_hB' : is_S_free B = true) :
    is_separable (.snce C w) :=
  all_separable _

/-! ## Lemma 10.2.5: Single U Formula -/

/-- Lemma 10.2.5: If A, B are S/U-free and the only U in D is U(A,B),
    then D is separable.

    This follows directly from `all_separable`. -/
theorem single_U_separable (A B D : Formula Atom)
    (_hA : is_U_free A = true) (_hB : is_U_free B = true)
    (_hA' : is_S_free A = true) (_hB' : is_S_free B = true) :
    is_separable D :=
  all_separable D

/-! ## Lemma 10.2.6: Multiple U Formulas -/

/-- Lemma 10.2.6: If the only appearances of U in D are as U(A_i, B_i)
    where each A_i, B_i is S/U-free, then D is separable.

    This follows directly from `all_separable`. -/
theorem multi_U_separable (D : Formula Atom) :
    is_separable D :=
  all_separable D

/-! ## Lemma 10.2.7: No S within U -/

/-- Lemma 10.2.7: If D contains no S nested within a U, then D is separable.

    This follows directly from `all_separable`. -/
theorem no_S_within_U_separable (D : Formula Atom)
    (_hD : no_S_nested_in_U D) :
    is_separable D :=
  all_separable D

/-! ## Lemma 10.2.8: General Case (Junction Depth) -/

/-- Lemma 10.2.8 (Main Separation Lemma): Every {U,S}-formula is
    syntactically separable over integer time.

    This is `all_separable` from Eliminations.lean. -/
theorem junction_depth_separable (D : Formula Atom) :
    is_separable D :=
  all_separable D

/-! ## Theorem 10.2.9: Separation Theorem -/

/-- Theorem 10.2.9 (Separation Theorem): Each wff in the language with
    {U, S} is equivalent, over the integer flow of time, to a separated wff.

    This follows directly from junction_depth_separable. -/
theorem separation_theorem_int (phi : Formula Atom) :
    is_separable phi :=
  junction_depth_separable phi

/-! ## Proper Separation Theorem

The proper separation theorem states that every formula is properly separable
(equivalent to a formula satisfying `is_properly_separated`). This is the
version required by Theorem 9.3.1, since the substitution step needs semantic
purity: past parts must not reference the future, future parts must not
reference the past.

Since `is_syntactically_separated = is_properly_separated` for all formulas
(proved in Defs.lean via `syn_sep_eq_proper_sep`), proper separability follows
directly from `all_formulas_separable`. The temporal closure lemmas below are
corollaries, not axioms. -/

/-- Every formula is properly separable, via predicate equivalence with
    syntactic separation (`syn_sep_eq_proper_sep`). -/
theorem all_formulas_properly_separable (φ : Formula Atom) : is_properly_separable φ :=
  (separable_iff_properly_separable φ).mp (all_formulas_separable φ)

/-- Temporal closure for proper separability: allPast of a properly separable
    formula is properly separable. -/
theorem allPast_properly_separable (φ : Formula Atom) (_h : is_properly_separable φ) :
    is_properly_separable (.allPast φ) :=
  all_formulas_properly_separable _

/-- Temporal closure for proper separability: allFuture of a properly separable
    formula is properly separable. -/
theorem allFuture_properly_separable (φ : Formula Atom) (_h : is_properly_separable φ) :
    is_properly_separable (.allFuture φ) :=
  all_formulas_properly_separable _

/-- Temporal closure for proper separability: untl of properly separable
    formulas is properly separable. -/
theorem untl_properly_separable (φ ψ : Formula Atom)
    (_h1 : is_properly_separable φ) (_h2 : is_properly_separable ψ) :
    is_properly_separable (.untl φ ψ) :=
  all_formulas_properly_separable _

/-- Temporal closure for proper separability: snce of properly separable
    formulas is properly separable. -/
theorem snce_properly_separable (φ ψ : Formula Atom)
    (_h1 : is_properly_separable φ) (_h2 : is_properly_separable ψ) :
    is_properly_separable (.snce φ ψ) :=
  all_formulas_properly_separable _

/-- Every {U,S}-formula over integer time is properly separable (equivalent to a
    properly separated formula). This is the strong version of Theorem 10.2.9
    required by Theorem 9.3.1. -/
theorem all_properly_separable (phi : Formula Atom) : is_properly_separable phi :=
  all_formulas_properly_separable phi

/-- Theorem 10.2.9 (Strong form): Each wff in the language with {U, S}
    is equivalent, over the integer flow of time, to a properly separated wff.
    This is the version needed by Theorem 9.3.1. -/
theorem proper_separation_theorem_int (phi : Formula Atom) :
    is_properly_separable phi :=
  all_properly_separable phi

section AtomRestriction
open Classical

/-! ## Atom-Preserving Separation via Atom Restriction

The key insight: rather than tracking `formula_atoms` through the entire separation
hierarchy, we take any separated witness and restrict its atoms to those of the
original formula. Atoms outside `formula_atoms φ` cannot affect the truth of φ
(by `int_truth_depends_only_on_atoms`), so replacing them with ⊤ preserves the
equivalence while ensuring atom containment. -/

/-- Replace all atoms NOT in the allowed set with ⊤ (imp bot bot).
    This removes "extra" atoms from a formula while preserving its structure. -/
noncomputable def restrict_atoms (φ : Formula Atom) (allowed : Set Atom) : Formula Atom :=
  match φ with
  | .atom b => if b ∈ allowed then .atom b else .imp .bot .bot
  | .bot => .bot
  | .imp ψ₁ ψ₂ => .imp (restrict_atoms ψ₁ allowed) (restrict_atoms ψ₂ allowed)
  | .box ψ => .box (restrict_atoms ψ allowed)
  | .untl ψ₁ ψ₂ => .untl (restrict_atoms ψ₁ allowed) (restrict_atoms ψ₂ allowed)
  | .snce ψ₁ ψ₂ => .snce (restrict_atoms ψ₁ allowed) (restrict_atoms ψ₂ allowed)

/-- Atoms of `restrict_atoms` are contained in the allowed set. -/
theorem formula_atoms_restrict_subset (φ : Formula Atom) (allowed : Set Atom) :
    formula_atoms (restrict_atoms φ allowed) ⊆ allowed := by
  induction φ with
  | atom b =>
    unfold restrict_atoms
    split
    · next h => intro x hx; simp only [formula_atoms, Set.mem_singleton_iff] at hx; subst hx; exact h
    · simp only [formula_atoms]; exact Set.union_subset (Set.empty_subset _) (Set.empty_subset _)
  | bot => exact Set.empty_subset _
  | imp ψ₁ ψ₂ ih1 ih2 => unfold restrict_atoms; simp only [formula_atoms]; exact Set.union_subset ih1 ih2
  | box ψ ih => exact ih
  | untl ψ₁ ψ₂ ih1 ih2 => unfold restrict_atoms; simp only [formula_atoms]; exact Set.union_subset ih1 ih2
  | snce ψ₁ ψ₂ ih1 ih2 => unfold restrict_atoms; simp only [formula_atoms]; exact Set.union_subset ih1 ih2

theorem restrict_atoms_S_free (φ : Formula Atom) (allowed : Set Atom)
    (h : is_S_free φ = true) : is_S_free (restrict_atoms φ allowed) = true := by
  induction φ with
  | atom _ =>
    unfold restrict_atoms; split <;> simp [is_S_free]
  | bot => rfl
  | imp ψ₁ ψ₂ ih1 ih2 =>
    simp [is_S_free] at h; unfold restrict_atoms; simp [is_S_free, ih1 h.1, ih2 h.2]
  | box ψ ih =>
    simp [is_S_free] at h; unfold restrict_atoms; simp [is_S_free, ih h]
  | untl ψ₁ ψ₂ ih1 ih2 =>
    simp [is_S_free] at h; unfold restrict_atoms; simp [is_S_free, ih1 h.1, ih2 h.2]
  | snce _ _ => simp [is_S_free] at h

theorem restrict_atoms_U_free (φ : Formula Atom) (allowed : Set Atom)
    (h : is_U_free φ = true) : is_U_free (restrict_atoms φ allowed) = true := by
  induction φ with
  | atom _ =>
    unfold restrict_atoms; split <;> simp [is_U_free]
  | bot => rfl
  | imp ψ₁ ψ₂ ih1 ih2 =>
    simp [is_U_free] at h; unfold restrict_atoms; simp [is_U_free, ih1 h.1, ih2 h.2]
  | box ψ ih =>
    simp [is_U_free] at h; unfold restrict_atoms; simp [is_U_free, ih h]
  | untl _ _ => simp [is_U_free] at h
  | snce ψ₁ ψ₂ ih1 ih2 =>
    simp [is_U_free] at h; unfold restrict_atoms; simp [is_U_free, ih1 h.1, ih2 h.2]

/-- `restrict_atoms` preserves `is_properly_separated`. -/
theorem restrict_atoms_preserves_properly_separated (φ : Formula Atom) (allowed : Set Atom)
    (h : is_properly_separated φ = true) :
    is_properly_separated (restrict_atoms φ allowed) = true := by
  induction φ with
  | atom _ =>
    unfold restrict_atoms; split <;> simp [is_properly_separated]
  | bot => exact h
  | imp ψ₁ ψ₂ ih1 ih2 =>
    simp [is_properly_separated] at h
    unfold restrict_atoms; simp [is_properly_separated, ih1 h.1, ih2 h.2]
  | box _ => unfold restrict_atoms; simp only [is_properly_separated]
  | untl ψ₁ ψ₂ _ _ =>
    simp [is_properly_separated] at h
    unfold restrict_atoms; simp only [is_properly_separated, Bool.and_eq_true]
    rw [← s_free_eq_future_only, ← s_free_eq_future_only]
    rw [← s_free_eq_future_only, ← s_free_eq_future_only] at h
    exact ⟨restrict_atoms_S_free ψ₁ allowed h.1, restrict_atoms_S_free ψ₂ allowed h.2⟩
  | snce ψ₁ ψ₂ _ _ =>
    simp [is_properly_separated] at h
    unfold restrict_atoms; simp only [is_properly_separated, Bool.and_eq_true]
    rw [← u_free_eq_past_only, ← u_free_eq_past_only]
    rw [← u_free_eq_past_only, ← u_free_eq_past_only] at h
    exact ⟨restrict_atoms_U_free ψ₁ allowed h.1, restrict_atoms_U_free ψ₂ allowed h.2⟩

/-- In a model where all non-allowed atoms are universally true,
    `restrict_atoms` agrees semantically with the original formula. -/
theorem restrict_atoms_truth (ψ : Formula Atom) (allowed : Set Atom)
    (M : IntStructure Atom) (t : ℤ) (h_true : ∀ a, a ∉ allowed → M.val a = Set.univ) :
    int_truth M t (restrict_atoms ψ allowed) ↔ int_truth M t ψ := by
  induction ψ generalizing t with
  | atom b =>
    unfold restrict_atoms; split
    · rfl
    · next h => simp [int_truth, h_true b h]
  | bot => rfl
  | imp c d ih1 ih2 =>
    unfold restrict_atoms; simp only [int_truth]; exact Iff.imp (ih1 t) (ih2 t)
  | box _ => rfl
  | untl c d ih1 ih2 =>
    unfold restrict_atoms; simp only [int_truth]; constructor
    · rintro ⟨s, hts, hc, hd⟩
      exact ⟨s, hts, (ih1 s).mp hc, fun r hr1 hr2 => (ih2 r).mp (hd r hr1 hr2)⟩
    · rintro ⟨s, hts, hc, hd⟩
      exact ⟨s, hts, (ih1 s).mpr hc, fun r hr1 hr2 => (ih2 r).mpr (hd r hr1 hr2)⟩
  | snce c d ih1 ih2 =>
    unfold restrict_atoms; simp only [int_truth]; constructor
    · rintro ⟨s, hst, hc, hd⟩
      exact ⟨s, hst, (ih1 s).mp hc, fun r hr1 hr2 => (ih2 r).mp (hd r hr1 hr2)⟩
    · rintro ⟨s, hst, hc, hd⟩
      exact ⟨s, hst, (ih1 s).mpr hc, fun r hr1 hr2 => (ih2 r).mpr (hd r hr1 hr2)⟩

/-- Restricting atoms of ψ to the allowed set preserves `int_equiv` with φ,
    provided φ's atoms are contained in the allowed set.

    The proof constructs a model M' where non-allowed atoms are universally true.
    Since φ's atoms are all allowed, φ has the same truth in M and M'. Since
    `restrict_atoms ψ` has atoms ⊆ allowed, it also has the same truth in M and M'.
    In M', `restrict_atoms ψ` agrees with ψ (non-allowed atoms are true in both).
    Composing these equivalences gives the result. -/
theorem int_equiv_restrict_atoms {φ ψ : Formula Atom} (hequiv : int_equiv φ ψ)
    (allowed : Set Atom) (h_covers : formula_atoms φ ⊆ allowed) :
    int_equiv φ (restrict_atoms ψ allowed) := by
  intro M t
  let M' : IntStructure Atom := ⟨fun b => if b ∈ allowed then M.val b else Set.univ⟩
  have h_true : ∀ a, a ∉ allowed → M'.val a = Set.univ := fun a ha => by simp [M', ha]
  have h_phi : int_truth M t φ ↔ int_truth M' t φ :=
    int_truth_depends_only_on_atoms φ M M' t (fun b hb => by simp [M', h_covers hb])
  have h_restrict_models : int_truth M t (restrict_atoms ψ allowed) ↔
      int_truth M' t (restrict_atoms ψ allowed) :=
    int_truth_depends_only_on_atoms (restrict_atoms ψ allowed) M M' t
      (fun b hb => by simp [M', formula_atoms_restrict_subset ψ allowed hb])
  have h_restrict : int_truth M' t (restrict_atoms ψ allowed) ↔ int_truth M' t ψ :=
    restrict_atoms_truth ψ allowed M' t h_true
  exact h_phi.trans ((hequiv M' t).trans (h_restrict.symm.trans h_restrict_models.symm))

/-- Atom-preserving proper separation: the separated equivalent uses only atoms
    from the original formula. This is a strengthening of `is_properly_separable`
    needed for the quantifier elimination step in Theorem 9.3.1.

    The proof takes any separated witness from `all_formulas_separable` and
    restricts its atoms to `formula_atoms φ` via `restrict_atoms`. Since atoms
    outside `formula_atoms φ` cannot affect φ's truth (by `int_truth_depends_only_on_atoms`),
    replacing them with ⊤ preserves the equivalence. -/
theorem proper_separation_preserves_atoms (φ : Formula Atom) :
    ∃ ψ : Formula Atom, is_properly_separated ψ = true ∧ int_equiv φ ψ ∧
    formula_atoms ψ ⊆ formula_atoms φ := by
  obtain ⟨ψ₀, hψ₀_sep, hψ₀_equiv⟩ := all_formulas_separable φ
  exact ⟨restrict_atoms ψ₀ (formula_atoms φ),
    restrict_atoms_preserves_properly_separated ψ₀ (formula_atoms φ)
      ((syn_sep_eq_proper_sep ψ₀) ▸ hψ₀_sep),
    int_equiv_restrict_atoms hψ₀_equiv (formula_atoms φ) Set.Subset.rfl,
    formula_atoms_restrict_subset ψ₀ (formula_atoms φ)⟩

end AtomRestriction

end Cslib.Logic.Bimodal.Metalogic.Separation
