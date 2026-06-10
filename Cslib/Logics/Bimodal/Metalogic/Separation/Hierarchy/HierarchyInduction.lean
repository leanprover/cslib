/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyDefs
import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyCaseSep

/-!
# Substitution-Based Induction Engine for the Separation Hierarchy (Steps 1-5b)

Hierarchy theorem steps 1-5b: substitution preservation, strict count decrease,
count_U_total lemmas, substitution into separated formulas, S/U-nesting depth
measures, and callback infrastructure.
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedDecidableInType false
set_option linter.style.maxHeartbeats false
namespace Cslib.Logic.Bimodal.Metalogic.Separation

variable {Atom : Type*} [DecidableEq Atom]

open Cslib.Logic.Bimodal

/-! ## Hierarchy Theorem (GHR94 Lemmas 10.2.5-10.2.8)

This section proves the full hierarchy as theorems (no axioms).
The chain is: Cases 1-8 -> no_S_nested_in_U_separable -> junction_depth_separable
-> all_formulas_separable. No circular dependencies.

### Key Technique: Constituent Substitution

After abstracting a U-type to a fresh atom and separating the result,
we substitute back into the separated formula. The crucial insight:
- In `.untl` positions of a separated formula, args are S-free.
  Substituting an S-free `.untl A B` preserves S-freeness.
- In `.snce` positions of a separated formula, args are U-free.
  Substituting `.untl A B` for an atom in U-free args creates
  `no_S_nested_in_U` (the new U has S-free args), allowing IH application
  with strictly fewer U-subformulas.

### References

- GHR94, Lemmas 10.2.5-10.2.8, pp. 581-590
- Strategy report: specs/157_.../reports/09_hierarchy-strategy.md
-/

/-! ### Step 1: Substitution Preservation Lemmas -/

/-- Substituting an S-free formula into an S-free formula preserves S-freeness.
    This is needed when substituting `.untl A B` (with S-free A, B) for an atom
    in the S-free arguments of `.untl` nodes in a separated formula. -/
theorem subst_S_free_preserves_S_free (ψ : Formula Atom) (p : Atom) (r : Formula Atom)
    (hψ : is_S_free ψ = true) (hr : is_S_free r = true) :
    is_S_free (subst_formula ψ p r) = true := by
  induction ψ with
  | atom a =>
    simp only [subst_formula]
    split
    · exact hr
    · simp [is_S_free]
  | bot => simp [subst_formula, is_S_free]
  | imp c d ih1 ih2 =>
    simp [is_S_free] at hψ
    simp [subst_formula, is_S_free, ih1 hψ.1, ih2 hψ.2]
  | box c ih =>
    simp [is_S_free] at hψ
    simp [subst_formula, is_S_free, ih hψ]
  | untl c d ih1 ih2 =>
    simp [is_S_free] at hψ
    simp [subst_formula, is_S_free, ih1 hψ.1, ih2 hψ.2]
  | snce _ _ => simp [is_S_free] at hψ

/-- Substituting a U-free formula into a U-free formula preserves U-freeness.
    Dual of `subst_S_free_preserves_S_free`. -/
theorem subst_U_free_preserves_U_free (ψ : Formula Atom) (p : Atom) (r : Formula Atom)
    (hψ : is_U_free ψ = true) (hr : is_U_free r = true) :
    is_U_free (subst_formula ψ p r) = true := by
  induction ψ with
  | atom a =>
    simp only [subst_formula]
    split
    · exact hr
    · simp [is_U_free]
  | bot => simp [subst_formula, is_U_free]
  | imp c d ih1 ih2 =>
    simp [is_U_free] at hψ
    simp [subst_formula, is_U_free, ih1 hψ.1, ih2 hψ.2]
  | box c ih =>
    simp [is_U_free] at hψ
    simp [subst_formula, is_U_free, ih hψ]
  | untl _ _ => simp [is_U_free] at hψ
  | snce c d ih1 ih2 =>
    simp [is_U_free] at hψ
    simp [subst_formula, is_U_free, ih1 hψ.1, ih2 hψ.2]

/-- Substituting `.untl A B` (with S-free args) into a U-free formula gives
    `no_S_nested_in_U`. The only new `.untl` nodes are the substituted copies
    of `.untl A B`, which have S-free arguments by hypothesis. -/
theorem subst_U_free_gives_no_S_nested (ψ : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hψ : is_U_free ψ = true) (hA : is_S_free A = true) (hB : is_S_free B = true) :
    no_S_nested_in_U (subst_formula ψ p (.untl A B)) := by
  induction ψ with
  | atom a =>
    simp only [subst_formula]
    split
    · -- a = p: result is .untl A B, need is_S_free A ∧ is_S_free B
      exact ⟨hA, hB⟩
    · -- a ≠ p: result is .atom a
      trivial
  | bot => trivial
  | imp c d ih1 ih2 =>
    simp [is_U_free] at hψ
    exact ⟨ih1 hψ.1, ih2 hψ.2⟩
  | box c ih =>
    simp [is_U_free] at hψ
    exact ih hψ
  | untl _ _ => simp [is_U_free] at hψ
  | snce c d ih1 ih2 =>
    simp [is_U_free] at hψ
    exact ⟨ih1 hψ.1, ih2 hψ.2⟩

/-- Substituting has_no_allpast_allfuture preservation: if ψ has no allPast/allFuture
    and the replacement has none either, the result has none. -/
theorem subst_preserves_no_allpast_allfuture (ψ : Formula Atom) (p : Atom) (r : Formula Atom)
    (hψ : has_no_allpast_allfuture ψ = true) (hr : has_no_allpast_allfuture r = true) :
    has_no_allpast_allfuture (subst_formula ψ p r) = true := by
  induction ψ with
  | atom a =>
    simp only [subst_formula]
    split
    · exact hr
    · simp [has_no_allpast_allfuture]
  | bot => simp [subst_formula, has_no_allpast_allfuture]
  | imp c d ih1 ih2 =>
    simp [subst_formula, has_no_allpast_allfuture,
      ih1 (has_no_allpast_allfuture_true c), ih2 (has_no_allpast_allfuture_true d)]
  | box _ => simp [subst_formula, has_no_allpast_allfuture]
  | untl c d ih1 ih2 =>
    simp [subst_formula, has_no_allpast_allfuture,
      ih1 (has_no_allpast_allfuture_true c), ih2 (has_no_allpast_allfuture_true d)]
  | snce c d ih1 ih2 =>
    simp [subst_formula, has_no_allpast_allfuture,
      ih1 (has_no_allpast_allfuture_true c), ih2 (has_no_allpast_allfuture_true d)]

/-! ### Step 2: Strict Count Decrease for Abstraction -/

/-- Surface-level containment of `.untl A B`: the formula has a `.untl A B` node
    reachable from the root without passing through another `.untl` node.
    This mirrors the structure of `count_U_subformulas`, which counts `.untl` nodes
    at the surface level (not recursing into `.untl` children). -/
def contains_untl_surface : Formula Atom → Formula Atom → Formula Atom → Prop
  | .atom _, _, _ => False
  | .bot, _, _ => False
  | .imp c d, A, B => contains_untl_surface c A B ∨ contains_untl_surface d A B
  | .box c, A, B => contains_untl_surface c A B
  | .untl c d, A, B => c = A ∧ d = B
  | .snce c d, A, B => contains_untl_surface c A B ∨ contains_untl_surface d A B

/-- Abstracting a formula that contains `.untl A B` at the surface level strictly
    decreases count_U_subformulas. This is the corrected version of the count
    decrease lemma: the hypothesis `contains_untl_surface` ensures the non-matching
    `.untl` case is vacuously true (since `count_U_subformulas` does not recurse
    into `.untl` children). -/
theorem abstract_untl_count_lt_of_contains_surface (phi A B : Formula Atom) (p : Atom)
    (h_contains : contains_untl_surface phi A B) :
    count_U_subformulas (abstract_untl phi A B p) < count_U_subformulas phi := by
  induction phi with
  | atom _ => exact absurd h_contains id
  | bot => exact absurd h_contains id
  | imp c d ih1 ih2 =>
    simp only [contains_untl_surface] at h_contains
    simp only [abstract_untl, count_U_subformulas]
    rcases h_contains with hc | hd
    · have := ih1 hc; have := abstract_untl_count_le d A B p; omega
    · have := ih2 hd; have := abstract_untl_count_le c A B p; omega
  | box c ih =>
    simp only [contains_untl_surface] at h_contains
    simp only [abstract_untl, count_U_subformulas]; exact ih h_contains
  | untl c d _ _ =>
    simp only [abstract_untl, count_U_subformulas]
    split
    · simp only [count_U_subformulas]; omega
    · next hne =>
      -- h_contains : contains_untl_surface (.untl c d) A B = (c = A ∧ d = B)
      -- hne : ¬(c = A ∧ d = B), so this case is vacuously true
      exact absurd h_contains hne
  | snce c d ih1 ih2 =>
    simp only [contains_untl_surface] at h_contains
    simp only [abstract_untl, count_U_subformulas]
    rcases h_contains with hc | hd
    · have := ih1 hc; have := abstract_untl_count_le d A B p; omega
    · have := ih2 hd; have := abstract_untl_count_le c A B p; omega

/-! ### count_U_total lemmas for oracle-free separation -/

/-- `abstract_untl` never increases `count_U_total`. -/
theorem abstract_untl_count_total_le (phi A B : Formula Atom) (p : Atom) :
    count_U_total (abstract_untl phi A B p) ≤ count_U_total phi := by
  induction phi with
  | atom _ => simp [abstract_untl, count_U_total]
  | bot => simp [abstract_untl, count_U_total]
  | imp c d ih1 ih2 =>
    simp [abstract_untl, count_U_total]; exact Nat.add_le_add ih1 ih2
  | box c ih =>
    simp [abstract_untl, count_U_total]; exact ih
  | untl c d ih1 ih2 =>
    simp only [abstract_untl, count_U_total]
    split
    · simp [count_U_total]
    · simp only [count_U_total]; have := Nat.add_le_add ih1 ih2; omega
  | snce c d ih1 ih2 =>
    simp [abstract_untl, count_U_total]; exact Nat.add_le_add ih1 ih2

/-- `contains_untl_deep phi A B`: there exists an `.untl A B` node at any depth in phi. -/
def contains_untl_deep : Formula Atom → Formula Atom → Formula Atom → Prop
  | .atom _, _, _ => False
  | .bot, _, _ => False
  | .imp c d, A, B => contains_untl_deep c A B ∨ contains_untl_deep d A B
  | .box c, A, B => contains_untl_deep c A B
  | .untl c d, A, B => (c = A ∧ d = B) ∨
      contains_untl_deep c A B ∨ contains_untl_deep d A B
  | .snce c d, A, B => contains_untl_deep c A B ∨ contains_untl_deep d A B

/-- Surface containment implies deep containment. -/
theorem contains_untl_surface_implies_deep (phi A B : Formula Atom) :
    contains_untl_surface phi A B → contains_untl_deep phi A B := by
  induction phi with
  | atom _ => exact id
  | bot => exact id
  | imp c d ih1 ih2 =>
    simp only [contains_untl_surface, contains_untl_deep]
    intro h; rcases h with hc | hd
    · exact Or.inl (ih1 hc)
    · exact Or.inr (ih2 hd)
  | box c ih =>
    simp only [contains_untl_surface, contains_untl_deep]; exact ih
  | untl c d _ _ =>
    simp only [contains_untl_surface, contains_untl_deep]
    exact Or.inl
  | snce c d ih1 ih2 =>
    simp only [contains_untl_surface, contains_untl_deep]
    intro h; rcases h with hc | hd
    · exact Or.inl (ih1 hc)
    · exact Or.inr (ih2 hd)

/-- Abstracting a formula that contains `.untl A B` at any depth strictly
    decreases `count_U_total`. -/
theorem abstract_untl_count_total_lt_of_contains_deep (phi A B : Formula Atom) (p : Atom)
    (h_contains : contains_untl_deep phi A B) :
    count_U_total (abstract_untl phi A B p) < count_U_total phi := by
  induction phi with
  | atom _ => exact absurd h_contains id
  | bot => exact absurd h_contains id
  | imp c d ih1 ih2 =>
    simp only [contains_untl_deep] at h_contains
    simp only [abstract_untl, count_U_total]
    rcases h_contains with hc | hd
    · have := ih1 hc; have := abstract_untl_count_total_le d A B p; omega
    · have := ih2 hd; have := abstract_untl_count_total_le c A B p; omega
  | box c ih =>
    simp only [contains_untl_deep] at h_contains
    simp only [abstract_untl, count_U_total]; exact ih h_contains
  | untl c d ih1 ih2 =>
    simp only [contains_untl_deep] at h_contains
    simp only [abstract_untl, count_U_total]
    split
    · simp only [count_U_total]; omega
    · next hne =>
      simp only [count_U_total]
      rcases h_contains with ⟨hc, hd⟩ | hc | hd
      · exact absurd ⟨hc, hd⟩ hne
      · have := ih1 hc; have := abstract_untl_count_total_le d A B p; omega
      · have := ih2 hd; have := abstract_untl_count_total_le c A B p; omega
  | snce c d ih1 ih2 =>
    simp only [contains_untl_deep] at h_contains
    simp only [abstract_untl, count_U_total]
    rcases h_contains with hc | hd
    · have := ih1 hc; have := abstract_untl_count_total_le d A B p; omega
    · have := ih2 hd; have := abstract_untl_count_total_le c A B p; omega

/-- S-free formulas have no_S_nested_in_U (vacuously: no `.snce` nodes at all). -/
theorem s_free_implies_no_S_nested (phi : Formula Atom) (h : is_S_free phi = true) :
    no_S_nested_in_U phi := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 =>
    simp only [is_S_free, Bool.and_eq_true] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box a ih => simp only [is_S_free] at h; exact ih h
  | untl a b =>
    simp only [is_S_free, Bool.and_eq_true] at h
    exact h
  | snce _ _ => simp [is_S_free] at h

/-- Extract innermost U-type: recurses INTO `.untl` children to find a `.untl`
    with U-free arguments. Unlike `extract_U_type` which takes the first `.untl`
    it finds, this descends into `.untl` children when they're not U-free. -/
noncomputable def extract_innermost_U_type :
    (φ : Formula Atom) → (is_U_free φ = false) → no_S_nested_in_U φ → (Formula Atom × Formula Atom)
  | .atom _, h, _ => by simp [is_U_free] at h
  | .bot, h, _ => by simp [is_U_free] at h
  | .imp c d, h, hns =>
    if hc : is_U_free c = false then extract_innermost_U_type c hc hns.1
    else extract_innermost_U_type d (by simp only [is_U_free] at h; simp [hc] at h; exact h) hns.2
  | .box c, h, hns => extract_innermost_U_type c (by simp only [is_U_free] at h; exact h) hns
  | .untl a b, _, hns =>
    -- Key difference from extract_U_type: recurse into children if they're not U-free
    if ha : is_U_free a = false then
      extract_innermost_U_type a ha (s_free_implies_no_S_nested a hns.1)
    else if hb : is_U_free b = false then
      extract_innermost_U_type b hb (s_free_implies_no_S_nested b hns.2)
    else (a, b)  -- Both U-free: this is an innermost U-type
  | .snce c d, h, hns =>
    if hc : is_U_free c = false then extract_innermost_U_type c hc hns.1
    else extract_innermost_U_type d (by simp only [is_U_free] at h; simp [hc] at h; exact h) hns.2

/-- `extract_innermost_U_type` returns S-free arguments. -/
theorem extract_innermost_U_type_S_free (φ : Formula Atom) (h : is_U_free φ = false)
    (hns : no_S_nested_in_U φ) :
    is_S_free (extract_innermost_U_type φ h hns).1 = true ∧
    is_S_free (extract_innermost_U_type φ h hns).2 = true := by
  induction φ with
  | atom _ => simp [is_U_free] at h
  | bot => simp [is_U_free] at h
  | imp c d ih1 ih2 =>
    unfold extract_innermost_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte]; exact ih1 hc hns.1
    · simp only [hc, ↓reduceDIte]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      exact ih2 hd hns.2
  | box c ih => simp only [is_U_free] at h; unfold extract_innermost_U_type; exact ih h hns
  | untl a b ih1 ih2 =>
    unfold extract_innermost_U_type
    by_cases ha : is_U_free a = false
    · simp only [ha, ↓reduceDIte]
      exact ih1 ha (s_free_implies_no_S_nested a hns.1)
    · simp only [ha, ↓reduceDIte]
      by_cases hb : is_U_free b = false
      · simp only [hb, ↓reduceDIte]
        exact ih2 hb (s_free_implies_no_S_nested b hns.2)
      · simp only [hb, ↓reduceDIte]; exact hns
  | snce c d ih1 ih2 =>
    unfold extract_innermost_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte]; exact ih1 hc hns.1
    · simp only [hc, ↓reduceDIte]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      exact ih2 hd hns.2

/-- `extract_innermost_U_type` returns U-free arguments (KEY property).
    At the innermost level, both arguments are U-free by construction. -/
theorem extract_innermost_U_type_U_free (φ : Formula Atom) (h : is_U_free φ = false)
    (hns : no_S_nested_in_U φ) :
    is_U_free (extract_innermost_U_type φ h hns).1 = true ∧
    is_U_free (extract_innermost_U_type φ h hns).2 = true := by
  induction φ with
  | atom _ => simp [is_U_free] at h
  | bot => simp [is_U_free] at h
  | imp c d ih1 ih2 =>
    unfold extract_innermost_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte]; exact ih1 hc hns.1
    · simp only [hc, ↓reduceDIte]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      exact ih2 hd hns.2
  | box c ih => simp only [is_U_free] at h; unfold extract_innermost_U_type; exact ih h hns
  | untl a b ih1 ih2 =>
    unfold extract_innermost_U_type
    by_cases ha : is_U_free a = false
    · simp only [ha, ↓reduceDIte]
      exact ih1 ha (s_free_implies_no_S_nested a hns.1)
    · simp only [ha, ↓reduceDIte]
      by_cases hb : is_U_free b = false
      · simp only [hb, ↓reduceDIte]
        exact ih2 hb (s_free_implies_no_S_nested b hns.2)
      · -- Both U-free: this is the innermost case
        simp only [hb, ↓reduceDIte]
        have ha_true : is_U_free a = true := by
          cases h : is_U_free a <;> simp_all
        have hb_true : is_U_free b = true := by
          cases h : is_U_free b <;> simp_all
        exact ⟨ha_true, hb_true⟩
  | snce c d ih1 ih2 =>
    unfold extract_innermost_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte]; exact ih1 hc hns.1
    · simp only [hc, ↓reduceDIte]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      exact ih2 hd hns.2

/-- `extract_innermost_U_type` returns a pair `(A, B)` such that
    `contains_untl_deep φ A B`. -/
theorem extract_innermost_U_type_contains_deep (φ : Formula Atom) (h : is_U_free φ = false)
    (hns : no_S_nested_in_U φ) :
    contains_untl_deep φ
      (extract_innermost_U_type φ h hns).1 (extract_innermost_U_type φ h hns).2 := by
  induction φ with
  | atom _ => simp [is_U_free] at h
  | bot => simp [is_U_free] at h
  | imp c d ih1 ih2 =>
    unfold extract_innermost_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte, contains_untl_deep]
      exact Or.inl (ih1 hc hns.1)
    · simp only [hc, ↓reduceDIte, contains_untl_deep]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      exact Or.inr (ih2 hd hns.2)
  | box c ih =>
    simp only [is_U_free] at h
    unfold extract_innermost_U_type; simp only [contains_untl_deep]; exact ih h hns
  | untl a b ih1 ih2 =>
    unfold extract_innermost_U_type
    by_cases ha : is_U_free a = false
    · simp only [ha, ↓reduceDIte, contains_untl_deep]
      exact Or.inr (Or.inl (ih1 ha (s_free_implies_no_S_nested a hns.1)))
    · simp only [ha, ↓reduceDIte]
      by_cases hb : is_U_free b = false
      · simp only [hb, ↓reduceDIte, contains_untl_deep]
        exact Or.inr (Or.inr (ih2 hb (s_free_implies_no_S_nested b hns.2)))
      · simp only [hb, ↓reduceDIte, contains_untl_deep]
        exact Or.inl ⟨rfl, rfl⟩
  | snce c d ih1 ih2 =>
    unfold extract_innermost_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte, contains_untl_deep]
      exact Or.inl (ih1 hc hns.1)
    · simp only [hc, ↓reduceDIte, contains_untl_deep]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      exact Or.inr (ih2 hd hns.2)

/-- abstract_untl preserves has_no_allpast_allfuture. -/
theorem abstract_untl_preserves_no_allpast_allfuture (phi A B : Formula Atom) (p : Atom)
    (h : has_no_allpast_allfuture phi = true) :
    has_no_allpast_allfuture (abstract_untl phi A B p) = true := by
  induction phi with
  | atom _ => simp [abstract_untl, has_no_allpast_allfuture]
  | bot => simp [abstract_untl, has_no_allpast_allfuture]
  | imp c d ih1 ih2 =>
    simp [abstract_untl, has_no_allpast_allfuture,
      ih1 (has_no_allpast_allfuture_true c), ih2 (has_no_allpast_allfuture_true d)]
  | box _ => simp [abstract_untl, has_no_allpast_allfuture]
  | untl c d ih1 ih2 =>
    simp only [abstract_untl]
    split
    · simp [has_no_allpast_allfuture]
    · simp [has_no_allpast_allfuture,
        ih1 (has_no_allpast_allfuture_true c), ih2 (has_no_allpast_allfuture_true d)]
  | snce c d ih1 ih2 =>
    simp [abstract_untl, has_no_allpast_allfuture,
      ih1 (has_no_allpast_allfuture_true c), ih2 (has_no_allpast_allfuture_true d)]

/-! ### Step 3: Substitution into Separated Formulas

The "constituent substitution" technique from GHR94 Lemma 10.2.6.
Given a separated formula ψ, substituting `.untl A B` (with S-free A, B)
for atom p yields a separable formula, provided we have a callback
for handling the `.snce` and `.allPast` constituents. -/

/-- Substituting `.untl A B` (S-free args) for atom p in a separated formula
    produces a separable formula, using `ih_snce` for constituents where
    substitution breaks separation (`.snce` and `.allPast` positions). -/
theorem subst_in_separated_separable (ψ : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hsep : is_syntactically_separated ψ = true)
    (ih_snce : ∀ (χ : Formula Atom), no_S_nested_in_U χ → is_separable χ) :
    is_separable (subst_formula ψ p (.untl A B)) := by
  induction ψ with
  | atom a =>
    simp only [subst_formula]; split
    · exact ⟨.untl A B, by simp [is_syntactically_separated, hA_sf, hB_sf], int_equiv_refl _⟩
    · exact ⟨.atom a, rfl, int_equiv_refl _⟩
  | bot => exact ⟨.bot, rfl, int_equiv_refl _⟩
  | box ψ => exact ⟨.box (subst_formula ψ p (.untl A B)), rfl, int_equiv_refl _⟩
  | imp c d ih_c ih_d =>
    simp [is_syntactically_separated] at hsep
    exact imp_separable (ih_c hsep.1) (ih_d hsep.2)
  | untl c d _ _ =>
    simp [is_syntactically_separated] at hsep
    have hU_sf : is_S_free (.untl A B) = true := by
      simp only [is_S_free, hA_sf, hB_sf, Bool.and_self]
    exact ⟨.untl (subst_formula c p (.untl A B)) (subst_formula d p (.untl A B)),
           by simp [is_syntactically_separated,
                     subst_S_free_preserves_S_free c p _ hsep.1 hU_sf,
                     subst_S_free_preserves_S_free d p _ hsep.2 hU_sf],
           int_equiv_refl _⟩
  | snce c d _ _ =>
    simp [is_syntactically_separated] at hsep
    exact ih_snce (.snce (subst_formula c p (.untl A B)) (subst_formula d p (.untl A B)))
      ⟨subst_U_free_gives_no_S_nested c p A B hsep.1 hA_sf hB_sf,
       subst_U_free_gives_no_S_nested d p A B hsep.2 hA_sf hB_sf⟩

/-! ### Step 4: Additional Infrastructure

Substitution congruence and helper lemmas for the hierarchy theorem. -/

/-- Substitution preserves int_equiv: if φ ≡ ψ then subst(φ, p, r) ≡ subst(ψ, p, r). -/
theorem subst_formula_congr {φ ψ : Formula Atom} (h : int_equiv φ ψ)
    (p : Atom) (r : Formula Atom) :
    int_equiv (subst_formula φ p r) (subst_formula ψ p r) := by
  intro M t; rw [subst_correctness, subst_correctness]; exact h _ t

/-- Helper: `.untl` with S-free args is already separated. -/
private theorem untl_sf_exp_separated (a b : Formula Atom)
    (ha_sf : is_S_free a = true) (hb_sf : is_S_free b = true) :
    is_separable (.untl a b) :=
  ⟨.untl a b, by simp [is_syntactically_separated, ha_sf, hb_sf], int_equiv_refl _⟩

/-- Helper: `.snce` with U-free args is already separated. -/
private theorem snce_uf_separated (a b : Formula Atom)
    (ha_uf : is_U_free a = true) (hb_uf : is_U_free b = true) :
    is_separable (.snce a b) :=
  ⟨.snce a b, by simp [is_syntactically_separated, ha_uf, hb_uf], int_equiv_refl _⟩

/-- Extract a U-type (A, B) with S-free args from a non-U-free formula
    that has `no_S_nested_in_U`. -/
noncomputable def extract_U_type : (φ : Formula Atom) → (is_U_free φ = false) →
    no_S_nested_in_U φ → (Formula Atom × Formula Atom)
  | .atom _, h, _ => by simp [is_U_free] at h
  | .bot, h, _ => by simp [is_U_free] at h
  | .imp c d, h, hns =>
    if hc : is_U_free c = false then extract_U_type c hc hns.1
    else extract_U_type d (by simp only [is_U_free] at h; simp [hc] at h; exact h) hns.2
  | .box c, h, hns => extract_U_type c (by simp only [is_U_free] at h; exact h) hns
  | .untl a b, _, _ => (a, b)
  | .snce c d, h, hns =>
    if hc : is_U_free c = false then extract_U_type c hc hns.1
    else extract_U_type d (by simp only [is_U_free] at h; simp [hc] at h; exact h) hns.2

theorem extract_U_type_S_free (φ : Formula Atom) (h : is_U_free φ = false)
    (hns : no_S_nested_in_U φ) :
    is_S_free (extract_U_type φ h hns).1 = true ∧
    is_S_free (extract_U_type φ h hns).2 = true := by
  induction φ with
  | atom _ => simp [is_U_free] at h
  | bot => simp [is_U_free] at h
  | imp c d ih1 ih2 =>
    unfold extract_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte]; exact ih1 hc hns.1
    · simp only [hc, ↓reduceDIte]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      exact ih2 hd hns.2
  | box c ih => simp only [is_U_free] at h; unfold extract_U_type; exact ih h hns
  | untl a b => exact hns
  | snce c d ih1 ih2 =>
    unfold extract_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte]; exact ih1 hc hns.1
    · simp only [hc, ↓reduceDIte]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      exact ih2 hd hns.2

/-- `extract_U_type` returns a pair `(A, B)` such that `contains_untl_surface φ A B`.
    This is the bridge between `extract_U_type` (which finds the first `.untl` by
    descending through `imp`, `box`, `snce`) and the count decrease lemma
    `abstract_untl_count_lt_of_contains_surface`. -/
theorem extract_U_type_contains_surface (φ : Formula Atom) (h : is_U_free φ = false)
    (hns : no_S_nested_in_U φ) :
    contains_untl_surface φ (extract_U_type φ h hns).1 (extract_U_type φ h hns).2 := by
  induction φ with
  | atom _ => simp [is_U_free] at h
  | bot => simp [is_U_free] at h
  | imp c d ih1 ih2 =>
    unfold extract_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte, contains_untl_surface]
      exact Or.inl (ih1 hc hns.1)
    · simp only [hc, contains_untl_surface]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      exact Or.inr (ih2 hd hns.2)
  | box c ih =>
    simp only [is_U_free] at h
    unfold extract_U_type; simp only [contains_untl_surface]; exact ih h hns
  | untl a b =>
    unfold extract_U_type; exact ⟨rfl, rfl⟩
  | snce c d ih1 ih2 =>
    unfold extract_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte, contains_untl_surface]
      exact Or.inl (ih1 hc hns.1)
    · simp only [hc, contains_untl_surface]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      exact Or.inr (ih2 hd hns.2)

/-! ### Step 5: S-Nesting Depth Measure for Lemma 10.2.5

GHR94 Lemma 10.2.5 proves that a formula with a single U-type U(A,B) (A, B S-free)
is separable by induction on the maximum number of `.snce` nodes above any `.untl`
in the formula tree. We define a non-mutual version of this measure and prove
the key properties needed for the well-founded induction. -/

/-- Maximum number of `.snce` ancestors above any `.untl` node in the formula tree.
    Returns 0 if the formula is U-free. For `.snce C F`, adds 1 if U appears below.
    Non-mutual version of `S_nesting_above_U` for easier theorem proving. -/
def snce_depth_of_U : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp a b => max (snce_depth_of_U a) (snce_depth_of_U b)
  | .box a => snce_depth_of_U a
  | .untl _ _ => 0
  | .snce a b =>
    if is_U_free a = true ∧ is_U_free b = true then 0
    else 1 + max (snce_depth_of_U a) (snce_depth_of_U b)

/-- U-free formulas have snce_depth_of_U = 0. -/
theorem snce_depth_of_U_zero_of_U_free (phi : Formula Atom)
    (h : is_U_free phi = true) : snce_depth_of_U phi = 0 := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_U_free] at h
    simp [snce_depth_of_U, ih1 h.1, ih2 h.2]
  | box a ih => simp [is_U_free] at h; simp [snce_depth_of_U, ih h]
  | untl _ _ => simp [is_U_free] at h
  | snce a b ih1 ih2 =>
    simp [is_U_free] at h
    simp [snce_depth_of_U, h.1, h.2]

/-- Key property: for `.snce C F` where C or F is not U-free,
    `snce_depth_of_U C < snce_depth_of_U (.snce C F)` and similarly for F. -/
theorem snce_depth_of_U_lt_snce (C w : Formula Atom)
    (h : ¬(is_U_free C = true ∧ is_U_free w = true)) :
    snce_depth_of_U C < snce_depth_of_U (.snce C w) ∧
    snce_depth_of_U w < snce_depth_of_U (.snce C w) := by
  simp [snce_depth_of_U, h]
  constructor <;> omega

/-- snce_depth_of_U is monotone for imp subterms. -/
theorem snce_depth_of_U_le_imp_left (a b : Formula Atom) :
    snce_depth_of_U a ≤ snce_depth_of_U (.imp a b) :=
  Nat.le_max_left _ _

theorem snce_depth_of_U_le_imp_right (a b : Formula Atom) :
    snce_depth_of_U b ≤ snce_depth_of_U (.imp a b) :=
  Nat.le_max_right _ _

/-- snce_depth_of_U passes through box unchanged. -/
theorem snce_depth_of_U_le_box (a : Formula Atom) :
    snce_depth_of_U a ≤ snce_depth_of_U (.box a) :=
  Nat.le_refl _

/-- For `.snce a b` where not both U-free, left arg has strictly smaller depth. -/
theorem snce_depth_of_U_le_snce_left (a b : Formula Atom)
    (h : ¬(is_U_free a = true ∧ is_U_free b = true)) :
    snce_depth_of_U a ≤ snce_depth_of_U (.snce a b) := by
  simp [snce_depth_of_U, h]; omega

/-- For `.snce a b` where not both U-free, right arg has strictly smaller depth. -/
theorem snce_depth_of_U_le_snce_right (a b : Formula Atom)
    (h : ¬(is_U_free a = true ∧ is_U_free b = true)) :
    snce_depth_of_U b ≤ snce_depth_of_U (.snce a b) := by
  simp [snce_depth_of_U, h]; omega

/-! ### Step 5b′: Base Case — snce_depth_of_U = 0 with no_S_nested_in_U

When `snce_depth_of_U phi = 0` and `no_S_nested_in_U phi`, the formula is
syntactically separated (hence separable). This generalizes
`snce_depth_zero_single_U_separated` by dropping the single-U-type and
has_no_allpast_allfuture requirements.

The argument:
- `snce_depth_of_U = 0`: every `.snce a b` has `is_U_free a ∧ is_U_free b`
  (the else branch adds 1, so depth 0 forces the if-branch at every `.snce`)
- `no_S_nested_in_U`: every `.untl a b` has `is_S_free a ∧ is_S_free b`
- Together these imply `is_syntactically_separated phi = true`. -/

/-- Base case for GHR94 10.2.7: snce_depth_of_U = 0 with no_S_nested_in_U
    implies syntactically separated, hence separable. -/
theorem snce_depth_zero_no_S_nested_separated (phi : Formula Atom)
    (hns : no_S_nested_in_U phi)
    (hd : snce_depth_of_U phi = 0) :
    is_separable phi := by
  suffices h : is_syntactically_separated phi = true from
    separated_imp_separable phi h
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [snce_depth_of_U] at hd
    simp [no_S_nested_in_U] at hns
    simp [is_syntactically_separated, ih1 hns.1 (by omega), ih2 hns.2 (by omega)]
  | box a ih =>
    simp [is_syntactically_separated]
  | untl a b _ _ =>
    simp [no_S_nested_in_U] at hns
    simp [is_syntactically_separated, hns.1, hns.2]
  | snce a b _ _ =>
    simp [snce_depth_of_U] at hd
    simp [is_syntactically_separated, hd.1, hd.2]

/-! ### Step 5b: Base Case — snce_depth_of_U = 0 with single U-type

When snce_depth_of_U phi = 0 and phi has single U-type U(A,B) with S-free A, B
and has_no_allpast_allfuture, then phi is syntactically separated.

This means: every `.snce` in phi has U-free args, and every `.untl` is U(A,B)
with S-free args. So `.untl` positions have S-free args and `.snce` positions
have U-free args. -/

/-- When snce_depth_of_U = 0 and has_single_U_type, every `.snce` subformula
    has U-free args, so the formula is syntactically separated
    (given has_no_allpast_allfuture). -/
theorem snce_depth_zero_single_U_separated (phi A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hsingle : has_single_U_type phi A B)
    (hexp : has_no_allpast_allfuture phi = true)
    (hdepth : snce_depth_of_U phi = 0) :
    is_syntactically_separated phi = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [snce_depth_of_U] at hdepth
    simp [is_syntactically_separated,
      ih1 hsingle.1 (has_no_allpast_allfuture_true a) (by omega),
      ih2 hsingle.2 (has_no_allpast_allfuture_true b) (by omega)]
  | box _ => rfl
  | untl a b _ _ =>
    have ⟨ha, hb⟩ := hsingle; subst ha; subst hb
    simp [is_syntactically_separated, hA_sf, hB_sf]
  | snce a b _ _ =>
    simp [snce_depth_of_U] at hdepth
    obtain ⟨ha_uf, hb_uf⟩ := hdepth
    simp [is_syntactically_separated, ha_uf, hb_uf]

/-! ### U-Nesting Depth Measure for Lemma 10.2.7

GHR94 Lemma 10.2.7 inducts on the maximum depth of U-nesting chains
(the "maximum depth n of nesting of Us beneath an S"). This is different
from `snce_depth_of_U` (which counts S-layers above U and stops at `.untl`
nodes). `U_nesting_depth` counts `.untl` nesting levels throughout the
formula, passing through `.snce` transparently. -/

/-- Maximum depth of U-nesting chains in a formula.
    Counts how many levels of `.untl` are nested (through U-args).
    `.snce` passes through (takes max), `.untl` increments by 1.
    This is GHR94's "depth of nesting of Us beneath an S" for 10.2.7. -/
def U_nesting_depth : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp a b => max (U_nesting_depth a) (U_nesting_depth b)
  | .box a => U_nesting_depth a
  | .untl a b => 1 + max (U_nesting_depth a) (U_nesting_depth b)
  | .snce a b => max (U_nesting_depth a) (U_nesting_depth b)

/-- U_nesting_depth = 0 iff the formula is U-free. -/
theorem U_nesting_depth_zero_iff_U_free (phi : Formula Atom) :
    U_nesting_depth phi = 0 ↔ is_U_free phi = true := by
  induction phi with
  | atom _ => simp only [U_nesting_depth, is_U_free]
  | bot => simp only [U_nesting_depth, is_U_free]
  | imp a b ih1 ih2 =>
    simp only [U_nesting_depth, is_U_free, Nat.max_eq_zero_iff, Bool.and_eq_true, ih1, ih2]
  | box a ih =>
    simp only [U_nesting_depth, is_U_free]
    exact ih
  | untl _ _ _ _ =>
    simp only [U_nesting_depth, is_U_free]
    exact iff_of_false (by omega) (by decide)
  | snce a b ih1 ih2 =>
    simp only [U_nesting_depth, is_U_free, Nat.max_eq_zero_iff, Bool.and_eq_true, ih1, ih2]

/-- U-free formulas have U_nesting_depth = 0. -/
theorem U_nesting_depth_zero_of_U_free (phi : Formula Atom)
    (h : is_U_free phi = true) : U_nesting_depth phi = 0 :=
  (U_nesting_depth_zero_iff_U_free phi).mpr h

/-- When U_nesting_depth <= 1 and no_S_nested_in_U, all U-args are U-free.
    This is the key property: at depth <= 1, U-args are boolean (U-free AND S-free). -/
theorem U_nesting_depth_le_one_untl_args_U_free (a b : Formula Atom)
    (h : U_nesting_depth (.untl a b) ≤ 1) :
    is_U_free a = true ∧ is_U_free b = true := by
  simp only [U_nesting_depth] at h
  have ha : U_nesting_depth a = 0 := by omega
  have hb : U_nesting_depth b = 0 := by omega
  exact ⟨(U_nesting_depth_zero_iff_U_free a).mp ha,
         (U_nesting_depth_zero_iff_U_free b).mp hb⟩

-- Monotonicity lemmas

theorem U_nesting_depth_le_imp_left (a b : Formula Atom) :
    U_nesting_depth a ≤ U_nesting_depth (.imp a b) := by
  simp only [U_nesting_depth]
  exact Nat.le_max_left _ _

theorem U_nesting_depth_le_imp_right (a b : Formula Atom) :
    U_nesting_depth b ≤ U_nesting_depth (.imp a b) := by
  simp only [U_nesting_depth]
  exact Nat.le_max_right _ _

theorem U_nesting_depth_le_box (a : Formula Atom) :
    U_nesting_depth a ≤ U_nesting_depth (.box a) := by
  simp only [U_nesting_depth, le_refl]

theorem U_nesting_depth_le_snce_left (a b : Formula Atom) :
    U_nesting_depth a ≤ U_nesting_depth (.snce a b) := by
  simp only [U_nesting_depth]
  exact Nat.le_max_left _ _

theorem U_nesting_depth_le_snce_right (a b : Formula Atom) :
    U_nesting_depth b ≤ U_nesting_depth (.snce a b) := by
  simp only [U_nesting_depth]
  exact Nat.le_max_right _ _

theorem U_nesting_depth_lt_untl_left (a b : Formula Atom) :
    U_nesting_depth a < U_nesting_depth (.untl a b) := by
  simp only [U_nesting_depth]
  omega

theorem U_nesting_depth_lt_untl_right (a b : Formula Atom) :
    U_nesting_depth b < U_nesting_depth (.untl a b) := by
  simp only [U_nesting_depth]
  omega

/-- abstract_untl does not increase U_nesting_depth.
    Replacing `.untl A B` with `.atom p` can only decrease or maintain the depth. -/
theorem abstract_untl_U_nesting_depth_le (phi A B : Formula Atom) (p : Atom) :
    U_nesting_depth (abstract_untl phi A B p) ≤ U_nesting_depth phi := by
  induction phi with
  | atom _ => simp [abstract_untl, U_nesting_depth]
  | bot => simp [abstract_untl, U_nesting_depth]
  | imp c d ih1 ih2 =>
    simp only [abstract_untl, U_nesting_depth]; omega
  | box c ih =>
    simp only [abstract_untl, U_nesting_depth]; exact ih
  | untl c d ih1 ih2 =>
    simp only [abstract_untl]
    split
    · simp only [U_nesting_depth]; omega
    · simp only [U_nesting_depth]; omega
  | snce c d ih1 ih2 =>
    simp only [abstract_untl, U_nesting_depth]; omega

/-- Corollary: abstract_untl preserves the U_nesting_depth <= k bound. -/
theorem abstract_untl_U_nesting_depth_le_of_le (phi A B : Formula Atom) (p : Atom) (k : Nat)
    (h : U_nesting_depth phi ≤ k) :
    U_nesting_depth (abstract_untl phi A B p) ≤ k :=
  Nat.le_trans (abstract_untl_U_nesting_depth_le phi A B p) h

/-! ### Callback Single-U-Type Infrastructure (Task 3.4)

Substituting U(A,B) (with U-free A, B) for an atom in a U-free formula yields
a formula with single U-type U(A,B). This is the key property enabling the
self-contained depth-1 case in Lemma 10.2.5 (axiom-free). -/

/-- Substituting U(A,B) (with U-free A, B) for an atom in a U-free formula
    yields a formula with single U-type U(A,B). -/
theorem subst_U_free_gives_single_U_type (c : Formula Atom) (p : Atom)
    (A B : Formula Atom)
    (hc_U_free : is_U_free c = true)
    (hA_U_free : is_U_free A = true)
    (hB_U_free : is_U_free B = true) :
    has_single_U_type (subst_formula c p (.untl A B)) A B := by
  induction c with
  | atom a =>
    simp only [subst_formula]
    split
    · -- a = p: result is .untl A B
      exact ⟨rfl, rfl⟩
    · -- a ≠ p: result is .atom a
      trivial
  | bot => simp only [subst_formula, has_single_U_type]
  | imp c d ih1 ih2 =>
    simp only [is_U_free, Bool.and_eq_true] at hc_U_free
    simp only [subst_formula, has_single_U_type]
    exact ⟨ih1 hc_U_free.1, ih2 hc_U_free.2⟩
  | box c ih =>
    simp only [is_U_free] at hc_U_free
    simp only [subst_formula, has_single_U_type]
    exact ih hc_U_free
  | untl _ _ => simp only [is_U_free, Bool.false_eq_true] at hc_U_free
  | snce c d ih1 ih2 =>
    simp only [is_U_free, Bool.and_eq_true] at hc_U_free
    simp only [subst_formula, has_single_U_type]
    exact ⟨ih1 hc_U_free.1, ih2 hc_U_free.2⟩

/-- Callback formulas from subst_in_separated_separable have single U-type
    when the separated formula's snce-args are U-free (which they are by
    definition of is_syntactically_separated). -/
theorem callback_has_single_U_type (c d : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hc_U_free : is_U_free c = true) (hd_U_free : is_U_free d = true)
    (hA_U_free : is_U_free A = true) (hB_U_free : is_U_free B = true) :
    has_single_U_type (.snce (subst_formula c p (.untl A B))
                             (subst_formula d p (.untl A B))) A B :=
  ⟨subst_U_free_gives_single_U_type c p A B hc_U_free hA_U_free hB_U_free,
   subst_U_free_gives_single_U_type d p A B hd_U_free hA_U_free hB_U_free⟩

/-- Version of `subst_in_separated_separable` where the callback also receives
    `has_single_U_type chi A B`. This enables the callback to use
    `single_U_formula_separable_noax` which requires single-U-type.
    Used by `lemma_10_2_6_self_contained` for the axiom-free depth-1 case. -/
theorem subst_in_separated_separable_typed (ψ : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (hsep : is_syntactically_separated ψ = true)
    (ih_snce : ∀ (χ : Formula Atom), no_S_nested_in_U χ →
        has_single_U_type χ A B → is_separable χ) :
    is_separable (subst_formula ψ p (.untl A B)) := by
  induction ψ with
  | atom a =>
    simp only [subst_formula]; split
    · exact ⟨.untl A B, by simp [is_syntactically_separated, hA_sf, hB_sf], int_equiv_refl _⟩
    · exact ⟨.atom a, rfl, int_equiv_refl _⟩
  | bot => exact ⟨.bot, rfl, int_equiv_refl _⟩
  | box ψ => exact ⟨.box (subst_formula ψ p (.untl A B)), rfl, int_equiv_refl _⟩
  | imp c d ih_c ih_d =>
    simp [is_syntactically_separated] at hsep
    exact imp_separable (ih_c hsep.1) (ih_d hsep.2)
  | untl c d _ _ =>
    simp [is_syntactically_separated] at hsep
    have hU_sf : is_S_free (.untl A B) = true := by
      simp only [is_S_free, hA_sf, hB_sf, Bool.and_self]
    exact ⟨.untl (subst_formula c p (.untl A B)) (subst_formula d p (.untl A B)),
           by simp [is_syntactically_separated,
                     subst_S_free_preserves_S_free c p _ hsep.1 hU_sf,
                     subst_S_free_preserves_S_free d p _ hsep.2 hU_sf],
           int_equiv_refl _⟩
  | snce c d _ _ =>
    simp [is_syntactically_separated] at hsep
    have hns : no_S_nested_in_U (.snce (subst_formula c p (.untl A B))
        (subst_formula d p (.untl A B))) :=
      ⟨subst_U_free_gives_no_S_nested c p A B hsep.1 hA_sf hB_sf,
       subst_U_free_gives_no_S_nested d p A B hsep.2 hA_sf hB_sf⟩
    have hsingle : has_single_U_type (.snce (subst_formula c p (.untl A B))
        (subst_formula d p (.untl A B))) A B :=
      callback_has_single_U_type c d p A B hsep.1 hsep.2 hA_uf hB_uf
    exact ih_snce _ hns hsingle

/-! ### Syntactically Separated implies snce_depth_of_U = 0 (Task 3.5)

A syntactically separated formula has snce_depth_of_U = 0. This is the KEY
bridge lemma for single_U_formula_separable_noax: when the IH produces
separated C' and F', this lemma gives snce_depth_of_U C' = 0 and
snce_depth_of_U F' = 0, so .snce C' F' has depth exactly 1. -/

/-- After box-normalization, a syntactically separated formula has snce_depth_of_U = 0.
    The raw theorem without box-normalization fails because is_syntactically_separated
    treats .box as atomic while snce_depth_of_U passes through it. But after
    replace_box_with_top, all .box nodes become .imp .bot .bot (which has depth 0),
    so the induction goes through.

    This is the KEY bridge lemma for single_U_formula_separable_noax: when the IH
    produces separated C' and F', applying replace_box_with_top gives C'' and F''
    with snce_depth_of_U = 0, so .snce C'' F'' has depth exactly 1. -/
theorem separated_boxnorm_snce_depth_zero (phi : Formula Atom)
    (hsep : is_syntactically_separated phi = true) :
    snce_depth_of_U (replace_box_with_top phi) = 0 := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp only [is_syntactically_separated, Bool.and_eq_true] at hsep
    simp only [replace_box_with_top, snce_depth_of_U, ih1 hsep.1, ih2 hsep.2, Nat.max_self]
  | box _ =>
    simp only [replace_box_with_top, snce_depth_of_U, Nat.max_self]
  | untl _ _ =>
    simp only [replace_box_with_top, snce_depth_of_U]
  | snce a b _ _ =>
    simp only [is_syntactically_separated, Bool.and_eq_true] at hsep
    have ha_uf := replace_box_preserves_U_free a hsep.1
    have hb_uf := replace_box_preserves_U_free b hsep.2
    simp only [replace_box_with_top, snce_depth_of_U, ha_uf, hb_uf, and_self, ↓reduceIte]

/-! ### Step 5c: Single-U-Type at Depth 0 — Direct Separability via Event-Guard Decomposition

GHR94 Lemma 10.2.4: `.snce C F` where U(A,B) appears only at top level (not under
any S within C or F) is separable. The proof decomposes into Cases 1-8 using:
1. Event-splitting on U(A,B)
2. CNF decomposition of the guard
3. Generalized Cases 1-8 (no S-free requirement on a, q)

Key technique: `C ∧ U(A,B) ≡ C[U:=⊤] ∧ U(A,B)` where C[U:=⊤] is U-free. -/

/-- Replace all `.untl A B` with a constant formula `r` in `C`.
    Simpler than abstract_untl + subst: directly replaces at formula level. -/
def replace_untl (C A B r : Formula Atom) : Formula Atom :=
  match C with
  | .atom a => .atom a
  | .bot => .bot
  | .imp c d => .imp (replace_untl c A B r) (replace_untl d A B r)
  | .box c => .box (replace_untl c A B r)
  | .untl c d => if c = A ∧ d = B then r else .untl (replace_untl c A B r) (replace_untl d A B r)
  | .snce c d => .snce (replace_untl c A B r) (replace_untl d A B r)

/-- replace_untl with single U-type produces a U-free formula when r is U-free. -/
theorem replace_untl_U_free (C A B r : Formula Atom)
    (hsingle : has_single_U_type C A B) (hr : is_U_free r = true) :
    is_U_free (replace_untl C A B r) = true := by
  induction C with
  | atom _ => simp [replace_untl, is_U_free]
  | bot => simp [replace_untl, is_U_free]
  | imp c d ih1 ih2 =>
    simp [replace_untl, is_U_free, ih1 hsingle.1, ih2 hsingle.2]
  | box c ih =>
    simp [replace_untl, is_U_free, ih hsingle]
  | untl c d _ _ =>
    have ⟨hc, hd⟩ := hsingle; subst hc; subst hd
    simp [replace_untl, is_U_free, hr]
  | snce c d ih1 ih2 =>
    simp [replace_untl, is_U_free, ih1 hsingle.1, ih2 hsingle.2]

/-- replace_untl is identity on U-free formulas. -/
theorem replace_untl_identity_U_free (C A B r : Formula Atom) (h : is_U_free C = true) :
    replace_untl C A B r = C := by
  induction C with
  | atom _ => simp [replace_untl]
  | bot => simp [replace_untl]
  | imp c d ih1 ih2 => simp [is_U_free] at h; simp [replace_untl, ih1 h.1, ih2 h.2]
  | box c ih => simp [is_U_free] at h; simp [replace_untl, ih h]
  | untl _ _ => simp [is_U_free] at h
  | snce c d ih1 ih2 => simp [is_U_free] at h; simp [replace_untl, ih1 h.1, ih2 h.2]

/-- When U(A,B) holds at a point and C has single U-type with snce_depth_of_U = 0
    and has_no_allpast_allfuture, C evaluates identically to replace_untl C A B (¬⊥).
    This is because every .untl A B in C is evaluated at the SAME point t
    (not shifted by .snce or .allPast/.allFuture). -/
theorem single_U_eval_when_U_true (C A B : Formula Atom)
    (hsingle : has_single_U_type C A B)
    (hexp : has_no_allpast_allfuture C = true)
    (hdepth : snce_depth_of_U C = 0) (M : IntStructure Atom) (t : ℤ)
    (hU : int_truth M t (.untl A B)) :
    int_truth M t C ↔ int_truth M t (replace_untl C A B (Formula.neg .bot)) := by
  induction C with
  | atom _ => simp [replace_untl]
  | bot => simp [replace_untl]
  | imp c d ih1 ih2 =>
    simp [snce_depth_of_U] at hdepth
    simp only [replace_untl, int_truth]
    exact Iff.imp (ih1 hsingle.1 (has_no_allpast_allfuture_true c) (by omega))
                  (ih2 hsingle.2 (has_no_allpast_allfuture_true d) (by omega))
  | box _ => simp [replace_untl, int_truth]
  | untl c d _ _ =>
    have ⟨hc, hd⟩ := hsingle; subst hc; subst hd
    simp [replace_untl, Formula.neg, int_truth]
    exact hU
  | snce c d ih1 ih2 =>
    -- snce_depth_of_U (.snce c d) = 0 means both c and d are U-free
    simp [snce_depth_of_U] at hdepth
    obtain ⟨hc_uf, hd_uf⟩ := hdepth
    -- Both c, d are U-free. replace_untl is identity.
    simp only [replace_untl,
      replace_untl_identity_U_free c A B _ hc_uf,
      replace_untl_identity_U_free d A B _ hd_uf]

/-- Dual: when ¬U(A,B) holds at a point, C evaluates identically to replace_untl C A B ⊥. -/
theorem single_U_eval_when_U_false (C A B : Formula Atom)
    (hsingle : has_single_U_type C A B)
    (hexp : has_no_allpast_allfuture C = true)
    (hdepth : snce_depth_of_U C = 0) (M : IntStructure Atom) (t : ℤ)
    (hnotU : ¬ int_truth M t (.untl A B)) :
    int_truth M t C ↔ int_truth M t (replace_untl C A B .bot) := by
  induction C with
  | atom _ => simp [replace_untl]
  | bot => simp [replace_untl]
  | imp c d ih1 ih2 =>
    simp [snce_depth_of_U] at hdepth
    simp only [replace_untl, int_truth]
    exact Iff.imp (ih1 hsingle.1 (has_no_allpast_allfuture_true c) (by omega))
                  (ih2 hsingle.2 (has_no_allpast_allfuture_true d) (by omega))
  | box _ => simp [replace_untl, int_truth]
  | untl c d _ _ =>
    have ⟨hc, hd⟩ := hsingle; subst hc; subst hd
    simp only [replace_untl, ite_true, and_self, int_truth]
    constructor
    · intro ⟨_, _, _, _⟩; exact False.elim (hnotU ⟨_, ‹_›, ‹_›, ‹_›⟩)
    · intro h; exact False.elim h
  | snce c d ih1 ih2 =>
    simp [snce_depth_of_U] at hdepth
    obtain ⟨hc_uf, hd_uf⟩ := hdepth
    simp only [replace_untl,
      replace_untl_identity_U_free c A B _ hc_uf,
      replace_untl_identity_U_free d A B _ hd_uf]

/-- Semantic equivalence: C ∧ U(A,B) ≡ C[U:=⊤] ∧ U(A,B) for single-U-type C. -/
theorem single_U_and_conj_simplify (C A B : Formula Atom)
    (hsingle : has_single_U_type C A B)
    (hexp : has_no_allpast_allfuture C = true)
    (hdepth : snce_depth_of_U C = 0) :
    int_equiv (Formula.and C (.untl A B))
              (Formula.and (replace_untl C A B (Formula.neg .bot)) (.untl A B)) := by
  intro M t; constructor
  · intro h
    have ⟨hC, hU⟩ := int_truth_and_iff.mp h
    exact int_truth_and_iff.mpr ⟨(single_U_eval_when_U_true C A B hsingle hexp hdepth M t hU).mp hC, hU⟩
  · intro h
    have ⟨hCt, hU⟩ := int_truth_and_iff.mp h
    exact int_truth_and_iff.mpr ⟨(single_U_eval_when_U_true C A B hsingle hexp hdepth M t hU).mpr hCt, hU⟩

/-- Dual of `single_U_and_conj_simplify`: C ∧ ¬U(A,B) ≡ C[U:=⊥] ∧ ¬U(A,B). -/
theorem single_U_and_conj_simplify_neg (C A B : Formula Atom)
    (hsingle : has_single_U_type C A B)
    (hexp : has_no_allpast_allfuture C = true)
    (hdepth : snce_depth_of_U C = 0) :
    int_equiv (Formula.and C (Formula.neg (.untl A B)))
              (Formula.and (replace_untl C A B .bot) (Formula.neg (.untl A B))) := by
  intro M t; constructor
  · intro h
    have ⟨hC, hnotU⟩ := int_truth_and_iff.mp h
    have hnotU' : ¬ int_truth M t (.untl A B) := int_truth_neg_iff.mp hnotU
    exact int_truth_and_iff.mpr
      ⟨(single_U_eval_when_U_false C A B hsingle hexp hdepth M t hnotU').mp hC, hnotU⟩
  · intro h
    have ⟨hCb, hnotU⟩ := int_truth_and_iff.mp h
    have hnotU' : ¬ int_truth M t (.untl A B) := int_truth_neg_iff.mp hnotU
    exact int_truth_and_iff.mpr
      ⟨(single_U_eval_when_U_false C A B hsingle hexp hdepth M t hnotU').mpr hCb, hnotU⟩

/-- Guard 2-clause CNF decomposition for single-U-type formulas:
    F ≡ (replace_untl(F,A,B,⊤) ∨ ¬U(A,B)) ∧ (U(A,B) ∨ replace_untl(F,A,B,⊥))
    where ⊤ = Formula.neg .bot.

    Proof: By classical case split on U(A,B) at each point t:
    - If U(A,B) true: F ↔ replace_untl(F,A,B,⊤) (by single_U_eval_when_U_true).
      RHS first clause: ⊤ ∨ ¬U = ⊤. Second clause: U ∨ q_neg = ⊤.
      Both sides reduce to F ↔ q_pos.
    - If ¬U(A,B): F ↔ replace_untl(F,A,B,⊥) (by single_U_eval_when_U_false).
      RHS first clause: q_pos ∨ ⊤ = ⊤. Second clause: ⊥ ∨ q_neg = q_neg.
      Both sides reduce to F ↔ q_neg. -/
theorem single_U_guard_cnf (w A B : Formula Atom)
    (hsingle : has_single_U_type w A B)
    (hexp : has_no_allpast_allfuture w = true)
    (hdepth : snce_depth_of_U w = 0) :
    int_equiv w (Formula.and
      (Formula.or (replace_untl w A B (Formula.neg .bot)) (Formula.neg (.untl A B)))
      (Formula.or (.untl A B) (replace_untl w A B .bot))) := by
  intro M t; constructor
  · intro hF
    apply int_truth_and_iff.mpr
    constructor
    · -- First clause: q_pos ∨ ¬U
      apply int_truth_or_iff.mpr
      by_cases hU : int_truth M t (.untl A B)
      · left; exact (single_U_eval_when_U_true w A B hsingle hexp hdepth M t hU).mp hF
      · right; exact int_truth_neg_iff.mpr hU
    · -- Second clause: U ∨ q_neg
      apply int_truth_or_iff.mpr
      by_cases hU : int_truth M t (.untl A B)
      · left; exact hU
      · right; exact (single_U_eval_when_U_false w A B hsingle hexp hdepth M t hU).mp hF
  · intro h
    have ⟨h1, h2⟩ := int_truth_and_iff.mp h
    by_cases hU : int_truth M t (.untl A B)
    · -- U true: from second clause, we have U ∨ q_neg. We need F.
      -- From first clause: q_pos ∨ ¬U. Since U, the ¬U branch is false, so q_pos.
      rcases int_truth_or_iff.mp h1 with hqp | hnotU
      · exact (single_U_eval_when_U_true w A B hsingle hexp hdepth M t hU).mpr hqp
      · exact absurd hU (int_truth_neg_iff.mp hnotU)
    · -- ¬U: from second clause: U ∨ q_neg. Since ¬U, we have q_neg.
      rcases int_truth_or_iff.mp h2 with hU' | hqn
      · exact absurd hU' hU
      · exact (single_U_eval_when_U_false w A B hsingle hexp hdepth M t hU).mpr hqn

/-- Guard conjunction distribution for Since (Lemma 10.2.1(ii)):
    S(ev, G₁ ∧ G₂) ↔ S(ev, G₁) ∧ S(ev, G₂).
    Re-export of `since_distrib_and_right` with the naming convention
    used in this file. -/
theorem snce_conj_guard_distribute (ev G1 G2 : Formula Atom) :
    int_equiv (.snce ev (Formula.and G1 G2))
              (Formula.and (.snce ev G1) (.snce ev G2)) :=
  since_distrib_and_right ev G1 G2

/-- Congruence for untl: if a ≡ a' and b ≡ b' then untl a b ≡ untl a' b'. -/
theorem untl_congr {a a' b b' : Formula Atom}
    (ha : int_equiv a a') (hb : int_equiv b b') :
    int_equiv (.untl a b) (.untl a' b') := by
  intro M t; constructor
  · rintro ⟨s, hts, hφ, hψ⟩
    exact ⟨s, hts, (ha M s).mp hφ, fun r hr1 hr2 => (hb M r).mp (hψ r hr1 hr2)⟩
  · rintro ⟨s, hts, hφ, hψ⟩
    exact ⟨s, hts, (ha M s).mpr hφ, fun r hr1 hr2 => (hb M r).mpr (hψ r hr1 hr2)⟩

/-- Congruence for snce: if a ≡ a' and b ≡ b' then snce a b ≡ snce a' b'. -/
theorem snce_congr {a a' b b' : Formula Atom}
    (ha : int_equiv a a') (hb : int_equiv b b') :
    int_equiv (.snce a b) (.snce a' b') := by
  intro M t; constructor
  · rintro ⟨s, hst, hφ, hψ⟩
    exact ⟨s, hst, (ha M s).mp hφ, fun r hr1 hr2 => (hb M r).mp (hψ r hr1 hr2)⟩
  · rintro ⟨s, hst, hφ, hψ⟩
    exact ⟨s, hst, (ha M s).mpr hφ, fun r hr1 hr2 => (hb M r).mpr (hψ r hr1 hr2)⟩

/-- GHR94 Lemma 10.2.4 (general form -- the leaf case):
    `.snce C F` where C, F have `snce_depth_of_U = 0` and `has_single_U_type`
    is separable. Non-recursive -- uses event-guard decomposition + Cases 1-8.

    Proof strategy:
    1. Event-split on U(A,B): S(C,F) <-> S(C^U,F) v S(C^-U,F)
    2. Simplify events: C^U <-> a^U, C^-U <-> a'^-U (a, a' U-free)
    3. Case-split guard F:
       - F U-free: Cases 1/2 directly
       - F not U-free: Guard 2-clause CNF: F <-> (q_pos v -U) ^ (U v q_neg)
         Then S(ev, F) <-> S(ev, q_pos v -U) ^ S(ev, U v q_neg) (Lemma 10.2.1(ii))
         Each term matches Cases 5-8. -/
theorem snce_single_U_depth_one_separable (C w A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (hsingle_C : has_single_U_type C A B)
    (hsingle_w : has_single_U_type w A B)
    (hdC : snce_depth_of_U C = 0) (hdw : snce_depth_of_U w = 0)
    (hexp_C : has_no_allpast_allfuture C = true)
    (hexp_w : has_no_allpast_allfuture w = true) :
    is_separable (.snce C w) := by
  -- Step 1: Event-split on U(A,B)
  -- S(C,w) <-> S(C^U,w) v S(C^-U,w)
  apply since_event_split_separable C A B w
  -- Positive branch: S(C ^ U(A,B), w)
  · -- Step 2a: Simplify event C^U to a^U where a is U-free
    have h_simp_pos := single_U_and_conj_simplify C A B hsingle_C hexp_C hdC
    -- a = replace_untl C A B (neg bot) is U-free
    let a_pos := replace_untl C A B (Formula.neg .bot)
    have ha_uf : is_U_free a_pos = true :=
      replace_untl_U_free C A B (Formula.neg .bot) hsingle_C (by simp [is_U_free, Formula.neg])
    -- S(C^U, w) is equiv to S(a^U, w)
    have h_equiv_pos : int_equiv (.snce (Formula.and C (.untl A B)) w)
        (.snce (Formula.and a_pos (.untl A B)) w) :=
      snce_congr h_simp_pos (int_equiv_refl w)
    apply is_separable_of_equiv h_equiv_pos
    -- Step 3: Case-split on whether w is U-free
    by_cases hwuf : is_U_free w = true
    · -- w is U-free: Case 1
      exact case1_separable_gen a_pos w A B ha_uf hwuf hA_uf hB_uf hA_sf hB_sf
    · -- w not U-free: apply guard 2-clause CNF
      push_neg at hwuf; simp [Bool.not_eq_true] at hwuf
      -- Guard CNF: w <-> (q_pos v -U) ^ (U v q_neg)
      have h_cnf := single_U_guard_cnf w A B hsingle_w hexp_w hdw
      let q_pos := replace_untl w A B (Formula.neg .bot)
      let q_neg := replace_untl w A B .bot
      have hqp_uf : is_U_free q_pos = true :=
        replace_untl_U_free w A B (Formula.neg .bot) hsingle_w (by simp [is_U_free, Formula.neg])
      have hqn_uf : is_U_free q_neg = true :=
        replace_untl_U_free w A B .bot hsingle_w (by simp [is_U_free])
      -- S(a^U, w) equiv S(a^U, (q_pos v -U) ^ (U v q_neg))
      have h_guard_equiv : int_equiv (.snce (Formula.and a_pos (.untl A B)) w)
          (.snce (Formula.and a_pos (.untl A B))
            (Formula.and (Formula.or q_pos (Formula.neg (.untl A B)))
                         (Formula.or (.untl A B) q_neg))) :=
        snce_congr (int_equiv_refl _) h_cnf
      apply is_separable_of_equiv h_guard_equiv
      -- Distribute S over guard conjunction (Lemma 10.2.1(ii))
      have h_distrib := snce_conj_guard_distribute
        (Formula.and a_pos (.untl A B))
        (Formula.or q_pos (Formula.neg (.untl A B)))
        (Formula.or (.untl A B) q_neg)
      apply is_separable_of_equiv h_distrib
      -- Now need: S(a^U, q_pos v -U) ^ S(a^U, U v q_neg) is separable
      apply and_separable
      · -- S(a^U, q_pos v -U): Case 7
        exact case7_separable_gen' a_pos q_pos A B ha_uf hqp_uf hA_uf hB_uf hA_sf hB_sf
      · -- S(a^U, U v q_neg): Case 5
        -- Need to rewrite (U v q_neg) as (q_neg v U)
        have h_comm : int_equiv (Formula.or (.untl A B) q_neg) (Formula.or q_neg (.untl A B)) := by
          intro M t; constructor
          · intro h; rcases int_truth_or_iff.mp h with hu | hq
            · exact int_truth_or_iff.mpr (Or.inr hu)
            · exact int_truth_or_iff.mpr (Or.inl hq)
          · intro h; rcases int_truth_or_iff.mp h with hq | hu
            · exact int_truth_or_iff.mpr (Or.inr hq)
            · exact int_truth_or_iff.mpr (Or.inl hu)
        have h_snce_comm : int_equiv
            (.snce (Formula.and a_pos (.untl A B)) (Formula.or (.untl A B) q_neg))
            (.snce (Formula.and a_pos (.untl A B)) (Formula.or q_neg (.untl A B))) :=
          snce_congr (int_equiv_refl _) h_comm
        apply is_separable_of_equiv h_snce_comm
        exact case5_separable_gen' a_pos q_neg A B ha_uf hqn_uf hA_uf hB_uf hA_sf hB_sf
  -- Negative branch: S(C ^ -U(A,B), w)
  · -- Step 2b: Simplify event C^-U to a'^-U where a' is U-free
    have h_simp_neg := single_U_and_conj_simplify_neg C A B hsingle_C hexp_C hdC
    let a_neg := replace_untl C A B .bot
    have ha_neg_uf : is_U_free a_neg = true :=
      replace_untl_U_free C A B .bot hsingle_C (by simp [is_U_free])
    -- S(C^-U, w) equiv S(a'^-U, w)
    have h_equiv_neg : int_equiv (.snce (Formula.and C (Formula.neg (.untl A B))) w)
        (.snce (Formula.and a_neg (Formula.neg (.untl A B))) w) :=
      snce_congr h_simp_neg (int_equiv_refl w)
    apply is_separable_of_equiv h_equiv_neg
    -- Case-split on whether w is U-free
    by_cases hwuf : is_U_free w = true
    · -- w U-free: Case 2
      exact case2_separable_gen a_neg w A B ha_neg_uf hwuf hA_uf hB_uf hA_sf hB_sf
    · -- w not U-free: apply guard 2-clause CNF
      push_neg at hwuf; simp [Bool.not_eq_true] at hwuf
      have h_cnf := single_U_guard_cnf w A B hsingle_w hexp_w hdw
      let q_pos := replace_untl w A B (Formula.neg .bot)
      let q_neg := replace_untl w A B .bot
      have hqp_uf : is_U_free q_pos = true :=
        replace_untl_U_free w A B (Formula.neg .bot) hsingle_w (by simp [is_U_free, Formula.neg])
      have hqn_uf : is_U_free q_neg = true :=
        replace_untl_U_free w A B .bot hsingle_w (by simp [is_U_free])
      -- S(a'^-U, w) equiv S(a'^-U, (q_pos v -U) ^ (U v q_neg))
      have h_guard_equiv : int_equiv (.snce (Formula.and a_neg (Formula.neg (.untl A B))) w)
          (.snce (Formula.and a_neg (Formula.neg (.untl A B)))
            (Formula.and (Formula.or q_pos (Formula.neg (.untl A B)))
                         (Formula.or (.untl A B) q_neg))) :=
        snce_congr (int_equiv_refl _) h_cnf
      apply is_separable_of_equiv h_guard_equiv
      -- Distribute S over guard conjunction
      have h_distrib := snce_conj_guard_distribute
        (Formula.and a_neg (Formula.neg (.untl A B)))
        (Formula.or q_pos (Formula.neg (.untl A B)))
        (Formula.or (.untl A B) q_neg)
      apply is_separable_of_equiv h_distrib
      apply and_separable
      · -- S(a'^-U, q_pos v -U): Case 8
        exact case8_separable_gen' a_neg q_pos A B ha_neg_uf hqp_uf hA_uf hB_uf hA_sf hB_sf
      · -- S(a'^-U, U v q_neg): Case 6
        have h_comm : int_equiv (Formula.or (.untl A B) q_neg) (Formula.or q_neg (.untl A B)) := by
          intro M t; constructor
          · intro h; rcases int_truth_or_iff.mp h with hu | hq
            · exact int_truth_or_iff.mpr (Or.inr hu)
            · exact int_truth_or_iff.mpr (Or.inl hq)
          · intro h; rcases int_truth_or_iff.mp h with hq | hu
            · exact int_truth_or_iff.mpr (Or.inr hq)
            · exact int_truth_or_iff.mpr (Or.inl hu)
        have h_snce_comm : int_equiv
            (.snce (Formula.and a_neg (Formula.neg (.untl A B))) (Formula.or (.untl A B) q_neg))
            (.snce (Formula.and a_neg (Formula.neg (.untl A B))) (Formula.or q_neg (.untl A B))) :=
          snce_congr (int_equiv_refl _) h_comm
        apply is_separable_of_equiv h_snce_comm
        exact case6_separable_gen' a_neg q_neg A B ha_neg_uf hqn_uf hA_uf hB_uf hA_sf hB_sf

/-- GHR94 Lemma 10.2.4 with U-type preservation:
    `.snce C w` where C, w have `snce_depth_of_U = 0` and `has_single_U_type`
    is `is_separable_with_U_type`. Same structure as `snce_single_U_depth_one_separable`
    but returns the stronger `is_separable_with_U_type` predicate. -/
theorem snce_single_U_depth_one_sep_with_U_type (C w A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (hsingle_C : has_single_U_type C A B)
    (hsingle_F : has_single_U_type w A B)
    (hdC : snce_depth_of_U C = 0) (hdF : snce_depth_of_U w = 0)
    (hexp_C : has_no_allpast_allfuture C = true)
    (hexp_F : has_no_allpast_allfuture w = true) :
    is_separable_with_U_type (.snce C w) A B := by
  -- Step 1: Event-split on U(A,B)
  have hsplit := since_event_split C (.untl A B) w
  apply is_separable_with_U_type_of_equiv hsplit
  apply or_separable_with_U_type
  -- Positive branch: S(C ^ U(A,B), w)
  · have h_simp_pos := single_U_and_conj_simplify C A B hsingle_C hexp_C hdC
    let a_pos := replace_untl C A B (Formula.neg .bot)
    have ha_uf : is_U_free a_pos = true :=
      replace_untl_U_free C A B (Formula.neg .bot) hsingle_C (by simp [is_U_free, Formula.neg])
    have h_equiv_pos : int_equiv (.snce (Formula.and C (.untl A B)) w)
        (.snce (Formula.and a_pos (.untl A B)) w) :=
      snce_congr h_simp_pos (int_equiv_refl w)
    apply is_separable_with_U_type_of_equiv h_equiv_pos
    by_cases hFuf : is_U_free w = true
    · exact case1_sep_with_U_type_gen a_pos w A B ha_uf hFuf hA_uf hB_uf hA_sf hB_sf
    · push_neg at hFuf; simp [Bool.not_eq_true] at hFuf
      have h_cnf := single_U_guard_cnf w A B hsingle_F hexp_F hdF
      let q_pos := replace_untl w A B (Formula.neg .bot)
      let q_neg := replace_untl w A B .bot
      have hqp_uf : is_U_free q_pos = true :=
        replace_untl_U_free w A B (Formula.neg .bot) hsingle_F (by simp [is_U_free, Formula.neg])
      have hqn_uf : is_U_free q_neg = true :=
        replace_untl_U_free w A B .bot hsingle_F (by simp [is_U_free])
      have h_guard_equiv : int_equiv (.snce (Formula.and a_pos (.untl A B)) w)
          (.snce (Formula.and a_pos (.untl A B))
            (Formula.and (Formula.or q_pos (Formula.neg (.untl A B)))
                         (Formula.or (.untl A B) q_neg))) :=
        snce_congr (int_equiv_refl _) h_cnf
      apply is_separable_with_U_type_of_equiv h_guard_equiv
      have h_distrib := snce_conj_guard_distribute
        (Formula.and a_pos (.untl A B))
        (Formula.or q_pos (Formula.neg (.untl A B)))
        (Formula.or (.untl A B) q_neg)
      apply is_separable_with_U_type_of_equiv h_distrib
      apply and_separable_with_U_type
      · exact case7_sep_with_U_type_Z_gen a_pos q_pos A B ha_uf hqp_uf hA_uf hB_uf hA_sf hB_sf
      · have h_comm : int_equiv (Formula.or (.untl A B) q_neg) (Formula.or q_neg (.untl A B)) := by
          intro M t; constructor
          · intro h; rcases int_truth_or_iff.mp h with hu | hq
            · exact int_truth_or_iff.mpr (Or.inr hu)
            · exact int_truth_or_iff.mpr (Or.inl hq)
          · intro h; rcases int_truth_or_iff.mp h with hq | hu
            · exact int_truth_or_iff.mpr (Or.inr hq)
            · exact int_truth_or_iff.mpr (Or.inl hu)
        have h_snce_comm : int_equiv
            (.snce (Formula.and a_pos (.untl A B)) (Formula.or (.untl A B) q_neg))
            (.snce (Formula.and a_pos (.untl A B)) (Formula.or q_neg (.untl A B))) :=
          snce_congr (int_equiv_refl _) h_comm
        apply is_separable_with_U_type_of_equiv h_snce_comm
        exact case5_sep_with_U_type_Z_gen a_pos q_neg A B ha_uf hqn_uf hA_uf hB_uf hA_sf hB_sf
  -- Negative branch: S(C ^ -U(A,B), w)
  · have h_simp_neg := single_U_and_conj_simplify_neg C A B hsingle_C hexp_C hdC
    let a_neg := replace_untl C A B .bot
    have ha_neg_uf : is_U_free a_neg = true :=
      replace_untl_U_free C A B .bot hsingle_C (by simp [is_U_free])
    have h_equiv_neg : int_equiv (.snce (Formula.and C (Formula.neg (.untl A B))) w)
        (.snce (Formula.and a_neg (Formula.neg (.untl A B))) w) :=
      snce_congr h_simp_neg (int_equiv_refl w)
    apply is_separable_with_U_type_of_equiv h_equiv_neg
    by_cases hFuf : is_U_free w = true
    · exact case2_sep_with_U_type_gen a_neg w A B ha_neg_uf hFuf hA_uf hB_uf hA_sf hB_sf
    · push_neg at hFuf; simp [Bool.not_eq_true] at hFuf
      have h_cnf := single_U_guard_cnf w A B hsingle_F hexp_F hdF
      let q_pos := replace_untl w A B (Formula.neg .bot)
      let q_neg := replace_untl w A B .bot
      have hqp_uf : is_U_free q_pos = true :=
        replace_untl_U_free w A B (Formula.neg .bot) hsingle_F (by simp [is_U_free, Formula.neg])
      have hqn_uf : is_U_free q_neg = true :=
        replace_untl_U_free w A B .bot hsingle_F (by simp [is_U_free])
      have h_guard_equiv : int_equiv (.snce (Formula.and a_neg (Formula.neg (.untl A B))) w)
          (.snce (Formula.and a_neg (Formula.neg (.untl A B)))
            (Formula.and (Formula.or q_pos (Formula.neg (.untl A B)))
                         (Formula.or (.untl A B) q_neg))) :=
        snce_congr (int_equiv_refl _) h_cnf
      apply is_separable_with_U_type_of_equiv h_guard_equiv
      have h_distrib := snce_conj_guard_distribute
        (Formula.and a_neg (Formula.neg (.untl A B)))
        (Formula.or q_pos (Formula.neg (.untl A B)))
        (Formula.or (.untl A B) q_neg)
      apply is_separable_with_U_type_of_equiv h_distrib
      apply and_separable_with_U_type
      · exact case8_sep_with_U_type_Z_gen a_neg q_pos A B ha_neg_uf hqp_uf hA_uf hB_uf hA_sf hB_sf
      · have h_comm : int_equiv (Formula.or (.untl A B) q_neg) (Formula.or q_neg (.untl A B)) := by
          intro M t; constructor
          · intro h; rcases int_truth_or_iff.mp h with hu | hq
            · exact int_truth_or_iff.mpr (Or.inr hu)
            · exact int_truth_or_iff.mpr (Or.inl hq)
          · intro h; rcases int_truth_or_iff.mp h with hq | hu
            · exact int_truth_or_iff.mpr (Or.inr hq)
            · exact int_truth_or_iff.mpr (Or.inl hu)
        have h_snce_comm : int_equiv
            (.snce (Formula.and a_neg (Formula.neg (.untl A B))) (Formula.or (.untl A B) q_neg))
            (.snce (Formula.and a_neg (Formula.neg (.untl A B))) (Formula.or q_neg (.untl A B))) :=
          snce_congr (int_equiv_refl _) h_comm
        apply is_separable_with_U_type_of_equiv h_snce_comm
        exact case6_sep_with_U_type_Z_gen a_neg q_neg A B ha_neg_uf hqn_uf hA_uf hB_uf hA_sf hB_sf


end Cslib.Logic.Bimodal.Metalogic.Separation
