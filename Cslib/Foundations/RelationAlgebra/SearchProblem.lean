/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.ActiveSearch
public import Cslib.Foundations.RelationAlgebra.SearchConstraints
public import Cslib.Foundations.RelationAlgebra.SearchSymmetry

/-!
# Numeric problems for certified relation-algebra counting

A problem combines atomic associativity equations with lexicographic minimality under atom
renamings. Its executable callbacks fit the active-constraint search checker. The soundness
theorem counts bounded masks, leaving the interpretation of the equation and permutation
families to the signature-specific classification theorem.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Search

open Counting

/-- A numeric search problem for canonical associative cycle masks. -/
structure Problem where
  /-- Number of cycle variables. -/
  «variables» : ℕ
  /-- Number of associativity equations. -/
  equationCount : ℕ
  /-- The normalized associativity equations. -/
  equations : ℕ → Equation
  /-- Number of atom renamings used for canonicality. -/
  permutationCount : ℕ
  /-- The induced action of each renaming on cycle variables. -/
  permutations : ℕ → ℕ → ℕ

/-- Apply a cycle-variable permutation using only numeric bit operations. -/
def permuteMask (r : ℕ) (permutation : ℕ → ℕ) (mask : ℕ) : ℕ :=
  Code.bitsOf (fun i => Code.bitAt mask (permutation i)) r

/-- The numeric permutation agrees with the Boolean-vector permutation. -/
theorem permuteMask_eq (r : ℕ) (permutation : ℕ → ℕ) (mask : ℕ) :
    permuteMask r permutation mask =
      choiceMask (fun i : Fin r => Code.bitAt mask (permutation i)) := by
  apply Code.eq_of_testBit_eq_of_lt (Code.bitsOf_lt _ _) (choiceMask_lt _)
  intro i hi
  have hl := Code.bitAt_bitsOf (p := fun i => Code.bitAt mask (permutation i)) hi
  have hr := bitAt_choiceMask (fun j : Fin r => Code.bitAt mask (permutation j)) ⟨i, hi⟩
  simpa only [Code.bitAt_eq_testBit] using hl.trans hr.symm

/-- Check that a cube has no assigned bits outside the problem's variable range. -/
def cubeBounded (r : ℕ) (cube : Cube) : Bool :=
  Nat.blt cube.on (2 ^ r) && Nat.blt cube.off (2 ^ r)

/-- A cube's positive requirements are included in every matching assignment mask. -/
theorem maskSubset_of_matches {r : ℕ} {cube : Cube} {bits : Fin r → Bool}
    (hon : cube.on < 2 ^ r) (hm : cube.Matches r bits) :
    MaskSubset cube.on (choiceMask bits) := by
  apply maskSubset_iff.mpr
  intro i hi
  by_cases hir : i < r
  · have hbit := hm.1 ⟨i, hir⟩ (by simpa only [Code.bitAt_eq_testBit] using hi)
    have hmask := bitAt_choiceMask bits ⟨i, hir⟩
    simpa only [Code.bitAt_eq_testBit, hbit] using hmask
  · have hf := Code.testBit_eq_false_of_lt hon (Nat.le_of_not_gt hir)
    rw [hf] at hi
    contradiction

/-- No excluded bit is present in a matching assignment mask. -/
theorem mask_disjoint_of_matches {r : ℕ} {cube : Cube} {bits : Fin r → Bool}
    (hm : cube.Matches r bits) : choiceMask bits &&& cube.off = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and]
  by_cases hir : i < r
  · cases hoff : cube.off.testBit i
    · simp
    · have hbit := hm.2 ⟨i, hir⟩ (by simpa only [Code.bitAt_eq_testBit] using hoff)
      have hmask := bitAt_choiceMask bits ⟨i, hir⟩
      have hz : (choiceMask bits).testBit i = false := by
        simpa only [Code.bitAt_eq_testBit, hbit] using hmask
      simp [hz]
  · simp [Code.testBit_eq_false_of_lt (choiceMask_lt bits) (Nat.le_of_not_gt hir)]

/-- Enumerate equations first and canonicality constraints second. -/
def Problem.constraints (problem : Problem) : ActiveSearch.Constraints where
  size := problem.equationCount + problem.permutationCount
  eval witness mask :=
    if witness < problem.equationCount then (problem.equations witness).eval mask
    else Nat.ble mask (permuteMask problem.variables
      (problem.permutations (witness - problem.equationCount)) mask)
  conflict witness cube := cubeBounded problem.variables cube &&
    if witness < problem.equationCount then
      (problem.equations witness).conflict cube.on cube.off
    else permutationConflict problem.variables cube.on cube.off
      (problem.permutations (witness - problem.equationCount))
  settled witness cube := cubeBounded problem.variables cube &&
    if witness < problem.equationCount then
      (problem.equations witness).settled cube.on cube.off
    else permutationSettled problem.variables cube.on cube.off
      (problem.permutations (witness - problem.equationCount))

/-- Each permutation maps the bounded variable indices to bounded variable indices. -/
def Problem.PermutationsBounded (problem : Problem) : Prop :=
  ∀ p < problem.permutationCount, ∀ i < problem.variables,
    problem.permutations p i < problem.variables

/-- Partial-assignment callbacks for equations and canonicality are sound. -/
theorem Problem.constraints_sound (problem : Problem) (hp : problem.PermutationsBounded) :
    problem.constraints.Sound problem.variables where
  conflict witness hi cube bits hc hm := by
    change (cubeBounded problem.variables cube && _) = true at hc
    simp only [Bool.and_eq_true] at hc
    have hb := hc.1
    simp only [cubeBounded, Bool.and_eq_true, Nat.blt_eq] at hb
    have hon := maskSubset_of_matches hb.1 hm
    have hoff := mask_disjoint_of_matches hm
    by_cases he : witness < problem.equationCount
    · have hc' : (problem.equations witness).conflict cube.on cube.off = true := by
        simpa only [he, ↓reduceIte] using hc.2
      simpa only [Problem.constraints, he, ↓reduceIte] using
        Equation.eval_false_of_conflict hon hoff hc'
    · have hpi : witness - problem.equationCount < problem.permutationCount := by
        change witness < problem.equationCount + problem.permutationCount at hi
        omega
      have hc' : permutationConflict problem.variables cube.on cube.off
          (problem.permutations (witness - problem.equationCount)) = true := by
        simpa only [he, ↓reduceIte] using hc.2
      have hn := permutationConflict_sound (hp _ hpi)
        (fun i hir h => by
          have hx := hm.1 ⟨i, hir⟩ h
          exact (bitAt_choiceMask bits ⟨i, hir⟩).trans hx)
        (fun i hir h => by
          have hx := hm.2 ⟨i, hir⟩ h
          exact (bitAt_choiceMask bits ⟨i, hir⟩).trans hx)
        (choiceMask_lt bits) hc'
      simp only [Problem.constraints, he, ↓reduceIte, permuteMask_eq]
      apply Bool.eq_false_iff.mpr
      exact fun h => hn (Nat.le_of_ble_eq_true h)
  settled witness hi cube bits hc hm := by
    change (cubeBounded problem.variables cube && _) = true at hc
    simp only [Bool.and_eq_true] at hc
    have hb := hc.1
    simp only [cubeBounded, Bool.and_eq_true, Nat.blt_eq] at hb
    have hon := maskSubset_of_matches hb.1 hm
    have hoff := mask_disjoint_of_matches hm
    by_cases he : witness < problem.equationCount
    · have hc' : (problem.equations witness).settled cube.on cube.off = true := by
        simpa only [he, ↓reduceIte] using hc.2
      simpa only [Problem.constraints, he, ↓reduceIte] using
        Equation.eval_true_of_settled hon hoff hc'
    · have hpi : witness - problem.equationCount < problem.permutationCount := by
        change witness < problem.equationCount + problem.permutationCount at hi
        omega
      have hc' : permutationSettled problem.variables cube.on cube.off
          (problem.permutations (witness - problem.equationCount)) = true := by
        simpa only [he, ↓reduceIte] using hc.2
      have hn := permutationSettled_sound (hp _ hpi)
        (fun i hir h => by
          have hx := hm.1 ⟨i, hir⟩ h
          exact (bitAt_choiceMask bits ⟨i, hir⟩).trans hx)
        (fun i hir h => by
          have hx := hm.2 ⟨i, hir⟩ h
          exact (bitAt_choiceMask bits ⟨i, hir⟩).trans hx)
        (choiceMask_lt bits) hc'
      simpa only [Problem.constraints, he, ↓reduceIte, permuteMask_eq, Nat.ble_eq] using hn

/-- A mask satisfies every associativity and canonicality constraint of the problem. -/
def Problem.valid (problem : Problem) (mask : ℕ) : Bool :=
  Code.allBelow (fun i => problem.constraints.eval i mask) problem.constraints.size

/-- The combined Boolean checker expresses equations and least-mask inequalities. -/
theorem Problem.valid_iff (problem : Problem) (mask : ℕ) :
    problem.valid mask = true ↔
      (∀ i < problem.equationCount, (problem.equations i).eval mask = true) ∧
      ∀ p < problem.permutationCount, mask ≤
        choiceMask (fun i : Fin problem.variables =>
          Code.bitAt mask (problem.permutations p i)) := by
  rw [Problem.valid, Code.allBelow_eq_true]
  constructor
  · intro h
    constructor
    · intro i hi
      have hb : i < problem.constraints.size := by
        change i < problem.equationCount + problem.permutationCount
        omega
      simpa only [Problem.constraints, hi, ↓reduceIte] using h i hb
    · intro p hp
      have hb : problem.equationCount + p < problem.constraints.size := by
        change problem.equationCount + p < problem.equationCount + problem.permutationCount
        omega
      have hn : ¬problem.equationCount + p < problem.equationCount := by omega
      simpa only [Problem.constraints, hn, ↓reduceIte, Nat.add_sub_cancel_left,
        permuteMask_eq, Nat.ble_eq] using h (problem.equationCount + p) hb
  · rintro ⟨heq, hperm⟩ i hi
    by_cases he : i < problem.equationCount
    · simpa only [Problem.constraints, he, ↓reduceIte] using heq i he
    · have hp : i - problem.equationCount < problem.permutationCount := by
        change i < problem.equationCount + problem.permutationCount at hi
        omega
      simpa only [Problem.constraints, he, ↓reduceIte, permuteMask_eq, Nat.ble_eq] using
        hperm (i - problem.equationCount) hp

/-- Check a complete count certificate for a numeric problem. -/
def Problem.check (problem : Problem) (certificate : Certificate) : Option ℕ :=
  Counting.check (ActiveSearch.rules problem.variables problem.constraints)
    (ActiveSearch.initial problem.constraints) certificate

/-- A successful problem certificate gives the exact cardinality of satisfying masks. -/
theorem Problem.check_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (certificate : Certificate) (result : ℕ) (h : problem.check certificate = some result) :
    ((Finset.range (2 ^ problem.variables)).filter fun mask =>
      problem.valid mask = true).card = result := by
  have hc := Counting.check_sound
    (ActiveSearch.rules_sound (problem.constraints_sound hp)) certificate
    (ActiveSearch.initial problem.constraints) result h
  rw [ActiveSearch.modelCount_initial_masks] at hc
  exact hc

end Cslib.RelationAlgebra.Search
