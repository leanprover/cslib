module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Tactic

/-!
# Minimum of a list (linear scan)

We implement a simple linear scan algorithm that returns the minimum element of a list,
counting comparisons as time cost.

We return an `Option α` to handle the empty list.

## Main results

- `minScan_correct`: if the output is `some m`, then `m` is an element of the list and is
  below every element of the list.
- `minScan_time_le`: the number of comparisons is at most the list length.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open List

variable {α : Type} [LinearOrder α]

/-- `m` is a minimum element of `xs` if it is below every element of `xs`. -/
abbrev MinOfList (m : α) (xs : List α) : Prop := ∀ z ∈ xs, m ≤ z

/-- Compute the minimum of a list by scanning from the right, counting comparisons.

Cost model: each comparison (`x ≤ m`) costs one tick. -/
def minScan : List α → TimeM ℕ (Option α)
  | [] => return none
  | x :: xs => do
    let r ← minScan xs
    match r with
    | none => return some x
    | some m => do
      ✓
      if x ≤ m then
        return some x
      else
        return some m

section Correctness

/-- Correctness for `minScan`.

If `minScan xs` returns `some m`, then `m ∈ xs` and `m` is a minimum element of `xs`.
If it returns `none`, then `xs` is empty. -/
theorem minScan_correct (xs : List α) :
    match ⟪minScan xs⟫ with
    | none => xs = []
    | some m => m ∈ xs ∧ MinOfList m xs := by
  induction xs with
  | nil =>
    simp [minScan]
  | cons x xs ih =>
    cases h : ⟪minScan xs⟫ with
    | none =>
      have hxsempty : xs = [] := by
        simpa [h] using ih
      subst hxsempty
      simp [minScan, h]
    | some m =>
      have ihm : m ∈ xs ∧ MinOfList m xs := by
        simpa [h] using ih
      by_cases hxm : x ≤ m
      · -- choose `x`
        refine ?_
        simp [minScan, h, hxm, ihm]
        intro z hz
        rcases hz with rfl | hz
        · exact le_rfl
        · exact le_trans hxm (ihm.2 z hz)
      · -- choose `m`
        have hmx : m ≤ x := by
          have ht := le_total m x
          cases ht with
          | inl hmx => exact hmx
          | inr hcontr => exact False.elim (hxm hcontr)
        refine ?_
        simp [minScan, h, hxm, ihm]
        intro z hz
        rcases hz with rfl | hz
        · exact hmx
        · exact ihm.2 z hz

end Correctness

section TimeComplexity

/-- The scan does at most one comparison per element. -/
theorem minScan_time_le (xs : List α) : (minScan xs).time ≤ xs.length := by
  induction xs with
  | nil =>
    simp [minScan]
  | cons x xs ih =>
    -- Split on whether the recursive call found a minimum.
    cases h : ⟪minScan xs⟫ with
    | none =>
      -- No comparison performed at this step.
      have : (minScan xs).time ≤ xs.length + 1 := le_trans ih (Nat.le_succ _)
      simpa [minScan, time_bind, h, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using this
    | some m =>
      -- One comparison performed at this step.
      have : (minScan xs).time + 1 ≤ xs.length + 1 := Nat.add_le_add_right ih 1
      simpa [minScan, time_bind, h, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using this

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
