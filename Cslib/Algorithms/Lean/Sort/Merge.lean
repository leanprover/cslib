/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Eric Wieser
-/
module
import all Init.Data.List.Sort.Basic

/-!
# A Monadic version of the builtin `List.mergeSort`

This can be instantiated with `Id` to recover the original, or with `TimeM` or `FreeM` for
algorithmic analysis.
-/

public section

namespace List

variable {m} [Monad m]

/-- A monadic version of `List.merge` -/
def mergeM (xs ys : List α) (le : α → α → m Bool) : m (List α) := do
  match xs, ys with
  | [], ys => return ys
  | xs, [] => return xs
  | x :: xs, y :: ys =>
    if ← le x y then
      return x :: (← mergeM xs (y :: ys) le)
    else
      return y :: (← mergeM (x :: xs) ys le)

@[simp] theorem nil_mergeM (ys : List α) (le : α → α → m Bool) : mergeM [] ys le = pure ys := by
  simp [mergeM]
@[simp] theorem mergeM_right (xs : List α) (le : α → α → m Bool) : mergeM xs [] le = pure xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [mergeM]

@[simp]
theorem mergeM_pure [LawfulMonad m] (xs ys : List α) (le : α → α → Bool) :
    mergeM xs ys (fun x y => (pure (le x y) : m Bool)) = pure (merge xs ys le) := by
  fun_induction mergeM with grind [merge]

@[simp]
theorem idRun_mergeM (xs ys : List α) (le : α → α → Id Bool) :
    Id.run (mergeM xs ys le) = merge xs ys (fun x y => Id.run <| le x y) :=
  mergeM_pure _ _ _

set_option linter.unusedVariables false in
/-- A monadic version of `List.mergeSortM` -/
def mergeSortM : ∀ (xs : List α) (le : α → α → m Bool), m (List α)
  | [], _ => return []
  | [a], _ => return [a]
  | a :: b :: xs, le => do
    let lr := MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩
    have := by simpa using lr.2.2
    have := by simpa using lr.1.2
    mergeM (← mergeSortM lr.1 le) (← mergeSortM lr.2 le) le
termination_by xs => xs.length

@[simp]
theorem mergeSortM_pure [LawfulMonad m] (xs : List α) (le : α → α → Bool) :
    mergeSortM xs (fun x y => (pure (le x y) : m Bool)) = pure (mergeSort xs le) := by
  fun_induction mergeSort with
  | case1 | case2 => simp [mergeSortM]
  | case3  a b xs le lr _ _ ih1 ih2 =>
    simp only [mergeSortM]
    rw [ih1, ih2]
    simp

@[simp]
theorem idRun_mergeSortM (xs : List α) (le : α → α → Id Bool) :
    Id.run (mergeSortM xs le) = mergeSort xs (fun x y => Id.run <| le x y) :=
  mergeSortM_pure _ _

end List
