/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Eric Wieser
-/
module
public import Mathlib.Data.List.Sort

/-!
# A Monadic version of the builtin `List.insertionSort`

This can be instantiated with `Id` to recover the original, or with `TimeM` or `FreeM` for
algorithmic analysis.
-/

public section

namespace List

variable {m} [Monad m] (r : α → α → m Bool)

/-- A monadic version of `List.orderedInsert`. -/
def orderedInsertM (a : α) : List α → m (List α)
  | [] => return [a]
  | b :: l => do if ← r a b then return a :: b :: l else return b :: (← orderedInsertM a l)

@[simp]
theorem orderedInsertM_pure [LawfulMonad m] (r : α → α → Bool) (a : α) (xs : List α) :
    orderedInsertM (fun x y => (pure (r x y) : m Bool)) a xs =
      pure (orderedInsert (r · ·) a xs) := by
  fun_induction orderedInsertM with grind [orderedInsertM]

@[simp]
theorem idRun_orderedInsertM (r : α → α → Id Bool) (a : α) (xs : List α) :
    Id.run (orderedInsertM r a xs) = orderedInsert (fun x y => Id.run <| r x y) a xs :=
  orderedInsertM_pure _ _ _

/-- A monadic version of `List.insertionSort`. -/
@[simp]
def insertionSortM : List α → m (List α)
  | [] => return []
  | b :: l => do orderedInsertM r b (← insertionSortM l)

@[simp]
theorem insertionSortM_pure [LawfulMonad m] (xs : List α) (r : α → α → Bool) :
    insertionSortM (fun x y => (pure (r x y) : m Bool)) xs = pure (insertionSort (r · ·) xs) := by
  fun_induction insertionSortM with simp_all

@[simp]
theorem idRun_insertionSortM (xs : List α) (r : α → α → Id Bool) :
    Id.run (insertionSortM r xs) = insertionSort (fun x y => Id.run <| r x y) xs :=
  insertionSortM_pure _ _

end List
