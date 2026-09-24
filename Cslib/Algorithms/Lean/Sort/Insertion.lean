/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Eric Wieser
-/
module

public import Mathlib.Data.List.Sort
public import Cslib.Foundations.Control.Monad.IsMonadHom

import Cslib.Init

/-!
# A Monadic version of Mathlib's `List.insertionSort`

This can be instantiated with `Id` to recover the original, or with `TimeM` or `FreeM` for
algorithmic analysis.
-/

public section

open Cslib (IsMonadHom)

namespace List

variable {m n} [Monad m] [Monad n] (r : α → α → m Bool)

/-- A monadic version of `List.orderedInsert`. -/
def orderedInsertM (a : α) : List α → m (List α)
  | [] => return [a]
  | b :: l => do if ← r a b then return a :: b :: l else return b :: (← orderedInsertM a l)

@[simp, grind =] theorem orderedInsertM_nil (a : α) : orderedInsertM r a [] = pure [a] := by
  rfl
@[simp, grind =] theorem orderedInsertM_cons (a b : α) (l : List α) :
    orderedInsertM r a (b :: l) = do
      if ← r a b then return a :: b :: l else return b :: (← orderedInsertM r a l) := by
  rfl

@[simp]
theorem orderedInsertM_pure [LawfulMonad m] (r : α → α → Bool) (a : α) (xs : List α) :
    orderedInsertM (fun x y => (pure (r x y) : m Bool)) a xs =
      pure (orderedInsert (r · ·) a xs) := by
  fun_induction orderedInsertM with grind [orderedInsertM]

@[simp]
theorem idRun_orderedInsertM (r : α → α → Id Bool) (a : α) (xs : List α) :
    Id.run (orderedInsertM r a xs) = orderedInsert (fun x y => Id.run <| r x y) a xs :=
  orderedInsertM_pure _ _ _

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_orderedInsertM {f : {β : Type} → m β → n β}
    (hf : IsMonadHom m n f) (r : α → α → m Bool) (a : α) (xs : List α) :
    f (orderedInsertM r a xs) = orderedInsertM (fun x y => f (r x y)) a xs := by
  fun_induction orderedInsertM r a xs with grind

/-- A monadic version of `List.insertionSort`. -/
def insertionSortM : List α → m (List α)
  | [] => return []
  | b :: l => do orderedInsertM r b (← insertionSortM l)

@[simp] theorem insertionSortM_nil : insertionSortM r [] = pure [] := by
  rfl
@[simp] theorem insertionSortM_cons (b : α) (l : List α) :
    insertionSortM r (b :: l) = (do orderedInsertM r b (← insertionSortM r l)) := by
  rfl

@[simp]
theorem insertionSortM_pure [LawfulMonad m] (xs : List α) (r : α → α → Bool) :
    insertionSortM (fun x y => (pure (r x y) : m Bool)) xs = pure (insertionSort (r · ·) xs) := by
  fun_induction insertionSortM with simp_all

@[simp]
theorem idRun_insertionSortM (xs : List α) (r : α → α → Id Bool) :
    Id.run (insertionSortM r xs) = insertionSort (fun x y => Id.run <| r x y) xs :=
  insertionSortM_pure _ _

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_listInsertionSortM {f : {β : Type} → m β → n β}
    (hf : IsMonadHom m n f) (r : α → α → m Bool) (xs : List α) :
    f (insertionSortM r xs) = insertionSortM (fun x y => f (r x y)) xs := by
  fun_induction insertionSortM r xs with simp [hf.map_pure, hf.map_bind, hf.map_orderedInsertM, *]

end List
