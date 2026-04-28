/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas
-/
module

public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.IsSort
public import Cslib.Algorithms.Lean.Query.Sort.Insertion.Defs
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Group.Defs

/-! # Insertion Sort: Correctness and Upper Bound

Proofs that `insertionSort` is a correct comparison sort and uses at most `n²` queries.
All proofs are by plain equational reasoning on `FreeM.eval` and `FreeM.queriesOn`.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

variable {α : Type}

-- ## Evaluation simp lemmas for orderedInsert

@[simp] theorem eval_orderedInsert_nil (oracle : {ι : Type} → LEQuery α ι → ι) (x : α) :
    (orderedInsert x ([] : List α)).eval oracle = [x] := by
  simp [orderedInsert]

@[simp] theorem eval_orderedInsert_cons (oracle : {ι : Type} → LEQuery α ι → ι) (x y : α)
    (ys : List α) :
    (orderedInsert x (y :: ys)).eval oracle =
      if oracle (.le x y) then x :: y :: ys
      else y :: (orderedInsert x ys).eval oracle := by
  simp [orderedInsert, LEQuery.ask]
  split <;> simp_all

-- ## Evaluation simp lemmas for insertionSort

@[simp] theorem eval_insertionSort_nil (oracle : {ι : Type} → LEQuery α ι → ι) :
    (insertionSort (α := α) []).eval oracle = [] := by
  simp [insertionSort]

@[simp] theorem eval_insertionSort_cons (oracle : {ι : Type} → LEQuery α ι → ι)
    (x : α) (xs : List α) :
    (insertionSort (x :: xs)).eval oracle =
      (orderedInsert x ((insertionSort xs).eval oracle)).eval oracle := by
  simp [insertionSort]

-- ## Permutation proofs

theorem orderedInsert_perm (oracle : {ι : Type} → LEQuery α ι → ι) (x : α) (xs : List α) :
    ((orderedInsert x xs).eval oracle).Perm (x :: xs) := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [eval_orderedInsert_cons]
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons _ ih).trans (List.Perm.swap _ _ _)

theorem insertionSort_perm (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    ((insertionSort xs).eval oracle).Perm xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [eval_insertionSort_cons]
    exact (orderedInsert_perm oracle x _).trans (List.Perm.cons _ ih)

-- ## Sortedness proofs

theorem orderedInsert_sorted
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (x : α) (xs : List α) (hxs : xs.Pairwise r) :
    ((orderedInsert x xs).eval oracle).Pairwise r := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [eval_orderedInsert_cons, horacle]
    split
    next h =>
      have hle : r x y := by simpa [decide_eq_true_eq] using h
      exact List.pairwise_cons.mpr ⟨fun z hz =>
        match List.mem_cons.mp hz with
        | .inl h => h ▸ hle
        | .inr h => _root_.trans hle (List.rel_of_pairwise_cons hxs h), hxs⟩
    next h =>
      have hle : ¬ r x y := by simpa [decide_eq_true_eq] using h
      have hyx : r y x := (Std.Total.total y x).resolve_right hle
      have ih' := ih hxs.of_cons
      have hperm := orderedInsert_perm oracle x ys
      exact List.pairwise_cons.mpr ⟨fun z hz =>
        match List.mem_cons.mp (hperm.mem_iff.mp hz) with
        | .inl h => h ▸ hyx
        | .inr h => List.rel_of_pairwise_cons hxs h, ih'⟩

theorem insertionSort_sorted
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (xs : List α) :
    ((insertionSort xs).eval oracle).Pairwise r := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [eval_insertionSort_cons]
    exact orderedInsert_sorted r oracle horacle x _ ih

-- ## Query count proofs

theorem orderedInsert_queriesOn_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (x : α) (xs : List α) :
    (orderedInsert x xs).queriesOn oracle ≤ xs.length := by
  induction xs with
  | nil => simp [orderedInsert]
  | cons y ys ih =>
    unfold orderedInsert LEQuery.ask
    simp
    split
    · simp_all
    · simp_all; omega

theorem insertionSort_queriesOn_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs : List α) :
    (insertionSort xs).queriesOn oracle ≤ xs.length ^ 2 := by
  induction xs with
  | nil => simp [insertionSort]
  | cons x xs ih =>
    have hq : (insertionSort (x :: xs)).queriesOn oracle =
        (insertionSort xs).queriesOn oracle +
        (orderedInsert x ((insertionSort xs).eval oracle)).queriesOn oracle := by
      simp [insertionSort]
    rw [hq]
    have hlen : ((insertionSort xs).eval oracle).length = xs.length :=
      (insertionSort_perm oracle xs).length_eq
    have hord := orderedInsert_queriesOn_le oracle x ((insertionSort xs).eval oracle)
    rw [hlen] at hord
    have h1 := Nat.add_le_add ih hord
    have hpow : xs.length ^ 2 + xs.length ≤ (xs.length + 1) ^ 2 := by
      have : (xs.length + 1) ^ 2 = xs.length ^ 2 + 2 * xs.length + 1 := by ring
      omega
    simp only [List.length_cons]
    exact Nat.le_trans h1 hpow

-- ## UpperBound and IsSort instances

public theorem insertionSort_upperBound :
    UpperBound (insertionSort (α := α)) List.length (· ^ 2) := by
  intro oracle n x hle
  exact Nat.le_trans (insertionSort_queriesOn_le oracle x)
    (Nat.pow_le_pow_left hle 2)

public theorem insertionSort_isSort : IsSort (insertionSort (α := α)) where
  perm xs oracle := insertionSort_perm oracle xs
  sorted := by
    intro xs oracle r _ _ _ horacle
    exact insertionSort_sorted r oracle horacle xs

end Cslib.Query

end -- public section
