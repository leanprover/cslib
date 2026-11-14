/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.IsSort
public import Cslib.Algorithms.Lean.Query.Sort.Bubble.Defs
-- Needed for the generated induction principle `List.bubbleSort.induct`.
import all Cslib.Algorithms.Lean.Sort.Bubble

/-! # Bubble Sort: Correctness, Stability and Query Count

Proofs that `bubbleSort` is a correct and stable comparison sort that makes exactly
`n * (n - 1) / 2` queries on every input of length `n`, whatever the oracle answers.

`eval_bubbleSort` identifies the query program with `List.bubbleSort` under the comparator
induced by the oracle, so correctness and stability transfer from the `List.bubbleSort` API.

## Main results

* `Cslib.Query.eval_bubbleSort`: evaluating the query program gives `List.bubbleSort`.
* `Cslib.Query.countQueries_bubbleSort`: the exact query count `n * (n - 1) / 2`.
* `Cslib.Query.bubbleSort_upperBound` and `Cslib.Query.bubbleSort_isSort`.
* `Cslib.Query.sublist_bubbleSort`: stability, in the sublist form of `List.sublist_mergeSort`.
-/

open Cslib Cslib.Query
open scoped List

public section

namespace Cslib.Query

variable {α : Type}

/-! ## Evaluation -/

/-- Evaluating a query-based bubble pass agrees with `List.bubblePass` using the relation
supplied by the oracle. -/
@[simp] theorem eval_bubblePass (oracle : {ι : Type} → LEQuery α ι → ι) (x : α) (xs : List α) :
    (bubblePass x xs).eval oracle = xs.bubblePass (fun x y => oracle (.le x y)) x :=
  Id.pure_injective <| by simp [FreeM.isMonadHom_pure_eval oracle |>.map_listBubblePassM _ x xs]

/-- Evaluating query-based bubble sort agrees with `List.bubbleSort` using the relation supplied
by the oracle. Correctness and stability transfer from the `List.bubbleSort` API. -/
@[simp] theorem eval_bubbleSort (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (bubbleSort xs).eval oracle = xs.bubbleSort (fun x y => oracle (.le x y)) :=
  Id.pure_injective <| by simp [FreeM.isMonadHom_pure_eval oracle |>.map_listBubbleSortM _ xs]

/-! ## Stability -/

/-- Bubble sort is stable: when the oracle decides `r`, a sublist of the input that is sorted for
`r` is a sublist of the output. No order axioms on `r` are needed. -/
theorem sublist_bubbleSort (r : α → α → Prop) [DecidableRel r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) {xs c : List α}
    (hc : c.Pairwise r) (hsub : c <+ xs) : c <+ (bubbleSort xs).eval oracle := by
  rw [eval_bubbleSort]
  exact List.sublist_bubbleSort _ (hc.imp fun hab => (horacle _ _).trans (decide_eq_true hab)) hsub

/-! ## Query count proofs -/

/-- A pass over `x :: xs` makes exactly one query per element of `xs`, whatever the oracle
answers. -/
@[simp] theorem countQueries_bubblePass (oracle : {ι : Type} → LEQuery α ι → ι)
    (x : α) (xs : List α) :
    (bubblePass x xs).countQueries oracle = xs.length := by
  unfold bubblePass
  induction xs generalizing x with
  | nil => simp only [List.bubblePassM_nil, FreeM.countQueries_pure, List.length_nil]
  | cons y ys ih =>
    by_cases h : oracle (.le x y) = true
    · simp only [List.bubblePassM_cons, FreeM.countQueries_bind, FreeM.countQueries_lift,
        LEQuery.eval_ask, h, ↓reduceIte, FreeM.countQueries_pure, ih, Nat.add_zero,
        List.length_cons]
      omega
    · simp only [List.bubblePassM_cons, FreeM.countQueries_bind, FreeM.countQueries_lift,
        LEQuery.eval_ask, h, Bool.false_eq_true, ↓reduceIte, FreeM.countQueries_pure, ih,
        Nat.add_zero, List.length_cons]
      omega

/-- Bubble sort makes exactly `n * (n - 1) / 2` queries on a list of length `n`, for every
oracle: the passes scan `n - 1, n - 2, ..., 0` elements and every scanned element costs one
query. -/
theorem countQueries_bubbleSort (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (bubbleSort xs).countQueries oracle = xs.length * (xs.length - 1) / 2 := by
  induction xs using List.bubbleSort.induct (fun x y => oracle (.le x y)) with
  | case1 => simp
  | case2 x xs ih =>
    have hq : (bubbleSort (x :: xs)).countQueries oracle = xs.length +
        (bubbleSort (xs.bubblePass (fun x y => oracle (.le x y)) x).1).countQueries oracle := by
      simp only [bubbleSort, List.bubbleSortM_cons, FreeM.countQueries_bind,
        countQueries_bubblePass, eval_bubblePass, FreeM.countQueries_pure, Nat.add_zero]
    rw [hq, ih, List.length_bubblePass, List.length_cons, ← Nat.choose_two_right,
      ← Nat.choose_two_right, Nat.choose_succ_succ, Nat.choose_one_right]

/-! ## UpperBound and IsSort instances -/

/-- Bubble sort makes at most `n * (n - 1) / 2` queries on inputs of length at most `n`. -/
theorem bubbleSort_upperBound :
    UpperBound (bubbleSort (α := α)) List.length fun n => n * (n - 1) / 2 :=
  UpperBound.of_pointwise
    (fun _ _ h => Nat.div_le_div_right (Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)))
    fun oracle xs => (countQueries_bubbleSort oracle xs).le

/-- Bubble sort is a correct comparison sort. -/
theorem bubbleSort_isSort : IsSort (bubbleSort (α := α)) where
  perm xs oracle := by
    rw [eval_bubbleSort]
    exact List.perm_bubbleSort _ xs
  sorted := by
    intro xs oracle r _ _ _ horacle
    rw [eval_bubbleSort]
    simpa only [horacle, decide_eq_true_eq] using List.pairwise_bubbleSort r xs

end Cslib.Query
