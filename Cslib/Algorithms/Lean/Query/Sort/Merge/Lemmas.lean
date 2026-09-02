/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas, Sorrachai Yingchareonthawornchai
-/
module

public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.IsSort
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Defs
public import Mathlib.Data.Nat.Log
import all Init.Data.List.Sort.Basic

/-! # Merge Sort: Correctness and Upper Bound

Proofs that `mergeSort` is a correct comparison sort and uses at most `n * ⌈log₂ n⌉` queries.

`eval_mergeSort` identifies the query program with `List.mergeSort`: evaluating against any
oracle produces the same list as `List.mergeSort` with the comparator induced by the oracle.
Correctness properties (permutation, sortedness) transfer directly from the `List.mergeSort`
API. The query bound is proved by equational reasoning on `FreeM.countQueries`, which has no
`List` counterpart.
-/

open Cslib Cslib.Query
open scoped List

public section

namespace Cslib.Query

variable {α : Type}

/-! ## Evaluation -/

/-- Evaluating the query-based merge agrees with `List.merge` using the relation supplied
by the oracle. -/
@[simp] theorem eval_merge (oracle : {ι : Type} → LEQuery α ι → ι) (xs ys : List α) :
    (merge xs ys).eval oracle = xs.merge ys (fun a b => oracle (.le a b)) := by
  induction xs, ys using merge.induct (α := α) with
  | case1 ys => simp [merge]
  | case2 xs => cases xs <;> simp [merge]
  | case3 x xs' y ys' ih_true ih_false =>
    rw [List.cons_merge_cons]
    simp [merge]
    split <;> simp_all

-- Proposed upstream as `List.mergeSort_append` in
-- https://github.com/leanprover/lean4/pull/14995; replace this private helper once the
-- toolchain includes it. Until then we derive it from the auto-generated equation lemma
-- `List.mergeSort.eq_3`, which is only visible here thanks to the (non-public)
-- `import all Init.Data.List.Sort.Basic` above.
private theorem list_mergeSort_append {le : α → α → Bool} (l₁ l₂ : List α)
    (h₁ : l₂.length ≤ l₁.length) (h₂ : l₁.length ≤ l₂.length + 1) :
    (l₁ ++ l₂).mergeSort le = List.merge (l₁.mergeSort le) (l₂.mergeSort le) le := by
  match l₁, l₂ with
  | [], l₂ =>
    obtain rfl : l₂ = [] := by simp_all
    simp
  | [a], [] => simp
  | [a], [b] =>
    simp only [List.mergeSort_singleton, List.singleton_append]
    rw [List.mergeSort.eq_3]
    simp
  | [a], b :: c :: l₂ => simp at h₁
  | a :: b :: l₁, l₂ =>
    rw [List.cons_append, List.cons_append, List.mergeSort.eq_3]
    have hlen : (l₁.length + l₂.length + 1 + 1 + 1) / 2 = l₁.length + 2 := by
      simp only [List.length_cons] at h₁ h₂
      omega
    simp only [List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      List.length_cons, List.length_append, hlen]
    congr 2 <;> simp

private theorem list_mergeSort_cons_cons {le : α → α → Bool} (x y : α) (zs : List α) :
    (x :: y :: zs).mergeSort le =
      List.merge ((split (x :: y :: zs)).1.mergeSort le)
        ((split (x :: y :: zs)).2.mergeSort le) le := by
  conv_lhs => rw [← split_fst_append_split_snd (x :: y :: zs)]
  rw [list_mergeSort_append]
  · simp
    omega
  · simp
    omega

/-- Evaluating query-based merge sort agrees with `List.mergeSort` using the relation
supplied by the oracle.

This is the essential correctness statement: it identifies the query program as *the*
merge sort operation, so correctness properties (permutation, sortedness, stability)
transfer directly from the `List.mergeSort` API rather than being restated here. -/
@[simp] theorem eval_mergeSort (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (mergeSort xs).eval oracle = xs.mergeSort (fun a b => oracle (.le a b)) := by
  induction xs using mergeSort.induct (α := α) with
  | case1 => simp [mergeSort]
  | case2 x => simp [mergeSort]
  | case3 x y zs halves ih_l ih_r =>
    rw [list_mergeSort_cons_cons]
    simp [halves, split] at ih_l ih_r
    simp [mergeSort, split, ih_l, ih_r]

/-! ## Correctness, transferred from the `List.mergeSort` API -/

theorem mergeSort_perm (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (mergeSort xs).eval oracle ~ xs := by
  rw [eval_mergeSort]
  exact List.mergeSort_perm xs _

theorem mergeSort_sorted
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (xs : List α) :
    ((mergeSort xs).eval oracle).Pairwise r := by
  rw [eval_mergeSort]
  refine (List.pairwise_mergeSort ?_ ?_ xs).imp (by simp [horacle])
  · intro a b c hab hbc
    simp only [horacle, decide_eq_true_eq] at hab hbc ⊢
    exact _root_.trans hab hbc
  · intro a b
    simp only [horacle, Bool.or_eq_true, decide_eq_true_eq]
    exact Std.Total.total a b

/-! ## Query count simp lemmas -/

@[simp] theorem countQueries_merge_nil_left (oracle : {ι : Type} → LEQuery α ι → ι) (ys : List α) :
    (merge ([] : List α) ys).countQueries oracle = 0 := by
  simp [merge]

@[simp] theorem countQueries_merge_nil_right (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (merge xs ([] : List α)).countQueries oracle = 0 := by
  cases xs <;> simp [merge]

@[simp] theorem countQueries_merge_cons_cons (oracle : {ι : Type} → LEQuery α ι → ι)
    (x : α) (xs' : List α) (y : α) (ys' : List α) :
    (merge (x :: xs') (y :: ys')).countQueries oracle =
      1 + if oracle (.le x y)
      then (merge xs' (y :: ys')).countQueries oracle
      else (merge (x :: xs') ys').countQueries oracle := by
  simp [merge]
  split <;> simp_all

@[simp] theorem countQueries_mergeSort_nil (oracle : {ι : Type} → LEQuery α ι → ι) :
    (mergeSort (α := α) []).countQueries oracle = 0 := by
  simp [mergeSort]

@[simp] theorem countQueries_mergeSort_singleton (oracle : {ι : Type} → LEQuery α ι → ι) (x : α) :
    (mergeSort [x]).countQueries oracle = 0 := by
  simp [mergeSort]

@[simp] theorem countQueries_mergeSort_cons_cons (oracle : {ι : Type} → LEQuery α ι → ι)
    (x y : α) (zs : List α) :
    (mergeSort (x :: y :: zs)).countQueries oracle =
      (mergeSort (split (x :: y :: zs)).1).countQueries oracle +
      ((mergeSort (split (x :: y :: zs)).2).countQueries oracle +
       (merge ((split (x :: y :: zs)).1.mergeSort fun a b => oracle (.le a b))
              ((split (x :: y :: zs)).2.mergeSort fun a b => oracle (.le a b))).countQueries
         oracle) := by
  simp [mergeSort]

/-! ## Query count proofs -/

theorem merge_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs ys : List α) :
    (merge xs ys).countQueries oracle ≤ xs.length + ys.length := by
  induction xs, ys using merge.induct (α := α) with
  | case1 ys => simp
  | case2 xs => simp
  | case3 x xs' y ys' ih_true ih_false =>
    simp only [countQueries_merge_cons_cons, List.length_cons]
    split <;> simp_all <;> omega

/-- The key arithmetic inequality for the merge sort recurrence:
    `⌈n/2⌉ * clog(⌈n/2⌉) + ⌊n/2⌋ * clog(⌊n/2⌋) + n ≤ n * clog(n)`. -/
private theorem mergeSort_bound (n : ℕ) (hn : 2 ≤ n) :
    ((n + 1) / 2) * Nat.clog 2 ((n + 1) / 2) +
      (n / 2 * Nat.clog 2 (n / 2) + ((n + 1) / 2 + n / 2)) ≤
      n * Nat.clog 2 n := by
  have hclog := Nat.clog_of_one_lt (by omega : (1 : Nat) < 2) hn
  have hceil : Nat.clog 2 ((n + 1) / 2) + 1 ≤ Nat.clog 2 n := le_of_eq hclog.symm
  have hfloor : Nat.clog 2 (n / 2) + 1 ≤ Nat.clog 2 n :=
    (Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1).trans hceil
  have hsum : (n + 1) / 2 + n / 2 = n := by omega
  have h1 := Nat.mul_le_mul_left ((n + 1) / 2) hceil
  have h2 := Nat.mul_le_mul_left (n / 2) hfloor
  rw [Nat.mul_succ] at h1 h2
  calc _ = ((n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n + 1) / 2) +
           (n / 2 * Nat.clog 2 (n / 2) + n / 2) := by omega
    _ ≤ (n + 1) / 2 * Nat.clog 2 n + n / 2 * Nat.clog 2 n := Nat.add_le_add h1 h2
    _ = ((n + 1) / 2 + n / 2) * Nat.clog 2 n := (Nat.add_mul ..).symm
    _ = n * Nat.clog 2 n := by rw [hsum]

theorem mergeSort_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs : List α) :
    (mergeSort xs).countQueries oracle ≤ xs.length * Nat.clog 2 xs.length := by
  induction xs using mergeSort.induct (α := α) with
  | case1 => simp [mergeSort]
  | case2 x => simp [mergeSort]
  | case3 x y zs halves ih_l ih_r =>
    simp only [countQueries_mergeSort_cons_cons]
    have hml := merge_countQueries_le oracle
      ((split (x :: y :: zs)).1.mergeSort fun a b => oracle (.le a b))
      ((split (x :: y :: zs)).2.mergeSort fun a b => oracle (.le a b))
    rw [List.length_mergeSort, List.length_mergeSort,
        split_fst_length_eq, split_snd_length_eq] at hml
    rw [split_fst_length_eq] at ih_l
    rw [split_snd_length_eq] at ih_r
    exact Nat.le_trans (Nat.add_le_add ih_l (Nat.add_le_add ih_r hml))
      (mergeSort_bound _ (by simp only [List.length_cons]; omega))

/-! ## UpperBound and IsSort instances -/

theorem mergeSort_upperBound :
    UpperBound (mergeSort (α := α)) List.length (fun n => n * Nat.clog 2 n) :=
  UpperBound.of_pointwise
    (fun _ _ h => Nat.mul_le_mul h (Nat.clog_mono_right 2 h))
    fun oracle xs => mergeSort_countQueries_le oracle xs

theorem mergeSort_isSort : IsSort (mergeSort (α := α)) where
  perm xs oracle := mergeSort_perm oracle xs
  sorted := by
    intro xs oracle r _ _ _ horacle
    exact mergeSort_sorted r oracle horacle xs

end Cslib.Query
