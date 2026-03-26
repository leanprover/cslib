/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai, Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.IsSort
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Defs
import Mathlib.Data.List.Sort
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Nat.Log

/-! # Merge Sort: Correctness and Upper Bound

Proofs that `mergeSort` is a correct comparison sort and uses at most `n * ⌈log₂ n⌉` queries.
All proofs are by plain equational reasoning on `Prog.eval` and `Prog.queriesOn`.
-/

open Cslib.Query

public section

namespace Cslib.Query

variable {α : Type}

-- ## Split lemmas

theorem split_perm : ∀ (xs : List α),
    ((split xs).1 ++ (split xs).2).Perm xs
  | [] => List.Perm.refl _
  | [_] => List.Perm.refl _
  | x :: y :: zs => by
    simp only [split_cons_cons]
    show ((x :: (split zs).1) ++ (y :: (split zs).2)).Perm (x :: y :: zs)
    rw [List.cons_append]
    refine List.Perm.cons _ ?_
    -- goal: ((split zs).1 ++ y :: (split zs).2).Perm (y :: zs)
    exact (List.perm_middle).trans (List.Perm.cons _ (split_perm zs))

theorem split_lengths_add (xs : List α) :
    (split xs).1.length + (split xs).2.length = xs.length := by
  simp [split_fst_length_eq, split_snd_length_eq]; omega

-- ## Evaluation simp lemmas for merge

@[simp] theorem eval_merge_nil_left (oracle : {ι : Type} → LEQuery α ι → ι) (ys : List α) :
    (merge ([] : List α) ys).eval oracle = ys := by
  simp [merge]

@[simp] theorem eval_merge_nil_right (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (merge xs ([] : List α)).eval oracle = xs := by
  cases xs <;> simp [merge]

@[simp] theorem eval_merge_cons_cons (oracle : {ι : Type} → LEQuery α ι → ι)
    (x : α) (xs' : List α) (y : α) (ys' : List α) :
    (merge (x :: xs') (y :: ys')).eval oracle =
      if oracle (.le x y)
      then x :: (merge xs' (y :: ys')).eval oracle
      else y :: (merge (x :: xs') ys').eval oracle := by
  simp [merge, LEQuery.ask]
  split <;> simp_all

-- ## Evaluation simp lemmas for mergeSort

@[simp] theorem eval_mergeSort_nil (oracle : {ι : Type} → LEQuery α ι → ι) :
    (mergeSort (α := α) []).eval oracle = [] := by
  simp [mergeSort]

@[simp] theorem eval_mergeSort_singleton (oracle : {ι : Type} → LEQuery α ι → ι) (x : α) :
    (mergeSort [x]).eval oracle = [x] := by
  simp [mergeSort]

@[simp] theorem eval_mergeSort_cons_cons (oracle : {ι : Type} → LEQuery α ι → ι)
    (x y : α) (zs : List α) :
    (mergeSort (x :: y :: zs)).eval oracle =
      (merge
        ((mergeSort (split (x :: y :: zs)).1).eval oracle)
        ((mergeSort (split (x :: y :: zs)).2).eval oracle)).eval oracle := by
  simp [mergeSort]

-- ## Permutation proofs

theorem merge_perm (oracle : {ι : Type} → LEQuery α ι → ι) (xs ys : List α) :
    ((merge xs ys).eval oracle).Perm (xs ++ ys) := by
  induction xs, ys using merge.induct (α := α) with
  | case1 ys => simp
  | case2 xs => simp
  | case3 x xs' y ys' ih_true ih_false =>
    simp only [eval_merge_cons_cons]
    split
    · exact List.Perm.cons _ ih_true
    · -- goal: (y :: (merge (x :: xs') ys').eval oracle).Perm (x :: xs' ++ y :: ys')
      -- ih: ((merge (x :: xs') ys').eval oracle).Perm ((x :: xs') ++ ys')
      exact (List.Perm.cons _ ih_false).trans List.perm_middle.symm

theorem mergeSort_perm (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    ((mergeSort xs).eval oracle).Perm xs := by
  induction xs using mergeSort.induct (α := α) with
  | case1 => simp
  | case2 x => simp
  | case3 x y zs ih_l ih_r =>
    simp only [eval_mergeSort_cons_cons]
    exact (merge_perm oracle _ _).trans ((ih_l.append ih_r).trans (split_perm _))

-- ## Sortedness proofs

/-- If `l` is a permutation of `xs ++ ys`, and `r a` holds for all elements of `xs` and `ys`,
    then `r a` holds for all elements of `l`. -/
private theorem forall_mem_of_perm_append {r : α → Prop} {l xs ys : List α}
    (hperm : l.Perm (xs ++ ys))
    (hxs : ∀ z ∈ xs, r z) (hys : ∀ z ∈ ys, r z) :
    ∀ z ∈ l, r z := by
  intro z hz
  rcases List.mem_append.mp (hperm.mem_iff.mp hz) with h | h
  · exact hxs z h
  · exact hys z h

theorem merge_sorted
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (xs ys : List α) (hxs : xs.Pairwise r) (hys : ys.Pairwise r) :
    ((merge xs ys).eval oracle).Pairwise r := by
  induction xs, ys using merge.induct (α := α) with
  | case1 ys => simpa
  | case2 xs => simpa
  | case3 x xs' y ys' ih_true ih_false =>
    simp only [eval_merge_cons_cons, horacle]
    have hxs' := hxs.of_cons
    have hys' := hys.of_cons
    split
    next h =>
      have hle : r x y := by simpa [decide_eq_true_eq] using h
      refine List.pairwise_cons.mpr ⟨?_, ih_true hxs' hys⟩
      exact forall_mem_of_perm_append (merge_perm oracle xs' (y :: ys'))
        (fun _ hz => List.rel_of_pairwise_cons hxs hz)
        (fun z hz => by
          rcases List.mem_cons.mp hz with rfl | h
          · exact hle
          · exact _root_.trans hle (List.rel_of_pairwise_cons hys h))
    next h =>
      have hle : ¬ r x y := by simpa [decide_eq_true_eq] using h
      have hyx : r y x := (Std.Total.total y x).resolve_right hle
      refine List.pairwise_cons.mpr ⟨?_, ih_false hxs hys'⟩
      exact forall_mem_of_perm_append (merge_perm oracle (x :: xs') ys')
        (fun z hz => by
          rcases List.mem_cons.mp hz with rfl | h
          · exact hyx
          · exact _root_.trans hyx (List.rel_of_pairwise_cons hxs h))
        (fun _ hz => List.rel_of_pairwise_cons hys hz)

theorem mergeSort_sorted
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (xs : List α) :
    ((mergeSort xs).eval oracle).Pairwise r := by
  induction xs using mergeSort.induct (α := α) with
  | case1 => simp
  | case2 x => simp
  | case3 x y zs ih_l ih_r =>
    simp only [eval_mergeSort_cons_cons]
    exact merge_sorted r oracle horacle _ _ ih_l ih_r

-- ## Query count simp lemmas

@[simp] theorem queriesOn_merge_nil_left (oracle : {ι : Type} → LEQuery α ι → ι) (ys : List α) :
    (merge ([] : List α) ys).queriesOn oracle = 0 := by
  simp [merge]

@[simp] theorem queriesOn_merge_nil_right (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (merge xs ([] : List α)).queriesOn oracle = 0 := by
  cases xs <;> simp [merge]

@[simp] theorem queriesOn_merge_cons_cons (oracle : {ι : Type} → LEQuery α ι → ι)
    (x : α) (xs' : List α) (y : α) (ys' : List α) :
    (merge (x :: xs') (y :: ys')).queriesOn oracle =
      1 + if oracle (.le x y)
      then (merge xs' (y :: ys')).queriesOn oracle
      else (merge (x :: xs') ys').queriesOn oracle := by
  simp [merge, LEQuery.ask]
  split <;> simp_all

@[simp] theorem queriesOn_mergeSort_nil (oracle : {ι : Type} → LEQuery α ι → ι) :
    (mergeSort (α := α) []).queriesOn oracle = 0 := by
  simp [mergeSort]

@[simp] theorem queriesOn_mergeSort_singleton (oracle : {ι : Type} → LEQuery α ι → ι) (x : α) :
    (mergeSort [x]).queriesOn oracle = 0 := by
  simp [mergeSort]

@[simp] theorem queriesOn_mergeSort_cons_cons (oracle : {ι : Type} → LEQuery α ι → ι)
    (x y : α) (zs : List α) :
    (mergeSort (x :: y :: zs)).queriesOn oracle =
      (mergeSort (split (x :: y :: zs)).1).queriesOn oracle +
      ((mergeSort (split (x :: y :: zs)).2).queriesOn oracle +
       (merge ((mergeSort (split (x :: y :: zs)).1).eval oracle)
              ((mergeSort (split (x :: y :: zs)).2).eval oracle)).queriesOn oracle) := by
  simp [mergeSort]

-- ## Query count proofs

theorem merge_queriesOn_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs ys : List α) :
    (merge xs ys).queriesOn oracle ≤ xs.length + ys.length := by
  induction xs, ys using merge.induct (α := α) with
  | case1 ys => simp
  | case2 xs => simp
  | case3 x xs' y ys' ih_true ih_false =>
    simp only [queriesOn_merge_cons_cons, List.length_cons]
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

theorem mergeSort_queriesOn_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs : List α) :
    (mergeSort xs).queriesOn oracle ≤ xs.length * Nat.clog 2 xs.length := by
  induction xs using mergeSort.induct (α := α) with
  | case1 => simp [mergeSort]
  | case2 x => simp [mergeSort]
  | case3 x y zs ih_l ih_r =>
    simp only [queriesOn_mergeSort_cons_cons]
    have hml := merge_queriesOn_le oracle
      ((mergeSort (split (x :: y :: zs)).1).eval oracle)
      ((mergeSort (split (x :: y :: zs)).2).eval oracle)
    rw [(mergeSort_perm oracle (split (x :: y :: zs)).1).length_eq,
        (mergeSort_perm oracle (split (x :: y :: zs)).2).length_eq,
        split_fst_length_eq, split_snd_length_eq] at hml
    rw [split_fst_length_eq] at ih_l
    rw [split_snd_length_eq] at ih_r
    exact Nat.le_trans (Nat.add_le_add ih_l (Nat.add_le_add ih_r hml))
      (mergeSort_bound _ (by simp only [List.length_cons]; omega))

-- ## UpperBound and IsSort instances

public theorem mergeSort_upperBound :
    UpperBound (mergeSort (α := α)) List.length (fun n => n * Nat.clog 2 n) := by
  intro oracle n x hle
  exact Nat.le_trans (mergeSort_queriesOn_le oracle x)
    (Nat.mul_le_mul hle (Nat.clog_mono_right 2 hle))

public theorem mergeSort_isSort : IsSort (mergeSort (α := α)) where
  perm xs oracle := mergeSort_perm oracle xs
  sorted := by
    intro xs oracle r _ _ _ horacle
    exact mergeSort_sorted r oracle horacle xs

end Cslib.Query

end -- public section
