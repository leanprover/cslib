/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Flatten

/-!
# Counting sort

Counting sort orders a list by a key with values in a bounded range, here `Fin k`. One pass over
the input drops each element into the bucket of its key, keeping every bucket in input order, and
the output is the concatenation of the `k` buckets in key order. This is the list form of counting
sort in [Cormen2009, Section 8.2]: rather than counting the elements of each key and computing
prefix sums to find where each element goes, it keeps the elements of each key in a list, which
gives the same output.

The key is an arbitrary function `key : α → Fin k`, such as `Prod.fst` on pairs, so elements with
the same key can still differ. Stability says that such elements leave in the order they arrived.

Counting sort never compares two elements; it only evaluates `key`, which takes `k` values. So it
is not a comparison sort in the sense of `Cslib.Algorithms.Lean.Query.Sort.LowerBound`, and the
lower bound `Cslib.Query.IsSort.lowerBound_infinite` of `⌈log₂ n!⌉` comparisons does not apply to
it.

## Main definitions

- `List.bucketsBy`: distributes a list into `k` buckets by key, in one pass.
- `List.countingSort`: the buckets of a list, concatenated in key order.
- `Cslib.Algorithms.Lean.TimeM.countingSort`: the same algorithm in the `TimeM ℕ` cost monad.

## Main results

- `List.countingSort_eq_flatMap`: the output lists, key by key in increasing order, the input
  elements with that key.
- `List.perm_countingSort`: the output is a permutation of the input.
- `List.pairwise_countingSort`: the output is sorted by key.
- `List.countingSort_stable`: for each key, the output keeps the elements with that key in input
  order.
- `List.sublist_countingSort`: stability as in `List.sublist_mergeSort`, so every sublist of the
  input that is sorted by key is a sublist of the output.
- `List.countingSort_eq_mergeSort`: counting sort computes the same list as `List.mergeSort` by
  key.
- `Cslib.Algorithms.Lean.TimeM.ret_countingSort`: the timed version returns `List.countingSort`.
- `Cslib.Algorithms.Lean.TimeM.time_countingSort`: the timed version charges exactly
  `l.length + k` ticks.

## Cost model

`TimeM.countingSort` counts charged operations: one tick for each element it drops into a bucket
and one for each bucket it emits, so `n + k` ticks on a list of length `n`. Everything else is
free in this model: evaluating `key`, reading or writing a bucket, consing onto a bucket, creating
the `k` empty buckets, turning the vector into a list, and appending each emitted bucket to the
output (which costs the length of the bucket, so `n` in total).

The compiled `List.countingSort` keeps the buckets in a `Vector` that the distributing fold uses
linearly, so the vector is updated in place. If `key` takes constant time, it runs in `O(n + k)`
time in the usual unit-cost model; in general the bound is `O(n + k)` plus the total cost of
evaluating `key`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein,
  *Introduction to Algorithms*][Cormen2009]
-/

@[expose] public section

namespace List

variable {α : Type*} {k : ℕ}

/-! ### Buckets -/

/-- Distributes `l` into `k` buckets in one pass: bucket `i` holds the elements of `l` whose key
is `i`, in the order they occur in `l`. The pass is a right fold that conses each element onto
its bucket, which keeps every bucket in input order. -/
def bucketsBy (key : α → Fin k) (l : List α) : Vector (List α) k :=
  l.foldr (fun a v => v.set (key a) (a :: v[key a])) (Vector.replicate k [])

/-- Every bucket of the empty list is empty. -/
theorem bucketsBy_nil (key : α → Fin k) : ([] : List α).bucketsBy key = Vector.replicate k [] :=
  rfl

/-- The head of a list goes to the front of the bucket of its key. -/
theorem bucketsBy_cons (key : α → Fin k) (a : α) (l : List α) :
    (a :: l).bucketsBy key = (l.bucketsBy key).set (key a) (a :: (l.bucketsBy key)[key a]) :=
  rfl

/-- Bucket `i` holds the elements of `l` with key `i`, in input order. -/
@[simp]
theorem getElem_bucketsBy (key : α → Fin k) (l : List α) (i : Fin k) :
    (l.bucketsBy key)[(i : ℕ)] = l.filter (key · = i) := by
  induction l with
  | nil => rw [bucketsBy_nil, Vector.getElem_replicate, filter_nil]
  | cons a l ih =>
    rw [bucketsBy_cons, Vector.getElem_set, filter_cons]
    by_cases h : key a = i
    · subst h
      simp [ih]
    · have hd : ¬decide (key a = i) = true := by simpa using h
      rw [ite_eq_right (Fin.val_ne_of_ne h), ite_eq_right hd, ih]

/-! ### Counting sort -/

/-- Counting sort: the buckets `l.bucketsBy key`, concatenated in increasing order of key. The
result is sorted by `key` and stable, see `List.pairwise_countingSort` and
`List.countingSort_stable`. -/
def countingSort (key : α → Fin k) (l : List α) : List α :=
  (l.bucketsBy key).toList.flatten

/-- Counting sort of the empty list. -/
@[simp]
theorem countingSort_nil (key : α → Fin k) : ([] : List α).countingSort key = [] := by
  rw [countingSort, bucketsBy_nil, Vector.toList_replicate, flatten_replicate_nil]

/-- Counting sort lists, for each key in increasing order, the elements of `l` with that key in
input order. -/
theorem countingSort_eq_flatMap (key : α → Fin k) (l : List α) :
    l.countingSort key = (finRange k).flatMap (fun i => l.filter (key · = i)) := by
  rw [countingSort, ← Vector.ofFn_getElem (xs := l.bucketsBy key), Vector.toList_ofFn, ofFn_eq_map,
    flatMap_def]
  simp only [getElem_bucketsBy]

/-- Filtering commutes with counting sort. -/
theorem filter_countingSort (key : α → Fin k) (l : List α) (p : α → Bool) :
    (l.countingSort key).filter p = (l.filter p).countingSort key := by
  simp only [countingSort_eq_flatMap, filter_flatMap, filter_filter, Bool.and_comm]

/-- If `key a` is at most every key in `c`, then distributing `a :: c` over a strictly increasing
list of keys `js` that contains `key a` puts `a` in front. -/
private theorem flatMap_filter_cons {key : α → Fin k} {a : α} {c : List α}
    (hc : ∀ b ∈ c, key a ≤ key b) {js : List (Fin k)} (hjs : js.Pairwise (· < ·))
    (ha : key a ∈ js) :
    js.flatMap (fun i => (a :: c).filter (key · = i)) =
      a :: js.flatMap (fun i => c.filter (key · = i)) := by
  induction js with
  | nil => simp at ha
  | cons j js ih =>
    rw [pairwise_cons] at hjs
    rw [flatMap_cons, flatMap_cons]
    by_cases h : key a = j
    · -- `a` lands in bucket `j`; the later buckets have larger keys and do not see it
      have hj : (a :: c).filter (key · = j) = a :: c.filter (key · = j) :=
        filter_cons_of_pos (by simpa using h)
      have hrest : js.flatMap (fun i => (a :: c).filter (key · = i)) =
          js.flatMap (fun i => c.filter (key · = i)) :=
        flatMap_congr fun i hi =>
          filter_cons_of_neg (by simpa [h] using Fin.ne_of_lt (hjs.1 i hi))
      rw [hj, hrest, cons_append]
    · -- bucket `j` lies below `key a`, so it is empty
      have ha' : key a ∈ js := (mem_cons.1 ha).resolve_left h
      have hlt : j < key a := hjs.1 _ ha'
      have hj : (a :: c).filter (key · = j) = c.filter (key · = j) :=
        filter_cons_of_neg (by simpa using h)
      have hc' : c.filter (key · = j) = [] := filter_eq_nil_iff.2 fun b hb => by
        simpa using Fin.ne_of_gt (Fin.lt_of_lt_of_le hlt (hc b hb))
      simp only [hj, hc', nil_append, ih hjs.2 ha']

/-- Counting sort leaves a list that is already sorted by key unchanged. -/
theorem Pairwise.countingSort_eq {key : α → Fin k} {l : List α}
    (h : l.Pairwise (fun a b => key a ≤ key b)) : l.countingSort key = l := by
  induction l with
  | nil => exact countingSort_nil key
  | cons a l ih =>
    rw [pairwise_cons] at h
    rw [countingSort_eq_flatMap,
      flatMap_filter_cons h.1 (pairwise_lt_finRange k) (mem_finRange (key a)),
      ← countingSort_eq_flatMap key l, ih h.2]

/-- Counting sort sorts by key. -/
theorem pairwise_countingSort (key : α → Fin k) (l : List α) :
    (l.countingSort key).Pairwise (fun a b => key a ≤ key b) := by
  rw [countingSort_eq_flatMap, pairwise_flatMap]
  refine ⟨fun i _ => pairwise_of_forall_mem_list fun a ha b hb => ?_,
    (pairwise_lt_finRange k).imp fun hij a ha b hb => ?_⟩
  · -- inside one bucket all keys are equal
    rw [mem_filter, decide_eq_true_eq] at ha hb
    exact Fin.le_of_eq (ha.2.trans hb.2.symm)
  · -- an earlier bucket has a smaller key
    rw [mem_filter, decide_eq_true_eq] at ha hb
    have hab : key a < key b := by
      rw [ha.2, hb.2]
      exact hij
    exact Fin.le_of_lt hab

/-- Counting sort is stable: the elements with key `i` occur in the output in the same order as
in the input. -/
theorem countingSort_stable (key : α → Fin k) (l : List α) (i : Fin k) :
    (l.countingSort key).filter (key · = i) = l.filter (key · = i) := by
  rw [filter_countingSort]
  refine Pairwise.countingSort_eq (pairwise_of_forall_mem_list fun a ha b hb => ?_)
  rw [mem_filter, decide_eq_true_eq] at ha hb
  exact Fin.le_of_eq (ha.2.trans hb.2.symm)

/-- Counting sort permutes its input. -/
theorem perm_countingSort (key : α → Fin k) (l : List α) : l.countingSort key ~ l := by
  classical
  refine perm_iff_count.2 fun a => ?_
  -- `a` only occurs among the elements with key `key a`, and those agree on both sides
  have h (l' : List α) : count a (l'.filter (key · = key a)) = count a l' :=
    count_filter (decide_eq_true rfl)
  rw [← h (l.countingSort key), countingSort_stable, h]

/-- Counting sort preserves the length. -/
@[simp]
theorem length_countingSort (key : α → Fin k) (l : List α) :
    (l.countingSort key).length = l.length :=
  (perm_countingSort key l).length_eq

/-- Counting sort preserves membership. -/
@[simp]
theorem mem_countingSort {key : α → Fin k} {l : List α} {a : α} :
    a ∈ l.countingSort key ↔ a ∈ l :=
  (perm_countingSort key l).mem_iff

/-- Counting sort is monotone for the sublist order. -/
protected theorem Sublist.countingSort (key : α → Fin k) {c l : List α} (h : c <+ l) :
    c.countingSort key <+ l.countingSort key := by
  rw [countingSort_eq_flatMap, countingSort_eq_flatMap]
  exact Sublist.flatMap_right _ fun i _ => h.filter _

/-- Counting sort is stable in the form of `List.sublist_mergeSort`: a sublist of `l` that is
sorted by key is a sublist of the output. -/
theorem sublist_countingSort {key : α → Fin k} {c l : List α}
    (hc : c.Pairwise (fun a b => key a ≤ key b)) (h : c <+ l) : c <+ l.countingSort key := by
  have h' := h.countingSort key
  rwa [hc.countingSort_eq] at h'

/-- Counting sort computes the same list as `List.mergeSort` ordered by key. -/
theorem countingSort_eq_mergeSort (key : α → Fin k) (l : List α) :
    l.countingSort key = l.mergeSort (fun a b => key a ≤ key b) := by
  have trans (a b c : α) (hab : decide (key a ≤ key b)) (hbc : decide (key b ≤ key c)) :
      decide (key a ≤ key c) :=
    decide_eq_true (Fin.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have total (a b : α) : decide (key a ≤ key b) || decide (key b ≤ key a) := by
    simpa using Fin.le_total (key a) (key b)
  have hsorted :
      (l.mergeSort (fun a b => key a ≤ key b)).Pairwise (fun a b => key a ≤ key b) := by
    simpa using pairwise_mergeSort trans total l
  -- both sides are sorted by key, so it is enough to compare them key by key
  rw [← hsorted.countingSort_eq, countingSort_eq_flatMap, countingSort_eq_flatMap]
  refine flatMap_congr fun i _ => ?_
  -- the elements with key `i` form a sorted sublist of `l`, which `mergeSort` keeps in order
  have hfib : (l.filter (key · = i)).Pairwise (fun a b => decide (key a ≤ key b)) :=
    pairwise_of_forall_mem_list fun a ha b hb => by
      rw [mem_filter, decide_eq_true_eq] at ha hb
      exact decide_eq_true (Fin.le_of_eq (ha.2.trans hb.2.symm))
  have hidem : (l.filter (key · = i)).filter (key · = i) = l.filter (key · = i) :=
    filter_eq_self.2 fun a ha => (mem_filter.1 ha).2
  have hsub := (sublist_mergeSort trans total hfib filter_sublist).filter (key · = i)
  rw [hidem] at hsub
  exact hsub.eq_of_length ((mergeSort_perm l _).filter _).length_eq.symm

end List

/-! ### Counting sort with its cost -/

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type*} {k : ℕ}

/-- Counting sort in `TimeM ℕ`. The first pass charges one tick for each element it drops into
its bucket, the second pass one tick for each bucket it emits; everything else is free (see the
cost model in the module docstring). -/
def countingSort (key : α → Fin k) (l : List α) : TimeM ℕ (List α) := do
  let buckets : Vector (List α) k ←
    l.foldrM (fun a v => do ✓ return v.set (key a) (a :: v[key a])) (Vector.replicate k [])
  buckets.toList.foldrM (fun bucket out => do ✓ return bucket ++ out) []

/-- The timed counting sort returns `List.countingSort`. -/
@[simp, grind =]
theorem ret_countingSort (key : α → Fin k) (l : List α) :
    ⟪countingSort key l⟫ = l.countingSort key := by
  rw [countingSort, ret_bind, ret_foldrM_tick, ret_foldrM_tick, List.foldr_append_eq_append,
    List.map_id', List.append_nil]
  rfl

/-- The timed counting sort charges `l.length + k` ticks: one per element and one per bucket. -/
@[simp, grind =]
theorem time_countingSort (key : α → Fin k) (l : List α) :
    (countingSort key l).time = l.length + k := by
  rw [countingSort, time_bind, time_foldrM_tick, time_foldrM_tick, Vector.length_toList]
  simp only [Nat.nsmul_eq_mul, Nat.mul_one]

end Cslib.Algorithms.Lean.TimeM
