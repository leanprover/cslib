/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Data.Nat.Segment
public import Cslib.Foundations.Data.OmegaSequence.Init

/-!
# Flattening an infinite sequence of lists

Given `ls : ωSequence (List α)`, `ls.flatten` is the infinite sequence formed by
concatenating all members of `ls`.  For this definition to make proper sense,
we will consistently assume that all lists in `ls` are nonempty.  Furthermore,
in order to simplify the definition, we will also assume [Inhabited α].
-/

@[expose] public section

namespace Cslib

open Nat Function Set

namespace ωSequence

universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}

/-- Given an ω-sequence `ls` of lists, `ls.cumLen k` is the cumulative sum
of `(ls k).length` for `k = 0, ..., k - 1`. -/
def cumLen (ls : ωSequence (List α)) : ℕ → ℕ
  | 0 => 0
  | k + 1 => ls.cumLen k + (ls k).length

/- The following are some helper theorems about `ls.cumLen`. -/

@[simp, scoped grind =]
theorem cumLen_zero {ls : ωSequence (List α)} :
    ls.cumLen 0 = 0 :=
  rfl

@[scoped grind =]
theorem cumLen_succ (ls : ωSequence (List α)) (k : ℕ) :
    ls.cumLen (k + 1) = ls.cumLen k + (ls k).length :=
  rfl

theorem cumLen_one_add_drop (ls : ωSequence (List α)) (k : ℕ) :
    ls.cumLen (1 + k) = (ls 0).length + (ls.drop 1).cumLen k := by
  induction k <;> grind

/-- If all lists in `ls` are nonempty, then `ls.cumLen` is strictly monotonic. -/
theorem cumLen_strictMono {ls : ωSequence (List α)} (h_ls : ∀ k, 0 < (ls k).length) :
    StrictMono ls.cumLen := by
  grind [strictMono_nat_of_lt_succ]

@[simp, scoped grind =]
theorem cumLen_segment_zero {ls : ωSequence (List α)} (h_ls : ∀ k, 0 < (ls k).length)
    (n : ℕ) (h_n : n < (ls 0).length) : segment ls.cumLen n = 0 := by
  have h0 : ls.cumLen 0 ≤ n := by simp [cumLen_zero]
  have h1 : n < ls.cumLen 1 := by simpa [cumLen_succ, cumLen_zero]
  exact segment_range_val (cumLen_strictMono h_ls) h0 h1

theorem cumLen_segment_one_add {ls : ωSequence (List α)} (h_ls : ∀ k, 0 < (ls k).length)
    (n : ℕ) (h_n : (ls 0).length ≤ n) :
    segment ls.cumLen n = 1 + segment (ls.drop 1).cumLen (n - (ls 0).length) := by
  have h_mono := cumLen_strictMono (ls := ls.drop 1) (fun k => h_ls (k + 1))
  have h_lower := segment_lower_bound h_mono rfl (n - (ls 0).length)
  have h_upper := segment_upper_bound h_mono rfl (n - (ls 0).length)
  apply segment_range_val (cumLen_strictMono h_ls) <;>
    simp only [Nat.add_assoc, cumLen_one_add_drop] <;> lia

/-- Given an ω-sequence `ls` of lists, `ls.flatten` is the infinite sequence
formed by the concatenation of all of them.  For the definition to make proper
sense, we will consistently assume that all lists in `ls` are nonempty. -/
noncomputable def flatten [Inhabited α] (ls : ωSequence (List α)) : ωSequence α :=
  fun n ↦ (ls (segment ls.cumLen n))[n - ls.cumLen (segment ls.cumLen n)]!

theorem flatten_def [Inhabited α] (ls : ωSequence (List α)) (n : ℕ) :
    flatten ls n = (ls (segment ls.cumLen n))[n - ls.cumLen (segment ls.cumLen n)]! :=
  rfl

theorem flatten_get_add [Inhabited α] (ls : ωSequence (List α)) {n k : ℕ}
    (hk : k < (ls n).length) (hpos : ∀ n, 0 < (ls n).length) :
    ls.flatten (ls.cumLen n + k) = (ls n)[k] := by
  have := segment_range_val (cumLen_strictMono hpos) (ls.cumLen n |>.le_add_right k)
    (by lia [cumLen_succ])
  simp [flatten_def, this, hk]

theorem flatten_get_cumLen [Inhabited α] (ls : ωSequence (List α)) {n : ℕ}
    (hpos : ∀ n, 0 < (ls n).length) : ls.flatten (ls.cumLen n) = (ls n)[0]'(hpos n) :=
  ls.flatten_get_add (hpos n) hpos

/-- `ls.flatten` equals the concatenation of `ls.head` and `ls.tail.flatten`. -/
@[simp, scoped grind =]
theorem cons_flatten [Inhabited α] {ls : ωSequence (List α)} (h_ls : ∀ k, 0 < (ls k).length) :
    ls.head ++ω ls.tail.flatten = ls.flatten := by
  ext n; rw [flatten_def, head, tail_eq_drop]
  obtain (h_n | h_n) : n < (ls 0).length ∨ (ls 0).length ≤ n := n.lt_or_ge (ls 0).length
  · simp [get_append_left _ _ _ h_n, cumLen_segment_zero h_ls n h_n, cumLen_zero,
      getElem?_pos (ls 0) n h_n]
  · simp [get_append_right' h_n, flatten_def, cumLen_segment_one_add h_ls _ h_n,
      cumLen_one_add_drop]
    grind

/-- `ls.flatten` equals the concatenation of `(ls.take n).flatten` and `(ls.drop n).flatten`. -/
@[simp, scoped grind =]
theorem append_flatten [Inhabited α] {ls : ωSequence (List α)} (h_ls : ∀ k, 0 < (ls k).length)
    (n : ℕ) : (ls.take n).flatten ++ω (ls.drop n).flatten = ls.flatten := by
  induction n generalizing ls <;> grind [tail_eq_drop, take_succ]

/-- The sum of `List.map List.length (take n ls)` is `ls.cumLen n`. -/
@[simp, scoped grind =]
theorem map_length_take_sum {ls : ωSequence (List α)} (n : ℕ) :
    (List.map List.length (take n ls)).sum = ls.cumLen n := by
  induction n <;> grind [take_succ']

/-- In fact, `(ls.take n).flatten` is `ls.flatten.take (ls.cumLen n)`
and `(ls.drop n).flatten` is `ls.flatten.drop (ls.cumLen n)`. -/
theorem flatten_take_drop [Inhabited α]
    {ls : ωSequence (List α)} (h_ls : ∀ k, 0 < (ls k).length) (n : ℕ) :
    (ls.take n).flatten = ls.flatten.take (ls.cumLen n) ∧
    (ls.drop n).flatten = ls.flatten.drop (ls.cumLen n) := by
  apply append_left_right_injective
  · rw [append_flatten h_ls n, append_take_drop (ls.cumLen n) ls.flatten]
  · simp

theorem flatten_take [Inhabited α]
    {ls : ωSequence (List α)} (h_ls : ∀ k, 0 < (ls k).length) (n : ℕ) :
    (ls.take n).flatten = ls.flatten.take (ls.cumLen n) :=
  (flatten_take_drop h_ls n).1

theorem flatten_drop [Inhabited α]
    {ls : ωSequence (List α)} (h_ls : ∀ k, 0 < (ls k).length) (n : ℕ) :
    (ls.drop n).flatten = ls.flatten.drop (ls.cumLen n) :=
  (flatten_take_drop h_ls n).2

/-- `ls n` is the segment from position `ls.cumLen n` to position `ls.cumLen (n + 1) - 1`
of `ls.flatten` -/
@[simp, scoped grind =]
theorem extract_flatten [Inhabited α] {ls : ωSequence (List α)} (h_ls : ∀ k, 0 < (ls k).length)
    (n : ℕ) : ls.flatten.extract (ls.cumLen n) (ls.cumLen (n + 1)) = ls n := by
  have h_ls' : ∀ k, 0 < (ls.drop n k).length := by grind
  have h_drop := flatten_drop h_ls n
  have h_take := flatten_take h_ls' 1
  grind [extract_eq_drop_take]

/-- Distributivity of "forall" over `flatten`. -/
theorem forall_flatten_iff [Inhabited α] {ls : ωSequence (List α)} (h_ls : ∀ k, 0 < (ls k).length)
    (p : α → Prop) : (∀ n, p (ls.flatten n)) ↔ ∀ k, (ls k).Forall p := by
  constructor
  · simp only [List.forall_iff_forall_mem, List.forall_mem_iff_getElem, ← extract_flatten h_ls]
    grind
  · have := segment_upper_bound (cumLen_strictMono h_ls)
    grind [List.forall_iff_forall_mem, flatten_def]

/-- Given an ω-sequence `s` and a function `f : ℕ → ℕ`, `s.toSegs f` is the ω-sequence
whose `n`-th element is the list `s.extract (f n) (f (n + 1))`.  In all its uses, the
function `f` will always be assumed to be strictly monotonic with `f 0 = 0`. -/
def toSegs (s : ωSequence α) (f : ℕ → ℕ) : ωSequence (List α) :=
  fun n ↦ s.extract (f n) (f (n + 1))

theorem toSegs_def (s : ωSequence α) (f : ℕ → ℕ) (n : ℕ) :
    s.toSegs f n = s.extract (f n) (f (n + 1)) :=
  rfl

/-- `(s.toSegs f).cumLen` is `f` itself. -/
@[simp]
theorem segment_toSegs_cumLen {f : ℕ → ℕ}
    (hm : StrictMono f) (h0 : f 0 = 0) (s : ωSequence α) :
    (s.toSegs f).cumLen = f := by
  ext n
  have (n' : ℕ) := hm (show n' < n' + 1 by lia)
  induction n <;> grind [toSegs_def]

/-- `(s.toSegs f).flatten` is `s` itself. -/
@[simp, scoped grind =]
theorem strictMono_flatten [Inhabited α] {f : ℕ → ℕ}
    (hm : StrictMono f) (h0 : f 0 = 0) (s : ωSequence α) :
    (s.toSegs f).flatten = s := by
  ext k; rw [flatten_def, segment_toSegs_cumLen hm h0, toSegs_def]
  have := segment_lower_bound hm h0 k
  have := segment_upper_bound hm h0 k
  grind

end ωSequence

end Cslib
