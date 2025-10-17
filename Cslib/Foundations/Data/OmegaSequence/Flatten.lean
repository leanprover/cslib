/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Foundations.Data.Nat.Segment
import Cslib.Foundations.Data.OmegaSequence.Init
import Mathlib.Tactic

/-!
# Flattening an infinite sequence of lists

Given an ω-sequence `ls` of (nonempty) lists, `ls.flatten` is the infinite sequence
formed by the concatenation of all of them.
-/

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
theorem cumLen_strict_mono {ls : ωSequence (List α)} (h_ls : ∀ k, (ls k).length > 0) :
    StrictMono ls.cumLen := by
  grind [strictMono_nat_of_lt_succ]

@[simp, scoped grind =]
theorem cumLen_segment_zero {ls : ωSequence (List α)} (h_ls : ∀ k, (ls k).length > 0)
    (n : ℕ) (h_n : n < (ls 0).length) : segment ls.cumLen n = 0 := by
  have h0 : ls.cumLen 0 ≤ n := by simp [cumLen_zero]
  have h1 : n < ls.cumLen 1 := by simpa [cumLen_succ, cumLen_zero]
  exact segment_range_val (cumLen_strict_mono h_ls) h0 h1

theorem cumLen_segment_one_add {ls : ωSequence (List α)} (h_ls : ∀ k, (ls k).length > 0)
    (n : ℕ) (h_n : (ls 0).length ≤ n) :
    segment ls.cumLen n = 1 + segment (ls.drop 1).cumLen (n - (ls 0).length) := by
  classical
  have h0 : (ls.drop 1).cumLen 0 = 0 := by simp [cumLen_zero]
  rw [add_comm, segment_plus_one h0] ; unfold Nat.segment
  simp only [Nat.count_eq_card_filter_range]
  have h1 : {x ∈ Finset.range (n + 1) | x ∈ Set.range ls.cumLen} = insert 0
      {x ∈ Finset.range (n + 1) | x ∈ Set.range ls.cumLen ∧ (ls 0).length ≤ x} := by
    ext k ; simp only [Set.mem_range, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨h_k, i, rfl⟩
      simp only [h_k, exists_apply_eq_apply, true_and, or_iff_not_imp_left]
      intro h_i
      suffices h : i = 1 + (i - 1) by grind [cumLen_one_add_drop]
      grind
    · rintro (rfl | _)
      · refine ⟨?_, 0, ?_⟩ <;> grind
      · grind
  have h2 : 0 ∉ {x ∈ Finset.range (n + 1) | x ∈ Set.range ls.cumLen ∧ (ls 0).length ≤ x} := by
    grind
  rw [h1, Finset.card_insert_of_notMem h2, Nat.add_one_sub_one]
  symm
  apply Set.BijOn.finsetCard_eq (fun n ↦ n + (ls 0).length)
  refine ⟨?_, by grind [injOn_of_injective, Injective], ?_⟩ <;>
  ( intro k ; simp only [Set.mem_range, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq,
      le_add_iff_nonneg_left, _root_.zero_le, and_true] )
  · rintro ⟨h_k, i, rfl⟩
    refine ⟨?_, 1 + i, ?_⟩ <;> grind [cumLen_one_add_drop]
  · rintro ⟨h_k, ⟨i, rfl⟩, h_l0⟩
    have := cumLen_one_add_drop ls (i - 1)
    refine ⟨ls.cumLen i - (ls 0).length, ⟨?_, i - 1, ?_⟩, ?_⟩ <;> grind

/-- Given an ω-sequence `ls` of lists, `ls.flatten` is the infinite sequence
formed by the concatenation of all of them.  For the definition to make proper
sense, we will consistently assume that all lists in `ls` are nonempty. -/
noncomputable def flatten [Inhabited α] (ls : ωSequence (List α)) : ωSequence α :=
  fun n ↦ (ls (segment ls.cumLen n))[n - ls.cumLen (segment ls.cumLen n)]!

theorem flatten_def [Inhabited α] (ls : ωSequence (List α)) (n : ℕ) :
    flatten ls n = (ls (segment ls.cumLen n))[n - ls.cumLen (segment ls.cumLen n)]! :=
  rfl

/-- `ls.flatten` equals the concatenation of `ls.head` and `ls.tail.flatten`. -/
@[simp, scoped grind =]
theorem flatten_cons [Inhabited α] {ls : ωSequence (List α)} (h_ls : ∀ k, (ls k).length > 0) :
    ls.head ++ω ls.tail.flatten = ls.flatten := by
  ext n ; rw [flatten_def, head, tail_eq_drop]
  rcases (show n < (ls 0).length ∨ n ≥ (ls 0).length by omega) with h_n | h_n
  · simp (disch := omega) [get_append_left, cumLen_segment_zero, cumLen_zero]
  · simp (disch := omega) [get_append_right', flatten_def, cumLen_segment_one_add, cumLen_one_add_drop]
    grind

/-- `ls.flatten` equals the concatenation of `(ls.take n).flatten` and `(ls.drop n).flatten`. -/
@[simp, scoped grind =]
theorem flatten_append [Inhabited α] {ls : ωSequence (List α)} (h_ls : ∀ k, (ls k).length > 0)
    (n : ℕ) : (ls.take n).flatten ++ω (ls.drop n).flatten = ls.flatten := by
  induction n generalizing ls <;> grind [tail_eq_drop, take_succ]

end ωSequence

end Cslib
