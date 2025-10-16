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

open Nat Function

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

theorem cumLen_succ (ls : ωSequence (List α)) (k : ℕ) :
    ls.cumLen (k + 1) = ls.cumLen k + (ls k).length :=
  rfl

theorem cumLen_1plus_drop (ls : ωSequence (List α)) (k : ℕ) :
    ls.cumLen (1 + k) = (ls 0).length + (ls.drop 1).cumLen k := by
  induction k
  case zero => simp [cumLen_zero, cumLen_succ]
  case succ k h_ind =>
  rw [← add_assoc, cumLen_succ, h_ind, cumLen_succ, add_assoc]
  congr 2 ; rw [get_drop]

/-- If all lists in `ls` are nonempty, then `ls.cumLen` is strictly monotonic. -/
theorem cumLen_strict_mono {ls : ωSequence (List α)} (h_ls : ∀ k, (ls k).length > 0) :
    StrictMono ls.cumLen := by
  apply strictMono_nat_of_lt_succ
  intro k ; have := h_ls k
  rw [cumLen_succ] ; omega

@[simp, scoped grind =]
theorem cumLen_segment_zero {ls : ωSequence (List α)} (h_ls : ∀ k, (ls k).length > 0)
    (n : ℕ) (h_n : n < (ls 0).length) : segment ls.cumLen n = 0 := by
  have h0 : ls.cumLen 0 ≤ n := by simp [cumLen_zero]
  have h1 : n < ls.cumLen 1 := by simpa [cumLen_succ, cumLen_zero]
  exact segment_range_val (cumLen_strict_mono h_ls) h0 h1

open scoped Classical in
theorem cumLen_segment_1plus {ls : ωSequence (List α)} (h_ls : ∀ k, (ls k).length > 0)
    (n : ℕ) (h_n : (ls 0).length ≤ n) :
    segment ls.cumLen n = 1 + segment (ls.drop 1).cumLen (n - (ls 0).length) := by
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
      suffices h : i = 1 + (i - 1) by rw [h, cumLen_1plus_drop] ; omega
      suffices h : 0 < i by omega
      rw [← StrictMono.lt_iff_lt (cumLen_strict_mono h_ls), cumLen_zero] ; omega
    · rintro (rfl | _)
      · simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, true_and]
        use 0 ; rw [cumLen_zero]
      · grind
  have h2 : 0 ∉ {x ∈ Finset.range (n + 1) | x ∈ Set.range ls.cumLen ∧ (ls 0).length ≤ x} := by
    suffices h : ¬ (ls 0).length ≤ 0 by simp [h]
    grind
  rw [h1, Finset.card_insert_of_notMem h2, Nat.add_one_sub_one] ; symm
  apply Set.BijOn.finsetCard_eq (fun n ↦ n + (ls 0).length)
  unfold Set.BijOn ; constructorm* _ ∧ _
  · intro k ; simp only [Set.mem_range, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq,
      le_add_iff_nonneg_left, _root_.zero_le, and_true]
    rintro ⟨h_k, i, rfl⟩ ; constructorm* _ ∧ _
    · omega
    · use (1 + i) ; rw [cumLen_1plus_drop, add_comm]
  · apply Set.injOn_of_injective ; intro i j ; grind
  · intro k
    simp only [Set.mem_range, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, Set.mem_image]
    rintro ⟨h_k, ⟨i, rfl⟩, h_l0⟩
    use (ls.cumLen i - (ls 0).length)
    simp (disch := omega) only [Nat.sub_add_cancel, and_true] ; constructor
    · omega
    · use (i - 1)
      have := cumLen_1plus_drop ls (i - 1)
      have : 1 + (i - 1) = i := by
        suffices 0 < i by omega
        rw [← StrictMono.lt_iff_lt (cumLen_strict_mono h_ls), cumLen_zero]
        grind
      grind

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
  · simp (disch := omega) [get_append_right', flatten_def, cumLen_segment_1plus, cumLen_1plus_drop]
    congr 2 ; omega

/-- `ls.flatten` equals the concatenation of `(ls.take n).flatten` and `(ls.drop n).flatten`. -/
@[simp, scoped grind =]
theorem flatten_append [Inhabited α] {ls : ωSequence (List α)} (h_ls : ∀ k, (ls k).length > 0)
    (n : ℕ) : (ls.take n).flatten ++ω (ls.drop n).flatten = ls.flatten := by
  revert ls
  induction n
  case zero => simp
  case succ n h_ind =>
  intro ls h_ls
  specialize h_ind (ls := ls.drop 1) (by grind)
  rw [drop_drop, add_comm] at h_ind
  rw [take_succ, List.flatten_cons, append_append_ωSequence, tail_eq_drop,
    h_ind, ← tail_eq_drop]
  apply flatten_cons h_ls

end ωSequence

end Cslib
