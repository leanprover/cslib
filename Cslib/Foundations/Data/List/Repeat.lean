/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Foundations.Data.List.Occurrence
public import Mathlib.Data.List.Dedup

/-! # Repeats and right-maximal repeats

A repeat of a word `w` is a nonempty word that occurs in `w` at two different positions. It is
right-maximal if two of its occurrences are followed by different letters, where an occurrence at
the end of `w` counts as followed by a letter that occurs nowhere else [Gusfield1997].

## Main definitions

* `List.IsRepeat u w`: `u` is a repeat of `w`.
* `List.IsRightMaximalRepeat u w`: `u` is a right-maximal repeat of `w`.
* `List.rightMaximalRepeats w`: the right-maximal repeats of `w`, found by checking every infix.

## Main statements

* `List.IsRightMaximalRepeat.isRepeat`: right-maximal repeats are repeats.
* `List.mem_rightMaximalRepeats`: `rightMaximalRepeats w` lists exactly the right-maximal repeats
  of `w`.

## References

* [D. Gusfield, *Algorithms on Strings, Trees, and Sequences*][Gusfield1997]
-/

@[expose] public section

namespace List

variable {α : Type*} {u w : List α}

/-- A repeat of `w` is a nonempty word that occurs in `w` at two different positions. -/
def IsRepeat (u w : List α) : Prop :=
  u ≠ [] ∧ ∃ i j, i ≠ j ∧ u.OccursAt w i ∧ u.OccursAt w j

/-- A right-maximal repeat of `w` is a nonempty word with two occurrences in `w` followed by
different letters. An occurrence at the end of `w` is followed by `none`, which differs from every
letter. -/
def IsRightMaximalRepeat (u w : List α) : Prop :=
  u ≠ [] ∧ ∃ i j, u.OccursAt w i ∧ u.OccursAt w j ∧ w[i + u.length]? ≠ w[j + u.length]?

/-- Right-maximal repeats are repeats. -/
theorem IsRightMaximalRepeat.isRepeat (h : u.IsRightMaximalRepeat w) : u.IsRepeat w := by
  obtain ⟨hu, i, j, hi, hj, hne⟩ := h
  exact ⟨hu, i, j, fun hij => hne (by subst hij; rfl), hi, hj⟩

/-- Being a repeat only depends on the list of occurrences. -/
theorem isRepeat_iff_mem_occurrences [DecidableEq α] :
    u.IsRepeat w ↔ u ≠ [] ∧ ∃ i ∈ u.occurrences w, ∃ j ∈ u.occurrences w, i ≠ j := by
  refine and_congr_right fun hu => ?_
  simp only [mem_occurrences_of_ne_nil hu]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨i, hi, j, hj, hij⟩
  · rintro ⟨i, hi, j, hj, hij⟩
    exact ⟨i, j, hij, hi, hj⟩

instance [DecidableEq α] (u w : List α) : Decidable (u.IsRepeat w) :=
  decidable_of_iff _ isRepeat_iff_mem_occurrences.symm

/-- Being a right-maximal repeat only depends on the list of occurrences. -/
theorem isRightMaximalRepeat_iff_mem_occurrences [DecidableEq α] :
    u.IsRightMaximalRepeat w ↔ u ≠ [] ∧ ∃ i ∈ u.occurrences w, ∃ j ∈ u.occurrences w,
      w[i + u.length]? ≠ w[j + u.length]? := by
  refine and_congr_right fun hu => ?_
  simp only [mem_occurrences_of_ne_nil hu]
  constructor
  · rintro ⟨i, j, hi, hj, hne⟩
    exact ⟨i, hi, j, hj, hne⟩
  · rintro ⟨i, hi, j, hj, hne⟩
    exact ⟨i, j, hi, hj, hne⟩

instance [DecidableEq α] (u w : List α) : Decidable (u.IsRightMaximalRepeat w) :=
  decidable_of_iff _ isRightMaximalRepeat_iff_mem_occurrences.symm

/-- The right-maximal repeats of `w`, each listed once, found by checking every infix of `w`. -/
def rightMaximalRepeats [DecidableEq α] (w : List α) : List (List α) :=
  ((w.tails.flatMap inits).filter fun u => decide (u.IsRightMaximalRepeat w)).dedup

@[simp]
theorem mem_rightMaximalRepeats [DecidableEq α] :
    u ∈ w.rightMaximalRepeats ↔ u.IsRightMaximalRepeat w := by
  simp only [rightMaximalRepeats, mem_dedup, mem_filter, mem_flatMap, mem_tails, mem_inits,
    decide_eq_true_eq]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨-, i, -, hi, -, -⟩ := h
  exact ⟨w.drop i, drop_suffix i w, hi⟩

theorem nodup_rightMaximalRepeats [DecidableEq α] (w : List α) : w.rightMaximalRepeats.Nodup :=
  nodup_dedup _

end List
