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

A word of length `n` can have `Θ(n²)` repeats, but at most `n - 1` right-maximal ones. The proof
adds one letter at a time: prepending a letter keeps every right-maximal repeat and makes at most
one new one, the longest prefix of the new word that occurs in the old one.

## Main definitions

* `List.IsRepeat u w`: `u` is a repeat of `w`.
* `List.IsRightMaximalRepeat u w`: `u` is a right-maximal repeat of `w`.
* `List.rightMaximalRepeats w`: the right-maximal repeats of `w`, found by checking every infix.

## Main statements

* `List.IsRightMaximalRepeat.isRepeat`: right-maximal repeats are repeats.
* `List.mem_rightMaximalRepeats`: `rightMaximalRepeats w` lists exactly the right-maximal repeats
  of `w`.
* `List.length_rightMaximalRepeats_cons_le`: prepending a letter adds at most one right-maximal
  repeat.
* `List.length_rightMaximalRepeats_le`: a word `w` has at most `w.length - 1` right-maximal
  repeats.

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

variable {c : α}

/-- The letters of `c :: w` after its first position are those of `w`. -/
private theorem getElem?_cons_succ_add (c : α) (w : List α) (i k : ℕ) :
    (c :: w)[i + 1 + k]? = w[i + k]? := by
  rw [show i + 1 + k = i + k + 1 by omega, getElem?_cons_succ]

/-- Prepending a letter keeps every right-maximal repeat. -/
theorem IsRightMaximalRepeat.cons (h : u.IsRightMaximalRepeat w) (c : α) :
    u.IsRightMaximalRepeat (c :: w) := by
  obtain ⟨hu, i, j, hi, hj, hne⟩ := h
  refine ⟨hu, i + 1, j + 1, occursAt_cons_succ.mpr hi, occursAt_cons_succ.mpr hj, ?_⟩
  rwa [getElem?_cons_succ_add, getElem?_cons_succ_add]

/-- A right-maximal repeat of `c :: w` that is not one of `w` is a prefix of `c :: w` that occurs
in `w`, while its extension by one more letter of `c :: w` does not occur in `w`. -/
theorem IsRightMaximalRepeat.of_cons (h : u.IsRightMaximalRepeat (c :: w))
    (hw : ¬u.IsRightMaximalRepeat w) :
    u <+: c :: w ∧ (∃ j, u.OccursAt w j) ∧ ∀ m, ¬((c :: w).take (u.length + 1)).OccursAt w m := by
  obtain ⟨hu, i, j, hi, hj, hne⟩ := h
  -- With one occurrence at the start and the other later, the later one is in `w`, and an
  -- occurrence of the extension in `w` would make `u` right-maximal in `w`.
  have key : ∀ {j : ℕ}, u.OccursAt (c :: w) 0 → u.OccursAt (c :: w) (j + 1) →
      (c :: w)[0 + u.length]? ≠ (c :: w)[j + 1 + u.length]? →
      u <+: c :: w ∧ (∃ j, u.OccursAt w j) ∧
        ∀ m, ¬((c :: w).take (u.length + 1)).OccursAt w m := by
    intro j h₀ hj hne
    have hp := occursAt_zero.mp h₀
    have hj' : u.OccursAt w j := occursAt_cons_succ.mp hj
    have hlen := hj'.add_length_le hu
    refine ⟨hp, ⟨j, hj'⟩, fun m hm => hw ⟨hu, m, j, ?_, hj', ?_⟩⟩
    · refine hm.of_prefix (prefix_of_prefix_length_le hp (take_prefix _ _) ?_)
      simp only [length_take, length_cons]
      omega
    · have hk : u.length < ((c :: w).take (u.length + 1)).length := by
        simp only [length_take, length_cons]
        omega
      rw [occursAt_iff_getElem?] at hm
      rw [hm u.length hk, getElem_take, ← getElem?_eq_getElem, ← getElem?_cons_succ_add c w j]
      rwa [Nat.zero_add] at hne
  rcases i with _ | i <;> rcases j with _ | j
  · exact absurd rfl hne
  · exact key hi hj hne
  · exact key hj hi (Ne.symm hne)
  · exact absurd ⟨hu, i, j, occursAt_cons_succ.mp hi, occursAt_cons_succ.mp hj,
      by rwa [getElem?_cons_succ_add, getElem?_cons_succ_add] at hne⟩ hw

/-- Prepending a letter makes at most one new right-maximal repeat: of two new ones, the longer
would contain the extension of the shorter by one letter, which does not occur in `w`. -/
theorem eq_of_isRightMaximalRepeat_cons {u' : List α} (h : u.IsRightMaximalRepeat (c :: w))
    (hw : ¬u.IsRightMaximalRepeat w) (h' : u'.IsRightMaximalRepeat (c :: w))
    (hw' : ¬u'.IsRightMaximalRepeat w) : u = u' := by
  obtain ⟨hp, ⟨j, hj⟩, hext⟩ := h.of_cons hw
  obtain ⟨hp', ⟨j', hj'⟩, hext'⟩ := h'.of_cons hw'
  have hlen : u.length = u'.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · refine hext j' (hj'.of_prefix (prefix_of_prefix_length_le (take_prefix _ _) hp' ?_))
      simp only [length_take]
      omega
    · refine hext' j (hj.of_prefix (prefix_of_prefix_length_le (take_prefix _ _) hp ?_))
      simp only [length_take]
      omega
  rw [prefix_iff_eq_take.mp hp, prefix_iff_eq_take.mp hp', hlen]

/-- A word of length at most `1` has no right-maximal repeat: a nonempty word occurs in it only
at the start. -/
theorem rightMaximalRepeats_eq_nil_of_length_le_one [DecidableEq α] (hw : w.length ≤ 1) :
    w.rightMaximalRepeats = [] := by
  refine eq_nil_iff_forall_not_mem.mpr fun u hu => ?_
  obtain ⟨hu, i, j, hi, hj, hne⟩ := mem_rightMaximalRepeats.mp hu
  have := hi.add_length_le hu
  have := hj.add_length_le hu
  have := length_pos_iff.mpr hu
  obtain rfl : i = j := by omega
  exact hne rfl

/-- Prepending a letter adds at most one right-maximal repeat. -/
theorem length_rightMaximalRepeats_cons_le [DecidableEq α] (c : α) (w : List α) :
    (c :: w).rightMaximalRepeats.length ≤ w.rightMaximalRepeats.length + 1 := by
  by_cases h : ∃ u ∈ (c :: w).rightMaximalRepeats, u ∉ w.rightMaximalRepeats
  · -- The right-maximal repeats of `c :: w` are those of `w` and the new one `u`.
    obtain ⟨u, hu, huw⟩ := h
    have hsub : (c :: w).rightMaximalRepeats ⊆ u :: w.rightMaximalRepeats := fun u' hu' => by
      by_cases hu'w : u' ∈ w.rightMaximalRepeats
      · exact mem_cons_of_mem _ hu'w
      · simp only [mem_rightMaximalRepeats] at hu hu' huw hu'w
        rw [eq_of_isRightMaximalRepeat_cons hu' hu'w hu huw]
        exact mem_cons_self
    simpa using (nodup_rightMaximalRepeats _).length_le_of_subset hsub
  · have hsub : (c :: w).rightMaximalRepeats ⊆ w.rightMaximalRepeats := fun u hu => by
      by_contra huw
      exact h ⟨u, hu, huw⟩
    have := (nodup_rightMaximalRepeats _).length_le_of_subset hsub
    omega

/-- A word of length `n` has at most `n - 1` right-maximal repeats [Gusfield1997]. -/
theorem length_rightMaximalRepeats_le [DecidableEq α] (w : List α) :
    w.rightMaximalRepeats.length ≤ w.length - 1 := by
  induction w with
  | nil => rw [rightMaximalRepeats_eq_nil_of_length_le_one (by simp)]; simp
  | cons c w ih =>
    cases w with
    | nil => rw [rightMaximalRepeats_eq_nil_of_length_le_one (by simp)]; simp
    | cons c' w =>
      have := length_rightMaximalRepeats_cons_le c (c' :: w)
      simp only [length_cons] at ih ⊢
      omega

end List
