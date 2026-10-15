/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Infix

/-! # Occurrences of a word in a word

This file defines when a list `u` occurs in a list `w` at a position `i`, and the list of all
positions at which `u` occurs in `w`. Positions start at `0`.

## Main definitions

* `List.OccursAt u w i`: `u` occurs in `w` starting at position `i`.
* `List.occurrences u w`: the positions at which `u` occurs in `w`, in increasing order.

## Main statements

* `List.occursAt_iff_getElem?`: occurrences in terms of letters.
* `List.OccursAt.trans`: an occurrence inside an occurrence is an occurrence.
* `List.mem_occurrences` and `List.pairwise_lt_occurrences`.
-/

@[expose] public section

namespace List

variable {α : Type*} {u v w : List α} {i p : ℕ}

/-- `u` occurs in `w` at position `i` if it is a prefix of the suffix of `w` starting at `i`. -/
def OccursAt (u w : List α) (i : ℕ) : Prop :=
  u <+: w.drop i

instance [DecidableEq α] (u w : List α) (i : ℕ) : Decidable (u.OccursAt w i) :=
  inferInstanceAs (Decidable (u <+: w.drop i))

/-- The empty list occurs at every position. -/
@[simp]
theorem occursAt_nil (w : List α) (i : ℕ) : ([] : List α).OccursAt w i :=
  nil_prefix

/-- An occurrence at position `0` is a prefix. -/
@[simp]
theorem occursAt_zero : u.OccursAt w 0 ↔ u <+: w := by
  simp [OccursAt]

/-- `u` occurs in `w` at `i` if and only if the letters of `w` from position `i` on are those
of `u`. -/
theorem occursAt_iff_getElem? :
    u.OccursAt w i ↔ ∀ k (hk : k < u.length), w[i + k]? = some u[k] := by
  simp [OccursAt, prefix_iff_getElem?]

/-- An occurrence of a nonempty word lies inside the word it occurs in. -/
theorem OccursAt.add_length_le (h : u.OccursAt w i) (hu : u ≠ []) :
    i + u.length ≤ w.length := by
  have h₁ := IsPrefix.length_le h
  have h₂ := length_pos_iff.mpr hu
  rw [length_drop] at h₁
  omega

/-- A prefix of a word occurs wherever the word occurs. -/
theorem OccursAt.of_prefix (h : u.OccursAt w i) (hv : v <+: u) : v.OccursAt w i :=
  hv.trans h

/-- If `v` occurs in `u` at `p` and `u` occurs in `w` at `i`, then `v` occurs in `w` at `i + p`. -/
theorem OccursAt.trans (hv : v.OccursAt u p) (hu : u.OccursAt w i) : v.OccursAt w (i + p) := by
  unfold OccursAt at *
  rw [← drop_drop]
  exact hv.trans (hu.drop p)

/-- `u ++ [c]` occurs in `w` at `i` if and only if `u` occurs there and is followed by `c`. -/
theorem occursAt_append_singleton_iff {c : α} :
    (u ++ [c]).OccursAt w i ↔ u.OccursAt w i ∧ w[i + u.length]? = some c := by
  rw [occursAt_iff_getElem?, occursAt_iff_getElem?]
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := h k (by simp only [length_append, length_singleton]; omega)
      rwa [getElem_append_left hk] at this
    · have := h u.length (by simp only [length_append, length_singleton]; omega)
      rwa [getElem_concat_length rfl] at this
  · rintro ⟨h, hc⟩ k hk
    rcases Nat.lt_or_ge k u.length with hk' | hk'
    · rw [getElem_append_left hk']
      exact h k hk'
    · obtain rfl : k = u.length := by
        simp only [length_append, length_singleton] at hk
        omega
      rw [getElem_concat_length rfl]
      exact hc

/-- The positions at which `u` occurs in `w`, in increasing order. -/
def occurrences [DecidableEq α] (u w : List α) : List ℕ :=
  (range (w.length + 1)).filter fun i => decide (u.OccursAt w i)

@[simp]
theorem mem_occurrences [DecidableEq α] :
    i ∈ u.occurrences w ↔ i ≤ w.length ∧ u.OccursAt w i := by
  simp [occurrences, Nat.lt_add_one_iff]

/-- For a nonempty word, the occurrences are exactly the positions where it occurs. -/
theorem mem_occurrences_of_ne_nil [DecidableEq α] (hu : u ≠ []) :
    i ∈ u.occurrences w ↔ u.OccursAt w i := by
  rw [mem_occurrences]
  exact ⟨And.right, fun h => ⟨by have := h.add_length_le hu; omega, h⟩⟩

/-- The occurrences are listed in strictly increasing order. -/
theorem pairwise_lt_occurrences [DecidableEq α] (u w : List α) :
    (u.occurrences w).Pairwise (· < ·) :=
  pairwise_lt_range.filter _

end List
