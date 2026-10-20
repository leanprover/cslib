/-
Copyright (c) 2026 Chi-Yun Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chi-Yun Hsu
-/

module

public import Cslib.Init
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Data.Set.Card

/-!
# Regular Expressions (additional definitions and theorems)

This file contains additional definitions and theorems about `RegularExpression`
as defined and developed in `Mathlib.Computability.RegularExpressions`.
-/

@[expose] public section

namespace RegularExpression

open Set Computability

variable {α : Type*}

@[simp]
theorem mem_sum_matches' (rs : List (RegularExpression α)) (x : List α) :
    x ∈ rs.sum.matches' ↔ ∃ r ∈ rs, x ∈ r.matches' := by
  induction rs with
  | nil => simp
  | cons head tail ih =>
    simp only [List.sum_cons, matches', Language.mem_add, ih, List.mem_cons, exists_eq_or_imp]

theorem iSup_matches' {I : Type*} [Finite I] {s : Set I} {l : I → Language α}
    (h : ∀ i ∈ s, ∃ r : RegularExpression α, l i = r.matches') :
    ∃ r : RegularExpression α, (⨆ i ∈ s, l i) = r.matches' := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero =>
    obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp only [mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot]
    exact ⟨0, matches'_zero⟩
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
    rw [iSup_insert]
    simp only [Set.mem_insert_iff, forall_eq_or_imp] at h
    obtain ⟨ri, hri⟩ := h.1
    obtain ⟨rt, hrt⟩ := h_ind h.2 rfl
    use ri + rt
    simp [hri, hrt]

end RegularExpression
