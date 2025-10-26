/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Computability.Language
import Mathlib.Tactic

/-!
# Language (additional definitions and theorems)

This file contains additional definitions and theorems about `Language`
as defined and developed in `Mathlib.Computability.Language`.
-/

namespace Language

open Set List
open scoped Computability

variable {α : Type _} {l : Language α}

/-- A language is le_one iff it contains at most the empty list `[]`. -/
def le_one (l : Language α) := l \ 1 = 0

@[simp]
theorem zero_le_one : (0 : Language α).le_one :=
  empty_diff _

@[simp]
theorem one_le_one : (1 : Language α).le_one :=
  diff_self

theorem le_one_eq_zero_or_one (h : l.le_one) : l = 0 ∨ l = 1 :=
  subset_singleton_iff_eq.mp <| diff_eq_empty.mp h

theorem le_one_iff : l.le_one ↔ l = 0 ∨ l = 1 := by
  constructor
  · intro h
    exact le_one_eq_zero_or_one h
  · rintro (rfl | rfl)
    · exact zero_le_one
    · exact one_le_one

@[simp, scoped grind =]
theorem mem_sdiff_one (x : List α) : x ∈ (l \ 1) ↔ x ∈ l ∧ x ≠ [] :=
  Iff.rfl

@[simp]
theorem one_sdiff_one : 1 \ 1 = (0 : Language α) := by
  ext x
  simp only [sdiff_self, notMem_zero, iff_false]
  exact id

@[simp, scoped grind =]
theorem sdiff_one_mul : (l \ 1) * l = l * (l \ 1) := by
  ext x ; constructor
  · rintro ⟨u, h_u, v, h_v, rfl⟩
    rcases Classical.em (v = []) with rfl | h
    · use [] ; grind
    · use u ; grind
  · rintro ⟨u, h_u, v, h_v, rfl⟩
    rcases Classical.em (u = []) with rfl | h
    · use v ; grind
    · use u ; grind

@[simp, scoped grind =]
theorem kstar_sdiff_one : l∗ \ 1 = (l \ 1) * l∗ := by
  ext x ; constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨xl, rfl, h_xl⟩ := kstar_def_nonempty l ▸ h1
    have h3 : ¬ xl = [] := by grind [one_def]
    obtain ⟨x, xl', h_xl'⟩ := exists_cons_of_ne_nil h3
    have := h_xl x
    refine ⟨x, ?_, xl'.flatten, ?_, ?_⟩ <;> grind [join_mem_kstar]
  · rintro ⟨y, ⟨h_y, h_1⟩, z, h_z, rfl⟩
    refine ⟨?_, ?_⟩
    · apply (show l * l∗ ≤ l∗ by exact mul_kstar_le_kstar)
      exact ⟨y, h_y, z, h_z, rfl⟩
    · grind [one_def, append_eq_nil_iff]

end Language
