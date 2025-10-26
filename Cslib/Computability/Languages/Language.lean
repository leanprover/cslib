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

/-- A language is trivial iff it contains at most the empty list `[]`. -/
def Trivial (l : Language α) := l \ 1 = 0

@[simp]
theorem zero_trivial : (0 : Language α).Trivial :=
  empty_diff _

@[simp]
theorem one_trivial : (1 : Language α).Trivial :=
  diff_self

theorem trivial_eq_zero_or_one (h : l.Trivial) : l = 0 ∨ l = 1 :=
  subset_singleton_iff_eq.mp <| diff_eq_empty.mp h

theorem trivial_iff : l.Trivial ↔ l = 0 ∨ l = 1 := by
  constructor
  · intro h
    exact trivial_eq_zero_or_one h
  · rintro (rfl | rfl)
    · exact zero_trivial
    · exact one_trivial

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
    have h3 : ¬ xl = [] := by intro h ; simp [h, one_def] at h2
    obtain ⟨x, xl', h_xl'⟩ := exists_cons_of_ne_nil h3
    refine ⟨x, ?_, xl'.flatten, ?_, by grind⟩
    · specialize h_xl x (by grind)
      exact h_xl
    · apply join_mem_kstar
      intro y h_y
      specialize h_xl y (by grind)
      grind
  · rintro ⟨y, ⟨h_y, h_1⟩, z, h_z, rfl⟩
    refine ⟨?_, ?_⟩
    · apply (show l * l∗ ≤ l∗ by exact mul_kstar_le_kstar)
      refine ⟨y, h_y, z, h_z, rfl⟩
    · simp only [one_def, mem_singleton_iff, append_eq_nil_iff] at h_1 ⊢
      tauto

end Language
