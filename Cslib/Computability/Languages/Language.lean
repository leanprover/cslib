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

-- ********** BEGIN temporary block **********
-- This block of code will be removed once the following PR gets into mathlib:
-- https://github.com/leanprover-community/mathlib4/pull/30913

/-- The subtraction of two languages is their difference. -/
instance : Sub (Language α) where
  sub := SDiff.sdiff

theorem sub_def (l m : Language α) : l - m = (l \ m : Set (List α)) :=
  rfl

theorem mem_sub (l m : Language α) (x : List α) : x ∈ l - m ↔ x ∈ l ∧ x ∉ m :=
  Iff.rfl

instance : OrderedSub (Language α) where
  tsub_le_iff_right _ _ _ := sdiff_le_iff'

-- ********** END temporary block **********

theorem le_one_iff_eq : l ≤ 1 ↔ l = 0 ∨ l = 1 :=
  subset_singleton_iff_eq

@[simp, scoped grind =]
theorem mem_sub_one (x : List α) : x ∈ (l - 1) ↔ x ∈ l ∧ x ≠ [] :=
  Iff.rfl

@[simp, scoped grind =]
theorem sub_one_mul : (l - 1) * l = l * (l - 1) := by
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
theorem kstar_sub_one : l∗ - 1 = (l - 1) * l∗ := by
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
