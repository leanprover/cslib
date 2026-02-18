/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Computability.Language

@[expose] public section

/-!
# Language (additional definitions and theorems)

This file contains additional definitions and theorems about `Language`
as defined and developed in `Mathlib.Computability.Language`.
-/

namespace Language

open Set List
open scoped Computability

variable {α : Type*} {l m : Language α}

@[simp]
theorem mem_biInf {I : Type*} (s : Set I) (l : I → Language α) (x : List α) :
    (x ∈ ⨅ i ∈ s, l i) ↔ ∀ i ∈ s, x ∈ l i :=
  mem_iInter₂

@[simp]
theorem mem_biSup {I : Type*} (s : Set I) (l : I → Language α) (x : List α) :
    (x ∈ ⨆ i ∈ s, l i) ↔ ∃ i ∈ s, x ∈ l i := by
  constructor <;> intro h
  · have := mem_iUnion₂.mp h
    grind
  · apply mem_iUnion₂.mpr
    grind

theorem le_one_iff_eq : l ≤ 1 ↔ l = 0 ∨ l = 1 :=
  subset_singleton_iff_eq

@[simp, scoped grind =]
theorem mem_sub_one (x : List α) : x ∈ (l - 1) ↔ x ∈ l ∧ x ≠ [] :=
  Iff.rfl

@[simp, scoped grind =]
theorem reverse_sub (l m : Language α) : (l - m).reverse = l.reverse - m.reverse := by
  ext x; simp [mem_sub]

@[scoped grind =]
theorem sub_one_mul : (l - 1) * l = l * l - 1 := by
  ext x; constructor
  · rintro ⟨u, h_u, v, h_v, rfl⟩
    constructor
    · refine ⟨u, ?_, v, ?_⟩ <;> grind
    · grind [append_eq_nil_iff, mem_one]
  · rintro ⟨⟨u, h_u, v, h_v, rfl⟩, h_x⟩
    rcases eq_or_ne u [] with (rfl | h_u')
    · refine ⟨v, ?_, [], ?_⟩ <;> grind [mem_sub, mem_one]
    · refine ⟨u, ?_, v, ?_⟩ <;> grind

@[scoped grind =]
theorem mul_sub_one : l * (l - 1) = l * l - 1 := by
  calc
    _ = (l * (l - 1)).reverse.reverse := by rw [reverse_reverse]
    _ = ((l.reverse - 1) * l.reverse).reverse := by rw [reverse_mul, reverse_sub, reverse_one]
    _ = (l.reverse * l.reverse - 1).reverse := by rw [sub_one_mul]
    _ = _ := by rw [reverse_sub, reverse_one, reverse_mul, reverse_reverse]

@[scoped grind =]
theorem kstar_sub_one : l∗ - 1 = (l - 1) * l∗ := by
  ext x; constructor
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

@[scoped grind =]
theorem sub_one_kstar : (l - 1)∗ = l∗ := by
  ext x
  grind [mem_kstar, mem_kstar_iff_exists_nonempty]

@[scoped grind .]
theorem kstar_iff_mul_add : m = l∗ ↔ m = (l - 1) * m + 1 := by
  rw [self_eq_mul_add_iff, mul_one, sub_one_kstar]
  grind

end Language
