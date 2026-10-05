/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Basic
public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Elementary properties of relation algebras

Converse preserves order, and composition preserves joins and annihilates the Boolean bottom.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {A : Type*} [RelationAlgebra A]

/-- Converse preserves the Boolean order. -/
theorem star_mono : Monotone (star : A → A) := by
  intro a b h
  calc
    star a ≤ star a ⊔ star b := le_sup_left
    _ = star (a ⊔ b) := (star_sup a b).symm
    _ = star b := by rw [sup_of_le_right h]

/-- Converse preserves the Boolean bottom. -/
@[simp] theorem star_bot : star (⊥ : A) = ⊥ := by
  apply le_antisymm _ bot_le
  simpa only [star_star] using (star_mono (bot_le : (⊥ : A) ≤ star ⊥))

/-- Converse preserves the Boolean top. -/
@[simp] theorem star_top : star (⊤ : A) = ⊤ := by
  apply le_antisymm le_top
  simpa only [star_star] using (star_mono (le_top : star (⊤ : A) ≤ ⊤))

/-- Composition distributes over joins in its right argument. -/
theorem mul_sup (a b c : A) : a * (b ⊔ c) = a * b ⊔ a * c := by
  apply star_injective
  simp only [star_mul, star_sup, sup_mul]

/-- Composition is monotone in its left argument. -/
theorem mul_le_mul_right {a b : A} (h : a ≤ b) (c : A) : a * c ≤ b * c := by
  have hs := sup_mul a b c
  rw [sup_of_le_right h] at hs
  exact hs ▸ le_sup_left

/-- Composition is monotone in its right argument. -/
theorem mul_le_mul_left {a b : A} (h : a ≤ b) (c : A) : c * a ≤ c * b := by
  have hs := mul_sup c a b
  rw [sup_of_le_right h] at hs
  exact hs ▸ le_sup_left

/-- The Boolean bottom annihilates composition on the right. -/
@[simp] theorem mul_bot (a : A) : a * ⊥ = ⊥ := by
  apply le_antisymm _ bot_le
  calc
    a * ⊥ ≤ a * (star a * ⊤)ᶜ := mul_le_mul_left bot_le a
    _ ≤ ⊥ := by simpa only [star_star, compl_top] using tarski (star a) ⊤

/-- The Boolean bottom annihilates composition on the left. -/
@[simp] theorem bot_mul (a : A) : ⊥ * a = ⊥ := by
  apply star_injective
  simp only [star_mul, star_bot, mul_bot]

end Cslib.RelationAlgebra
