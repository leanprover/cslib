/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.WithBot

/-! # Utilities for Heyting algebras -/

@[expose] public section

@[to_dual]
instance {α : Type*} [HImp α] [Top α] : HImp (WithBot α) where
  himp a b := a.recBotCoe ⊤ fun a ↦ b.recBotCoe ⊥ fun b ↦ (a ⇨ b : α)

@[to_dual (attr := simp)] lemma WithBot.bot_himp {α : Type*} [HImp α] [Top α] (a : WithBot α) :
  ⊥ ⇨ a = ⊤ := rfl
@[to_dual (attr := simp)] lemma WithBot.coe_himp_bot {α : Type*} [HImp α] [Top α] (a : α) :
  (a : WithBot α) ⇨ ⊥ = ⊥ := rfl
@[to_dual (attr := simp) WithTop.coe_sdiff] lemma WithBot.coe_himp {α : Type*} [HImp α] [Top α]
  (a b : α) : ↑(a ⇨ b : α) = (a : WithBot α) ⇨ b := rfl

instance {α : Type*} [GeneralizedHeytingAlgebra α] : HeytingAlgebra (WithBot α) where
  le_himp_iff {a b c} := by
    cases b with
    | bot => simp
    | coe b =>
      cases a with
      | bot => simp
      | coe a =>
        cases c with
        | bot => simp [← WithBot.coe_inf]
        | coe c => simp [← WithBot.coe_himp, ← WithBot.coe_inf]
  compl := (· ⇨ ⊥)
  himp_bot _ := rfl

instance {α : Type*} [GeneralizedCoheytingAlgebra α] : CoheytingAlgebra (WithTop α) where
  sdiff_le_iff {a b c} := by
    cases b with
    | top => simp
    | coe b =>
      cases c with
      | top => simp
      | coe c =>
        cases a with
        | top => simp [← WithTop.coe_sup]
        | coe c => simp [← WithTop.coe_sdiff, ← WithTop.coe_sup]
  hnot := (⊤ \ ·)
  top_sdiff _ := rfl
