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

namespace WithBot

/-- Heyting implication for `WithBot α`. Not an instance to avoid diamonds arising from
`LinearOrder.toBiheytingAlgebra`. -/
@[to_dual sdiff /-- SDiff for `WithTop α`. Not an instance to avoid diamonds arising from
`LinearOrder.toBiheytingAlgebra`. -/]
protected abbrev himp (α : Type*) [HImp α] [Top α] : HImp (WithBot α) where
  himp a b := a.recBotCoe ⊤ fun a ↦ b.recBotCoe ⊥ fun b ↦ (a ⇨ b : α)

@[to_dual (attr := simp) sdiff_top]
lemma bot_himp {α : Type*} [HImp α] [Top α] (a : WithBot α) :
  letI := WithBot.himp α; ⊥ ⇨ a = ⊤ := rfl

@[to_dual (attr := simp) top_sdiff]
lemma coe_himp_bot {α : Type*} [HImp α] [Top α] (a : α) :
  letI := WithBot.himp α; (a : WithBot α) ⇨ ⊥ = ⊥ := rfl

@[to_dual (attr := simp) coe_sdiff]
lemma coe_himp {α : Type*} [HImp α] [Top α] (a b : α) :
  letI := WithBot.himp α; ↑(a ⇨ b : α) = (a : WithBot α) ⇨ b := rfl

/-- Heyting algebra structure on `WithBot α`. Not an instance to avoid diamonds arising from
`LinearOrder.toBiheytingAlgebra`. -/
protected abbrev heytingAlgebra (α : Type*) [GeneralizedHeytingAlgebra α] :
    HeytingAlgebra (WithBot α) where
  __ := WithBot.himp α
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

/-- Coheyting algebra structure on `WithTop α`. Not an instance to avoid diamonds arising from
`LinearOrder.toBiheytingAlgebra`. -/
@[to_dual existing]
protected abbrev _root_.WithTop.coheytingAlgebra (α : Type*) [GeneralizedCoheytingAlgebra α] :
    CoheytingAlgebra (WithTop α) where
  __ := WithTop.sdiff α
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

@[to_dual (attr := simp) hnot_coe]
lemma compl_coe {α : Type*} [GeneralizedHeytingAlgebra α] (a : α) :
  letI := WithBot.heytingAlgebra α; (a : WithBot α)ᶜ = ⊥ := rfl

end WithBot
