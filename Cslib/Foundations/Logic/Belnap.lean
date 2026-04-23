/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Mathlib.Order.WithBotTop

@[expose] public section

/-! # Belnap levels

Four-valued logic level with top (⊤), bottom (⊥), `true`, and `false`.

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]

-/

namespace Cslib.Logic

def BelnapLevel := WithBotTop Bool

namespace BelnapLevel

instance : Coe (WithBotTop Bool) (BelnapLevel) where
  coe l := l

instance : Bot BelnapLevel where
  bot := .none

instance : Top BelnapLevel where
  top := .some .none

def le : BelnapLevel → BelnapLevel → Prop
  | ⊥, _ => true
  | _, ⊤ => true
  | .some (.some x), .some (.some y) => x == y
  | _, _ => false

theorem le_refl (a : BelnapLevel) : a.le a := by
  cases a with
  | none => trivial
  | some a =>
    cases a with
    | top => trivial
    | coe b => cases b <;> trivial

theorem le_trans (a b c : BelnapLevel) (hab : a.le b) (hbc : b.le c) : a.le c := by
  cases a with
  | none => rfl
  | some a => cases a with
    | top =>
      cases b with
      | none => cases hab
      | some b => cases b with
        | top => exact hbc
        | coe bv => cases bv <;> trivial
    | coe av => cases c with
      | none =>
        cases b with
        | none => cases av <;> simp_all
        | some b => cases b with
          | top => trivial
          | coe bv => cases bv <;> trivial
      | some c => cases c with
        | top => rfl
        | coe cv =>
          cases b with
          | none => cases av <;> trivial
          | some b => cases b with
            | top => cases cv <;> trivial
            | coe bv => cases av <;> cases bv <;> cases cv <;> trivial

instance : Preorder BelnapLevel where
  le
  le_refl
  le_trans

theorem le_antisymm (a b : BelnapLevel) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some _ => cases hba
  | some a => cases a with
    | top =>
      cases b with
      | none => cases hab
      | some b => cases b with
        | top => rfl
        | coe _ => cases hab
    | coe av =>
      cases b with
      | none => cases hab
      | some b => cases b with
        | top => cases hba
        | coe bv => cases av <;> cases bv <;> first | rfl | cases hab

def sup : BelnapLevel → BelnapLevel → BelnapLevel
  | .none, x => x
  | x, .none => x
  | .some .none, _ => .some .none
  | _, .some .none => .some .none
  | .some (.some x), .some (.some y) => if x == y then .some (.some x) else .some .none

theorem le_sup_left (a b : BelnapLevel) : a ≤ a.sup b := by
  cases a with
  | none => trivial
  | some a => cases a with
    | top =>
      cases b with
      | none => trivial
      | some b => cases b with
        | top => trivial
        | coe bv => cases bv <;> trivial
    | coe av =>
      cases b with
      | none => cases av <;> trivial
      | some b => cases b with
        | top => trivial
        | coe bv => cases av <;> cases bv <;> trivial

theorem le_sup_right (a b : BelnapLevel) : b ≤ a.sup b := by
  cases a with
  | none => trivial
  | some a => cases a with
    | top =>
      cases b with
      | none => trivial
      | some b => cases b with
        | top => trivial
        | coe bv => cases bv <;> trivial
    | coe av =>
      cases b with
      | none => cases av <;> trivial
      | some b => cases b with
        | top => trivial
        | coe bv => cases av <;> cases bv <;> trivial

theorem sup_le (a b c : BelnapLevel) (hac : a ≤ c) (hbc : b ≤ c) : a.sup b ≤ c  := by
  cases a with
  | none => exact hbc
  | some a => cases a with
    | top => cases b <;> exact hac
    | coe av =>
      cases b with
      | none => exact hac
      | some b => cases b with
        | top => exact hbc
        | coe bv =>
          cases av <;> cases bv <;>
            first
            | exact hac
            | cases c with
                | none => cases hac
                | some c => cases c with
                  | top => trivial
                  | coe cv => cases cv <;> first | cases hbc; done | cases hac

def inf : BelnapLevel → BelnapLevel → BelnapLevel
  | .none, _ => .none
  | _, .none => .none
  | .some .none, x => x
  | x, .some .none => x
  | .some (.some x), .some (.some y) => if x == y then .some (.some x) else .none

theorem inf_le_left (a b : BelnapLevel) : a.inf b ≤ a := by
  cases a with
  | none => trivial
  | some a => cases a with
    | top =>
      cases b with
      | none => trivial
      | some b => cases b with
        | top => trivial
        | coe bv => cases bv <;> trivial
    | coe av =>
      cases b with
      | none => trivial
      | some b => cases b with
        | top => cases av <;> trivial
        | coe bv => cases av <;> cases bv <;> trivial

theorem inf_le_right (a b : BelnapLevel) : a.inf b ≤ b := by
  cases a with
  | none => trivial
  | some a => cases a with
    | top =>
      cases b with
      | none => trivial
      | some b => cases b with
        | top => trivial
        | coe bv => cases bv <;> trivial
    | coe av =>
      cases b with
      | none => trivial
      | some b => cases b with
        | top => cases av <;> trivial
        | coe bv => cases av <;> cases bv <;> trivial

theorem le_inf (a b c : BelnapLevel) (hab : a ≤ b) (hac : a ≤ c) : a ≤ b.inf c := by
  cases a with
  | none => trivial
  | some a => cases a with
    | top =>
      cases b with
      | none => cases hab
      | some b => cases b with
        | top =>
          cases c with
          | none => cases hac
          | some c => cases c with
            | top => trivial
            | coe cv => cases cv <;> trivial
        | coe _ => cases hab
    | coe av =>
      cases b with
      | none => cases hab
      | some b => cases b with
        | top =>
          cases c with
          | none => cases hac
          | some c => cases c with
            | top => trivial
            | coe cv => cases av <;> cases cv <;> trivial
        | coe bv =>
          cases c with
          | none => cases hac
          | some c => cases c with
            | top => cases av <;> cases bv <;> trivial
            | coe cv => cases av <;> cases bv <;> cases cv <;> trivial

instance : Lattice BelnapLevel where
  le_antisymm
  sup
  le_sup_left
  le_sup_right
  sup_le
  inf
  inf_le_left
  inf_le_right
  le_inf

variable {x₁ x₂ y₁ y₂ : BelnapLevel}

/-- Logical AND. -/
def and : BelnapLevel → BelnapLevel → BelnapLevel
  | .some (.some false), _ => false
  | _, .some (.some false) => false
  | .some (.some true), x => x
  | x, .some (.some true) => x
  | ⊥, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | _, _ => false

lemma and_leq (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂) : x₁.and x₂ ≤ y₁.and y₂ := by
  cases x₁ <;> try rename_i x; cases x <;> try (rename_i x; cases x)
  all_goals cases x₂ <;> try rename_i x; cases x <;> try rename_i x; cases x
  all_goals cases y₁ <;> try rename_i x; cases x <;> try rename_i x; cases x
  all_goals cases y₂ <;> try rename_i x; cases x <;> try rename_i x; cases x
  all_goals first | exact h₁ | exact h₂ | rfl

theorem and_monotone : Monotone and := by
  intro a b hab x
  exact and_leq hab le_rfl

/-- Logical OR. -/
def or : BelnapLevel → BelnapLevel → BelnapLevel
  | .some (.some true), _ => true
  | _, .some (.some true) => true
  | .some (.some false), x => x
  | x, .some (.some false) => x
  | ⊥, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | _, _ => true

lemma or_leq (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂) : x₁.or x₂ ≤ y₁.or y₂ := by
  cases x₁ <;> try rename_i x; cases x <;> try rename_i x; cases x
  all_goals cases x₂ <;> try rename_i x; cases x <;> try rename_i x; cases x
  all_goals cases y₁ <;> try rename_i x; cases x <;> try rename_i x; cases x
  all_goals cases y₂ <;> try rename_i x; cases x <;> try rename_i x; cases x
  all_goals first | exact h₁ | exact h₂ | rfl

theorem or_monotone : Monotone or := by
  intro a b hab x
  exact or_leq hab le_rfl

/-- Logical NOT. -/
def not : BelnapLevel → BelnapLevel
  | .some (.some b) => !b
  | x => x

lemma not_leq {x y : BelnapLevel} (h : x ≤ y) : x.not ≤ y.not := by
  cases x with
  | none => exact h
  | some x => cases x with
    | top =>
      cases y with | none => exact h | some y => cases y <;> exact h
    | coe xv =>
      cases y with
      | none => exact h
      | some y => cases y with
        | top => exact h
        | coe yv => cases xv <;> cases yv <;> exact h

theorem not_monotone : Monotone not := by
  intro a b hab
  exact not_leq hab

end BelnapLevel

end Cslib.Logic
