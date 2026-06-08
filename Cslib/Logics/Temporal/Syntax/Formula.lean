/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives

/-! # Temporal Logic Formula

This module defines the formula type for temporal logic with primitives
`{atom, bot, imp, untl, snce}`. The `untl` (until) and `snce` (since) operators
are the basic temporal modalities from which all other temporal operators
(globally, eventually, etc.) are derived.

## Derived Temporal Operators

- `some_future φ` (F φ): `⊤ U φ` — eventually in the future
- `all_future φ` (G φ): `¬F ¬φ` — always in the future
- `some_past φ` (P φ): `⊤ S φ` — at some point in the past
- `all_past φ` (H φ): `¬P ¬φ` — always in the past
-/

@[expose] public section

namespace Cslib.Logic.Temporal

/-- Temporal logic formula type. Primitives: atoms, falsum, implication, until, and since. -/
inductive Formula (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
  /-- Implication. -/
  | imp (φ₁ φ₂ : Formula Atom)
  /-- Until temporal operator: φ₁ U φ₂. -/
  | untl (φ₁ φ₂ : Formula Atom)
  /-- Since temporal operator: φ₁ S φ₂. -/
  | snce (φ₁ φ₂ : Formula Atom)
deriving DecidableEq, BEq

/-- Negation: ¬φ := φ → ⊥ -/
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := .imp φ .bot

/-- Verum / top: ⊤ := ⊥ → ⊥ -/
abbrev Formula.top : Formula Atom := .imp .bot .bot

/-- Disjunction: φ₁ ∨ φ₂ := ¬φ₁ → φ₂ -/
abbrev Formula.or (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  .imp (.imp φ₁ .bot) φ₂

/-- Conjunction: φ₁ ∧ φ₂ := ¬(φ₁ → ¬φ₂) -/
abbrev Formula.and (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  .imp (.imp φ₁ (.imp φ₂ .bot)) .bot

/-- Some future (eventually): F φ := ⊤ U φ -/
abbrev Formula.some_future (φ : Formula Atom) : Formula Atom :=
  .untl .top φ

/-- All future (globally): G φ := ¬F ¬φ -/
abbrev Formula.all_future (φ : Formula Atom) : Formula Atom :=
  .neg (.some_future (.neg φ))

/-- Some past: P φ := ⊤ S φ -/
abbrev Formula.some_past (φ : Formula Atom) : Formula Atom :=
  .snce .top φ

/-- All past (historically): H φ := ¬P ¬φ -/
abbrev Formula.all_past (φ : Formula Atom) : Formula Atom :=
  .neg (.some_past (.neg φ))

@[inherit_doc] scoped prefix:40 "¬" => Formula.neg
@[inherit_doc] scoped infix:36 " ∧ " => Formula.and
@[inherit_doc] scoped infix:35 " ∨ " => Formula.or
@[inherit_doc] scoped infix:30 " → " => Formula.imp
@[inherit_doc] scoped infix:40 " U " => Formula.untl
@[inherit_doc] scoped infix:40 " S " => Formula.snce
@[inherit_doc] scoped prefix:40 "F" => Formula.some_future
@[inherit_doc] scoped prefix:40 "G" => Formula.all_future
@[inherit_doc] scoped prefix:40 "P" => Formula.some_past
@[inherit_doc] scoped prefix:40 "H" => Formula.all_past

/-- Register `Temporal.Formula` as an instance of `TemporalConnectives`. -/
instance : TemporalConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
  snce := .snce

end Cslib.Logic.Temporal
