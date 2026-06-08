/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives

/-! # Bimodal Logic Formula

This module defines the formula type for bimodal (temporal-modal) logic with primitives
`{atom, bot, imp, box, untl, snce}`. This is the combined language that includes both
modal necessity and temporal until/since operators.

## Derived Connectives

All derived connectives from both modal and temporal logic are available:
- Propositional: `neg`, `top`, `and`, `or`
- Modal: `diamond` (◇φ := ¬□¬φ)
- Temporal: `some_future`, `all_future`, `some_past`, `all_past`
-/

@[expose] public section

namespace Cslib.Logic.Bimodal

/-- Bimodal logic formula type. Primitives: atoms, falsum, implication, box, until, since. -/
inductive Formula (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
  /-- Implication. -/
  | imp (φ₁ φ₂ : Formula Atom)
  /-- Necessity / box. -/
  | box (φ : Formula Atom)
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

/-- Possibility / diamond: ◇φ := ¬□¬φ -/
abbrev Formula.diamond (φ : Formula Atom) : Formula Atom :=
  .neg (.box (.neg φ))

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
@[inherit_doc] scoped prefix:40 "□" => Formula.box
@[inherit_doc] scoped prefix:40 "◇" => Formula.diamond
@[inherit_doc] scoped infix:40 " U " => Formula.untl
@[inherit_doc] scoped infix:40 " S " => Formula.snce
@[inherit_doc] scoped prefix:40 "F" => Formula.some_future
@[inherit_doc] scoped prefix:40 "G" => Formula.all_future
@[inherit_doc] scoped prefix:40 "P" => Formula.some_past
@[inherit_doc] scoped prefix:40 "H" => Formula.all_past

/-- Register `Bimodal.Formula` as an instance of `BimodalConnectives`. -/
instance : BimodalConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  box := .box
  untl := .untl
  snce := .snce

end Cslib.Logic.Bimodal
