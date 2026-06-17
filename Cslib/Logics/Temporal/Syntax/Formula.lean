/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Order.Notation

/-! # Temporal Logic Formula

This module defines the formula type for temporal logic with primitives
`{atom, bot, imp, untl, snce}`. The `untl` (until) and `snce` (since) operators are
the basic future and past temporal modalities from which all derived temporal operators
(globally, eventually, somePast, allPast) are obtained.

## Main definitions

- `Formula` : Inductive type for temporal logic formulas with constructors
  `atom`, `bot`, `imp`, `untl`, `snce`
- `Formula.someFuture` (𝐅): `φ U ⊤` — φ holds at some future point
- `Formula.allFuture` (𝐆): `¬𝐅¬φ` — φ holds at all future points
- `Formula.somePast` (𝐏): `φ S ⊤` — φ held at some past point
- `Formula.allPast` (𝐇): `¬𝐏¬φ` — φ held at all past points

## References

* [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]
* [D. Gabbay, A. Pnueli, S. Shelah, J. Stavi, *On the temporal analysis of fairness*][GPSS1980]
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

/-- Biconditional: φ₁ ↔ φ₂ := (φ₁ → φ₂) ∧ (φ₂ → φ₁) -/
abbrev Formula.iff (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  (φ₁.imp φ₂).and (φ₂.imp φ₁)

/-- Some future (eventually): 𝐅 φ := φ U ⊤. -/
abbrev Formula.someFuture (φ : Formula Atom) : Formula Atom :=
  .untl φ .top

/-- All future (globally): 𝐆 φ := ¬𝐅¬φ. -/
abbrev Formula.allFuture (φ : Formula Atom) : Formula Atom :=
  .neg (.someFuture (.neg φ))

/-- Some past: 𝐏 φ := φ S ⊤. -/
abbrev Formula.somePast (φ : Formula Atom) : Formula Atom :=
  .snce φ .top

/-- All past: 𝐇 φ := ¬𝐏¬φ. -/
abbrev Formula.allPast (φ : Formula Atom) : Formula Atom :=
  .neg (.somePast (.neg φ))

@[inherit_doc] scoped prefix:40 "¬" => Formula.neg
@[inherit_doc] scoped infix:36 " ∧ " => Formula.and
@[inherit_doc] scoped infix:35 " ∨ " => Formula.or
@[inherit_doc] scoped infix:30 " → " => Formula.imp
@[inherit_doc] scoped infix:30 " ↔ " => Formula.iff
@[inherit_doc] scoped infix:40 " U " => Formula.untl
@[inherit_doc] scoped infix:40 " S " => Formula.snce
@[inherit_doc] scoped prefix:40 "𝐅" => Formula.someFuture
@[inherit_doc] scoped prefix:40 "𝐆" => Formula.allFuture
@[inherit_doc] scoped prefix:40 "𝐏" => Formula.somePast
@[inherit_doc] scoped prefix:40 "𝐇" => Formula.allPast

/-- Register `Temporal.Formula` as an instance of `TemporalConnectives`. -/
instance : TemporalConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
  snce := .snce

instance : Bot (Formula Atom) := ⟨.bot⟩
instance : Top (Formula Atom) := ⟨.top⟩

/-- Reflexive until: derives non-strict until from strict until. -/
abbrev Formula.reflexiveUntl (φ ψ : Formula Atom) : Formula Atom :=
  φ.or (ψ.and (.untl φ ψ))

/-- Reflexive since: derives non-strict since from strict since. -/
abbrev Formula.reflexiveSnce (φ ψ : Formula Atom) : Formula Atom :=
  φ.or (ψ.and (.snce φ ψ))

end Cslib.Logic.Temporal

end
