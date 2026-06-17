/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Cslib.Logics.Temporal.Syntax.Formula

/-! # LTL Formula Type

This module defines the formula type for Linear Temporal Logic with primitives
`{atom, bot, imp, next, untl}`. The primitive `next` operator is kept separate from
`untl` following the Burgess convention: in full temporal logic, `next φ` is sometimes
encoded as `φ U ⊥`, but this encoding does not hold in all models (it relies on
discreteness and non-triviality). An independent primitive `next` avoids this coupling.

## Main definitions

- `Formula` : Inductive type for LTL formulas with constructors
  `atom`, `bot`, `imp`, `next`, `untl`
- `Formula.someFuture` (𝐅): `φ U ⊤` — φ holds at some future point
- `Formula.allFuture` (𝐆): `¬𝐅¬φ` — φ holds at all future points
- `Formula.toTemporal` : Embedding of `LTL.Formula` into `Temporal.Formula`

## Notation

Propositional connectives (scoped to `Cslib.Logic.LTL`):
- `¬` (prefix, 40) : negation (`Formula.neg`)
- `∧` (infix, 36) : conjunction (`Formula.and`)
- `∨` (infix, 35) : disjunction (`Formula.or`)
- `→` (infix, 30) : implication (`Formula.imp`)
- `↔` (infix, 30) : biconditional (`Formula.iff`)

Temporal operators (scoped to `Cslib.Logic.LTL`):
- `U` (infix, 40) : until (`Formula.untl`)
- `X` (prefix, 40) : next-step (`Formula.next`)
- `𝐅` (prefix, 40) : some future / eventually (`Formula.someFuture`)
- `𝐆` (prefix, 40) : all future / globally (`Formula.allFuture`)

## Derived Operators

Derived operators follow the Burgess convention: in `untl event guard`, the first argument
is the **event** (holds at the witness point) and the second is the **guard** (holds at all
intermediate points). `someFuture φ` is `φ U ⊤` (φ is the event, ⊤ is the trivial guard).

## References

* [A. Pnueli, *The Temporal Logic of Programs*][Pnueli1977]
* [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]
* [J. P. Burgess, *Axioms for Tense Logic. I. "Since" and "Until"*][Burgess1982I]
* [J. P. Burgess, *Basic Tense Logic*][Burgess1984]
* [M. Y. Vardi, P. Wolper,
  *An automata-theoretic approach to automatic program verification*][VardiWolper1986]
-/

@[expose] public section

namespace Cslib.Logic.LTL

/-- LTL formula type. Primitives: atoms, falsum, implication, next-step, and until.

`next` is a primitive constructor and is not derived from `untl`. The encoding
`next φ = φ U ⊥` holds on discrete non-ending sequences but fails in general temporal
models; keeping `next` primitive supports broader model classes. -/
inductive Formula (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
  /-- Implication. -/
  | imp (φ₁ φ₂ : Formula Atom)
  /-- Next-step operator: Xφ holds at t iff φ holds at t+1. -/
  | next (φ : Formula Atom)
  /-- Until temporal operator: φ₁ U φ₂ (Burgess: event U guard). -/
  | untl (φ₁ φ₂ : Formula Atom)
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

/-- Some future (eventually): F φ := φ U ⊤.
    Uses Burgess convention: φ is the event (holds at witness), ⊤ is the trivial guard. -/
abbrev Formula.someFuture (φ : Formula Atom) : Formula Atom :=
  .untl φ .top

/-- All future (globally): G φ := ¬F ¬φ -/
abbrev Formula.allFuture (φ : Formula Atom) : Formula Atom :=
  .neg (.someFuture (.neg φ))

@[inherit_doc] scoped prefix:40 "¬" => Formula.neg
@[inherit_doc] scoped infix:36 " ∧ " => Formula.and
@[inherit_doc] scoped infix:35 " ∨ " => Formula.or
@[inherit_doc] scoped infix:30 " → " => Formula.imp
@[inherit_doc] scoped infix:30 " ↔ " => Formula.iff
@[inherit_doc] scoped infix:40 " U " => Formula.untl
@[inherit_doc] scoped prefix:40 "X" => Formula.next
@[inherit_doc] scoped prefix:40 "𝐅" => Formula.someFuture
@[inherit_doc] scoped prefix:40 "𝐆" => Formula.allFuture

/-- Register `LTL.Formula` as an instance of `LTLConnectives`. -/
instance : LTLConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
  next := .next

instance : Bot (Formula Atom) := ⟨.bot⟩
instance : Top (Formula Atom) := ⟨.top⟩

/-- Embed `LTL.Formula` into `Temporal.Formula`. Translates `next φ` as `φ U ⊥`
(strict until forces the immediate successor on ℕ) and `untl` as reflexive until. -/
def Formula.toTemporal : Formula Atom → Temporal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ ψ => .imp (toTemporal φ) (toTemporal ψ)
  | .next φ => .untl (toTemporal φ) .bot
  | .untl φ ψ => (toTemporal φ).reflexiveUntl (toTemporal ψ)

end Cslib.Logic.LTL

end
