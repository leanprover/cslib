/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Order.Notation

/-! # LTL Formula Type

This module defines the formula type for Linear Temporal Logic with primitives
`{atom, bot, imp, next, untl}`. The primitive `next` operator is kept separate from
`untl`: in full temporal logic, `next φ` is sometimes encoded as `φ U ⊥`, but this
encoding does not hold in all models (it relies on discreteness and non-triviality).
An independent primitive `next` avoids this coupling.

## Main definitions

- `Formula` : Inductive type for LTL formulas with constructors
  `atom`, `bot`, `imp`, `next`, `untl`
- `Formula.someFuture` (◇): `φ U ⊤` — φ holds at some future point
- `Formula.allFuture` (□): `¬◇¬φ` — φ holds at all future points
- `Formula.leadsto` (⇝): `□(p → ◇q)` — liveness: every p-state is eventually followed by q

## Notation

Propositional connectives (scoped to `Cslib.Logic.LTL`):
- `¬` (prefix, 40) : negation (`Formula.neg`)
- `∧` (infix, 36) : conjunction (`Formula.and`)
- `∨` (infix, 35) : disjunction (`Formula.or`)
- `→` (infix, 30) : implication (`Formula.imp`)
- `↔` (infix, 30) : biconditional (`Formula.iff`)

Temporal operators (scoped to `Cslib.Logic.LTL`):
- `𝓤` (infix, 40) : until (`Formula.untl`)
- `◯` (prefix, 40) : next-step (`Formula.next`)
- `◇` (prefix, 40) : some future / eventually (`Formula.someFuture`)
- `□` (prefix, 40) : all future / globally (`Formula.allFuture`)
- `⇝` (infix, 20) : leads-to, `□(p → ◇q)` (`Formula.leadsto`)

## Derived Operators

In `untl φ ψ`, the first argument `φ` is the **guard** (holds at all intermediate
points) and the second `ψ` is the **event** (eventually holds at the witness point).
`someFuture φ` is `⊤ U φ` (⊤ is the trivial guard, φ is the event).

## References

* [A. Pnueli, *The Temporal Logic of Programs*][Pnueli1977]
* [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]
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
  /-- Until temporal operator: φ₁ U φ₂ (guard U event: φ₁ holds until φ₂). -/
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

/-- Some future (eventually): ◇φ := ⊤ U φ.
    ⊤ is the trivial guard, φ is the event that eventually holds. -/
abbrev Formula.someFuture (φ : Formula Atom) : Formula Atom :=
  .untl .top φ

/-- All future (globally): □φ := ¬◇¬φ -/
abbrev Formula.allFuture (φ : Formula Atom) : Formula Atom :=
  .neg (.someFuture (.neg φ))

/-- Leads-to: p ⇝ q := □(p → ◇q). A liveness property asserting that
    every state satisfying p is eventually followed by a state satisfying q. -/
abbrev Formula.leadsto (p q : Formula Atom) : Formula Atom :=
  .allFuture (.imp p (.someFuture q))

@[inherit_doc] scoped prefix:40 "¬" => Formula.neg
@[inherit_doc] scoped infix:36 " ∧ " => Formula.and
@[inherit_doc] scoped infix:35 " ∨ " => Formula.or
@[inherit_doc] scoped infix:30 " → " => Formula.imp
@[inherit_doc] scoped infix:30 " ↔ " => Formula.iff
@[inherit_doc] scoped infix:40 " 𝓤 " => Formula.untl
@[inherit_doc] scoped prefix:40 "◯" => Formula.next
@[inherit_doc] scoped prefix:40 "◇" => Formula.someFuture
@[inherit_doc] scoped prefix:40 "□" => Formula.allFuture
@[inherit_doc] scoped infix:20 " ⇝ " => Formula.leadsto

/-- Register `LTL.Formula` as an instance of `LTLConnectives`. -/
instance : LTLConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
  next := .next

instance : Bot (Formula Atom) := ⟨.bot⟩
instance : Top (Formula Atom) := ⟨.top⟩

end Cslib.Logic.LTL

end
