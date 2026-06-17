/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

/-! # Connective Typeclasses for Propositional and Temporal Logic

This module defines a typeclass hierarchy for logical connectives. Each formula
type registers itself as an instance of the appropriate connective class, enabling polymorphic
axiom definitions and notation that work uniformly across different formula types.

## Design

The hierarchy adopts a hybrid five-primitive propositional signature `{atom, bot, imp, and, or}`,
following the operator-typeclass direction of fmontesi's PR #607 (one class per operator):
- **Atomic classes**: `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasUntil`, `HasSince`, `HasNext`
- **Bundled classes**: `PropositionalConnectives` (extends `HasBot` and `HasImp`),
  `FutureTemporalConnectives` (extends `PropositionalConnectives` and `HasUntil`),
  `LTLConnectives` (extends `FutureTemporalConnectives` and `HasNext`),
  `TemporalConnectives` (extends `FutureTemporalConnectives` and `HasSince`)

Conjunction (`HasAnd`) and disjunction (`HasOr`) are treated as independent primitives rather
than Łukasiewicz-derived connectives. The classical encodings `φ ∧ ψ := ¬(φ → ¬ψ)` and
`φ ∨ ψ := ¬φ → ψ` are only propositionally equivalent to `∧` and `∨` in classical logic
([Wajsberg1938], [McKinsey1939]); they fail in intuitionistic and minimal logic. Making `and`
and `or` primitive via `HasAnd`/`HasOr` supports all three logic strengths with a single
typeclass hierarchy.

Negation and verum stay derived: each concrete formula type defines `neg φ := φ → ⊥` and
`top := ⊥ → ⊥` as `abbrev`s, which are valid in minimal, intuitionistic, and classical logic
alike, so no typeclass machinery is needed for them.

## References

* [J. Avigad, *Mathematical Logic and Computation*][Avigad2022]
* [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
* [M. Wajsberg, *Untersuchungen über den Aussagenkalkül von A. Heyting*][Wajsberg1938]
* [J. C. C. McKinsey,
  *Proof of the Independence of the Primitive Symbols of Heyting's Calculus*][McKinsey1939]
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
* [A. S. Troelstra, D. van Dalen,
  *Constructivism in Mathematics: An Introduction*][TroelstraVanDalen1988]
* [A. Church, *Introduction to Mathematical Logic*][Church1956]
* [G. Gentzen, *Untersuchungen über das logische Schließen*][Gentzen1935]
-/

@[expose] public section

namespace Cslib.Logic

/-- A type has a falsum (bottom) connective. -/
class HasBot (F : Type*) where
  /-- The falsum/bottom connective. -/
  bot : F

/-- A type has an implication connective. -/
class HasImp (F : Type*) where
  /-- The implication connective. -/
  imp : F → F → F

/-- A type has an until temporal operator. -/
class HasUntil (F : Type*) where
  /-- The until temporal operator. -/
  untl : F → F → F

/-- A type has a since temporal operator. -/
class HasSince (F : Type*) where
  /-- The since temporal operator. -/
  snce : F → F → F

/-- A type has a next-step temporal operator. -/
class HasNext (F : Type*) where
  /-- The next-step temporal operator. -/
  next : F → F

/-- A type has a conjunction connective. -/
class HasAnd (F : Type*) where
  /-- The conjunction connective. -/
  and : F → F → F

/-- A type has a disjunction connective. -/
class HasOr (F : Type*) where
  /-- The disjunction connective. -/
  or : F → F → F

/-- Propositional connectives: falsum and implication.

`HasAnd` and `HasOr` are defined as standalone atomic classes in this module.
When all four connectives are needed, use
`[PropositionalConnectives F] [HasAnd F] [HasOr F]`. -/
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F

/-- Future temporal connectives: propositional connectives plus until (no since, no next).

This bundle is shared by both `LTLConnectives` (which adds `HasNext`) and
`TemporalConnectives` (which adds `HasSince`). Factoring out the future fragment
allows code generic over future-only temporal logics without committing to past or
next-step operators. -/
class FutureTemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F

/-- LTL connectives: future temporal connectives plus a primitive next-step operator.

Linear Temporal Logic uses `next` as a primitive rather than deriving it from `until`
(the encoding `next φ = φ U ⊥` does not hold in all models). `FutureTemporalConnectives`
provides `bot`, `imp`, and `untl`; this bundle adds `next`. -/
class LTLConnectives (F : Type*) extends FutureTemporalConnectives F, HasNext F

/-- Temporal connectives: propositional connectives plus until and since.

Extends `FutureTemporalConnectives` with the `since` operator, forming the standard
two-sorted temporal signature (future + past). -/
class TemporalConnectives (F : Type*) extends FutureTemporalConnectives F, HasSince F

end Cslib.Logic
