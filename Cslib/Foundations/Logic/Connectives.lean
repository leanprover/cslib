/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

/-! # Connective Typeclasses for Propositional Logic

This module defines a typeclass hierarchy for propositional logical connectives. Each formula
type registers itself as an instance of the appropriate connective class, enabling polymorphic
axiom definitions and notation that work uniformly across different formula types.

## Design

The hierarchy adopts a hybrid five-primitive propositional signature `{atom, bot, imp, and, or}`,
following the operator-typeclass direction of fmontesi's PR #607 (one class per operator):
- **Atomic classes**: `HasBot`, `HasImp`, `HasAnd`, `HasOr`
- **Bundled class**: `PropositionalConnectives` (extends `HasBot` and `HasImp`)

Conjunction (`HasAnd`) and disjunction (`HasOr`) are treated as independent primitives rather
than Łukasiewicz-derived connectives. The classical encodings `φ ∧ ψ := ¬(φ → ¬ψ)` and
`φ ∨ ψ := ¬φ → ψ` are only propositionally equivalent to `∧` and `∨` in classical logic
([Wajsberg1938], [McKinsey1939]); they fail in intuitionistic and minimal logic. Making `and`
and `or` primitive via `HasAnd`/`HasOr` supports all three logic strengths with a single
typeclass hierarchy.

Negation and verum stay derived: each concrete formula type defines `neg φ := φ → ⊥` and
`top := ⊥ → ⊥` as `abbrev`s, which are valid in minimal, intuitionistic, and classical logic
alike, so no typeclass machinery is needed for them.

## Why Not Mathlib's `Bot` / `HImp`?

Mathlib's `Bot` class is for algebraic bottom elements (lattice theory), and `HImp` is for
Heyting implication in a lattice. Neither is appropriate here:
- Formula types are not lattices; they are freely generated algebras.
- We need `imp` to be a binary constructor (taking two formula arguments), not a binary
  operation on a lattice.
- The typeclass hierarchy here enables polymorphic axiom definitions that quantify over any
  formula type satisfying the appropriate connective class, independently of any algebraic
  structure.

## References

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

/-- A type has a conjunction connective. -/
class HasAnd (F : Type*) where
  /-- The conjunction connective. -/
  and : F → F → F

/-- A type has a disjunction connective. -/
class HasOr (F : Type*) where
  /-- The disjunction connective. -/
  or : F → F → F

/-- Propositional connectives: falsum, implication, conjunction, and disjunction.

`HasAnd` and `HasOr` are included because all four connectives are needed for a
five-primitive propositional signature `{atom, bot, imp, and, or}`. This bundled class
allows axiom schemas to be stated polymorphically over any formula type providing
all four connectives.

Note: this does not extend `HasAnd` and `HasOr` directly to avoid forcing all
formula types to bundle conjunction and disjunction together with the minimal
`HasBot`/`HasImp` interface. When all four are needed, use
`[PropositionalConnectives F] [HasAnd F] [HasOr F]`. -/
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F

end Cslib.Logic
