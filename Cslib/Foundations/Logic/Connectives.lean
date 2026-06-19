/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

/-! # Connective Typeclasses for Composable Logics

This module defines a typeclass hierarchy for logical connectives, shared across propositional
and modal logic levels. Each formula type registers itself as an instance of the appropriate
connective class, enabling polymorphic axiom definitions and notation.

## Design

The hierarchy adopts a hybrid design,
following the operator-typeclass direction of fmontesi's PR #607 (one class per operator):
- **Atomic classes**: `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`
- **Bundled classes**: `PropositionalConnectives`, `ModalConnectives`

Conjunction (`HasAnd`) and disjunction (`HasOr`) are treated as independent primitives rather
than Łukasiewicz-derived connectives. The classical encodings `φ ∧ ψ := ¬(φ → ¬ψ)` and
`φ ∨ ψ := ¬φ → ψ` are only propositionally equivalent to `∧` and `∨` in classical logic
([Avigad2022]); they fail in intuitionistic and minimal logic. Making `and`
and `or` primitive via `HasAnd`/`HasOr` supports all three logic strengths with a single
typeclass hierarchy.

Negation and verum stay derived: each concrete formula type defines `neg φ := φ → ⊥` and
`top := ⊥ → ⊥` as `abbrev`s, which are valid in minimal, intuitionistic, and classical logic
alike, so no typeclass machinery is needed for them.

## References

* [J. Avigad, *Mathematical Logic and Computation*][Avigad2022]
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

/-- A type has a necessity/box modality.

Box represents universal quantification over accessible worlds (`∀ w', r w w' → φ`),
distributes over implication (axiom K), and is the subject of the necessitation rule.
In classical systems,
diamond (possibility) is derived as `¬□¬φ`. Non-classical modal logics (intuitionistic,
minimal) require a separate `HasDia` typeclass, since `□` and `◇` become independent
operators in those settings. -/
class HasBox (F : Type*) where
  /-- The necessity/box modality. -/
  box : F → F

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

/-- Modal connectives: propositional connectives plus box (necessity).

Diamond (possibility) is derivable from box and propositional connectives via
classical negation (`◇φ := ¬□¬φ`) and need not appear in the typeclass. Non-classical modal
logics (intuitionistic, minimal) require extending this class with a primitive `HasDia` once
those formula types are formalized. -/
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F

end Cslib.Logic
