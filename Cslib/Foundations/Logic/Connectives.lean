/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

/-! # Connective Typeclasses for Composable Logics

This module defines a typeclass hierarchy for logical connectives, shared across the four
logic levels (Propositional, Modal, Temporal, Bimodal). Each formula type registers itself
as an instance of the appropriate connective class, enabling polymorphic axiom definitions
and notation.

## Design

The hierarchy follows the Foundation pattern (FormalizedFormalLogic/Foundation):
- **Atomic classes**: `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`
- **Bundled classes**: `PropositionalConnectives`, `ModalConnectives`,
  `TemporalConnectives`, `BimodalConnectives`
- **Derived connectives**: `ImpBotDerived` for `neg`, `top`, `or`, `and` from `bot`/`imp`

Each concrete formula type duplicates its constructors (Lean 4 cannot extend inductives)
and registers as an instance of the appropriate bundled class.

Falsum and implication are taken as the only propositional primitives because `{imp, bot}`
is functionally complete for classical logic: every other connective is definable, so it can
be a derived `abbrev` rather than a constructor. This keeps the inductive formula types as
small as possible -- minimising the case count in every recursion and induction over formulas
-- and lets the derived connectives unfold to `imp`/`bot` definitionally, so reasoning about
`¬`, `∧`, `∨`, and `↔` needs no separate axioms or bridging lemmas.


## References

* [A. Church, *Introduction to Mathematical Logic*][Church1956]
* [A. Heyting, *Die formalen Regeln der intuitionistischen Logik*][Heyting1930]
* [G. Gentzen, *Untersuchungen über das logische Schließen*][Gentzen1935]
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Chapter 1
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

/-- A type has a necessity (box) modality. -/
class HasBox (F : Type*) where
  /-- The necessity/box modality. -/
  box : F → F

/-- A type has an until temporal operator. -/
class HasUntil (F : Type*) where
  /-- The until temporal operator. -/
  untl : F → F → F

/-- A type has a since temporal operator. -/
class HasSince (F : Type*) where
  /-- The since temporal operator. -/
  snce : F → F → F

/-- Propositional connectives: falsum and implication. -/
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F

/-- Modal connectives: propositional connectives plus necessity. -/
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F

/-- Temporal connectives: propositional connectives plus until and since. -/
class TemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F, HasSince F

/-- Bimodal connectives: modal connectives plus until and since.
    Note: we extend `ModalConnectives` and add `HasUntil`/`HasSince` directly
    rather than extending `TemporalConnectives`, to avoid a typeclass diamond. -/
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F

/-- Derived connectives definable from `bot` and `imp` alone.

Provides `neg`, `top`, `or`, `and` as abbreviations: negation is implication to falsum
(`neg φ := imp φ bot`), verum is `imp bot bot`, disjunction is `imp (neg φ) ψ`, and conjunction
is `neg (imp φ (neg ψ))`. These are forced once `{imp, bot}` is fixed as the primitive basis --
each is the truth-functional definition of the connective in terms of implication and falsum --
so the choice carries no information beyond the basis itself.

**Status**: This class is intentionally uninstantiated. Each concrete formula type
(PL.Proposition, Modal.Proposition, Temporal.Formula, Bimodal.Formula) defines its
own `abbrev` connectives directly on the inductive constructors, which are
definitionally equal to these defaults. Registering typeclass instances would add
resolution overhead at every use site with no benefit, since the `abbrev` definitions
already compute. The class is retained as a specification artifact and for potential
future use in polymorphic proof-system abstractions that need to quantify over derived
connectives generically. -/
class ImpBotDerived (F : Type*) [HasBot F] [HasImp F] where
  /-- Negation: `neg φ := imp φ bot` -/
  neg : F → F := fun φ => HasImp.imp φ HasBot.bot
  /-- Top/verum: `top := imp bot bot` -/
  top : F := HasImp.imp HasBot.bot HasBot.bot
  /-- Disjunction: `or φ ψ := imp (neg φ) ψ` where `neg φ := imp φ bot` -/
  or : F → F → F := fun φ ψ => HasImp.imp (HasImp.imp φ HasBot.bot) ψ
  /-- Conjunction: `and φ ψ := neg (imp φ (neg ψ))` -/
  and : F → F → F := fun φ ψ =>
    HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot

end Cslib.Logic
