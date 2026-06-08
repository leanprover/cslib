/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

module

public import Cslib.Init

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
- **Derived connectives**: `LukasiewiczDerived` for `neg`, `top`, `or`, `and` from `bot`/`imp`

Each concrete formula type duplicates its constructors (Lean 4 cannot extend inductives)
and registers as an instance of the appropriate bundled class.
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

/-- Lukasiewicz-style derived connectives from `bot` and `imp`.
    Provides `neg`, `top`, `or`, `and` as abbreviations. -/
class LukasiewiczDerived (F : Type*) [HasBot F] [HasImp F] where
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
