/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Semantics.TaskFrame
public import Cslib.Logics.Bimodal.Semantics.WorldHistory
public import Cslib.Logics.Bimodal.Syntax.Formula

/-!
# TaskModel - Task Models with Valuation

This module defines task models, which extend task frames with valuation
functions.

## Main Definitions

- `TaskModel`: Task model structure with valuation function
- Example models for testing

## Implementation Notes

- Valuation assigns truth values to atoms at each world state
- Valuation function: `WorldState → Atom → Prop`
- Models provide complete semantic interpretation for TM formulas
- Parametrized by `Atom : Type*` for composability with cslib's
  polymorphic formula type

## Note on Variable Naming

Frame variables use `ℱ` (Unicode U+2131) rather than `F` because
`F` is a scoped notation for `Formula.someFuture` within the
`Cslib.Logic.Bimodal` namespace.
-/

@[expose] public section

namespace Cslib.Logic.Bimodal

/--
Task model for bimodal logic TM.

A task model extends a task frame with a valuation function that
determines which atomic propositions are true at each world state.
-/
structure TaskModel (Atom : Type*) {D : Type*}
    [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    (ℱ : TaskFrame D) where
  /-- Valuation function: assigns truth values to atomic propositions
  at world states. -/
  valuation : ℱ.WorldState → Atom → Prop

namespace TaskModel

variable {Atom : Type*} {D : Type*} [AddCommGroup D]
  [LinearOrder D] [IsOrderedAddMonoid D] {ℱ : TaskFrame D}

/--
Simple model where all atoms are false everywhere.
-/
def allFalse : TaskModel Atom ℱ where
  valuation := fun _ _ => False

/--
Simple model where all atoms are true everywhere.
-/
def allTrue : TaskModel Atom ℱ where
  valuation := fun _ _ => True

end TaskModel

/--
A finite task model is simply a task model over a finite task frame.
-/
abbrev FiniteTaskModel (Atom : Type*) {D : Type*}
    [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    (ℱ : FiniteTaskFrame D) :=
  TaskModel Atom ℱ.toTaskFrame

end Cslib.Logic.Bimodal
