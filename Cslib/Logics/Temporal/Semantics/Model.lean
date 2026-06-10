/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Syntax.Formula

/-! # Temporal Model on Linear Orders

This module defines the `TemporalModel` structure for temporal logic semantics
on linear orders.

## Design Rationale

A temporal model on a linear order is simply a valuation assigning truth values
to atoms at each time point. The linear order on the time domain `D` provides
all the temporal structure needed — no accessibility relation (that would be
modal logic), no task relation (that would be bimodal logic), and no world
histories. The frame IS the linear order on `D`; the model adds a valuation.

## Main Definitions

- `TemporalModel D Atom`: A temporal model with time domain `D` (a linear order)
  and atom type `Atom`, consisting of a valuation `D → Atom → Prop`.
- `TemporalModel.allFalse`: Model where all atoms are false everywhere.
- `TemporalModel.allTrue`: Model where all atoms are true everywhere.
- `TemporalModel.constant`: Model with a constant (time-independent) valuation.
-/

@[expose] public section

namespace Cslib.Logic.Temporal

/-- A temporal model on a linear order.

The time domain `D` is equipped with a `LinearOrder` instance (provided as a
typeclass parameter). The model consists solely of a valuation assigning a
truth value to each atom at each time point. -/
structure TemporalModel (D : Type*) [LinearOrder D] (Atom : Type*) where
  /-- Valuation assigning truth values to atoms at each time point. -/
  valuation : D → Atom → Prop

variable {D : Type*} [LinearOrder D] {Atom : Type*}

/-- The model where all atoms are false at every time point. -/
def TemporalModel.allFalse : TemporalModel D Atom where
  valuation := fun _ _ => False

/-- The model where all atoms are true at every time point. -/
def TemporalModel.allTrue : TemporalModel D Atom where
  valuation := fun _ _ => True

/-- A model with a constant (time-independent) valuation. -/
def TemporalModel.constant (v : Atom → Prop) : TemporalModel D Atom where
  valuation := fun _ p => v p

end Cslib.Logic.Temporal
