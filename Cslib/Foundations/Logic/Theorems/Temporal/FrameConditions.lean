/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
import Cslib.Init

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Int.SuccPred

/-! # Frame Condition Typeclasses for Temporal Logic

Marker typeclasses for temporal frame conditions. These bundle the underlying
Mathlib typeclasses required by temporal logic semantics.

## Hierarchy

```
LinearTemporalFrame (AddCommGroup + LinearOrder + IsOrderedAddMonoid)
        |
   SerialFrame (+ Nontrivial + NoMaxOrder + NoMinOrder)
      /    \
DenseTemporalFrame       DiscreteTemporalFrame
(+ DenselyOrdered)        (+ SuccOrder + PredOrder + IsSuccArchimedean)
```

## Standard Instances

- `Int` is a `DiscreteTemporalFrame`
-/

@[expose] public section

namespace Cslib.Logic.Temporal.FrameConditions

/-! ## Base Typeclass: LinearTemporalFrame -/

/-- Base typeclass for linear temporal frames. -/
class LinearTemporalFrame (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] : Prop

/-! ## Serial Frame -/

/-- Serial temporal frame: no maximum or minimum elements. -/
class SerialFrame (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] : Prop where
  toLinearTemporalFrame : LinearTemporalFrame D := {}

instance (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [SerialFrame D] :
    LinearTemporalFrame D :=
  SerialFrame.toLinearTemporalFrame

/-! ## Dense Temporal Frame -/

/-- Dense temporal frame: densely ordered times. -/
class DenseTemporalFrame (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]
    [DenselyOrdered D] : Prop where
  toSerialFrame : SerialFrame D := {}

instance (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [DenselyOrdered D]
    [DenseTemporalFrame D] : SerialFrame D :=
  DenseTemporalFrame.toSerialFrame

/-! ## Discrete Temporal Frame -/

/-- Discrete temporal frame: successor and predecessor structure. -/
class DiscreteTemporalFrame (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] : Prop where
  toSerialFrame : SerialFrame D := {}

instance (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [SuccOrder D] [PredOrder D]
    [IsSuccArchimedean D] [DiscreteTemporalFrame D] : SerialFrame D :=
  DiscreteTemporalFrame.toSerialFrame

/-! ## Standard Instances for Int -/

instance : LinearTemporalFrame Int := ⟨⟩
instance : SerialFrame Int := {}
instance : DiscreteTemporalFrame Int := {}

end Cslib.Logic.Temporal.FrameConditions
