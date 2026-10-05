/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Measurable bitvectors

Bitvectors carry the discrete measurable space, like `Bool` and `Fin` in Mathlib.
-/

public section

instance BitVec.instMeasurableSpace (n : ℕ) : MeasurableSpace (BitVec n) := ⊤

instance BitVec.instMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (BitVec n) := ⟨fun _ => trivial⟩
