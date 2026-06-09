/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.Filtration
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness Theorem for Filtered Models

This module proves that the filtered model has bounded cardinality.

## Overview

The key insight is that equivalence classes of closure MCS are determined
by their membership on the subformula closure. Since the closure is finite,
there are at most 2^|closure| distinct equivalence classes.

## Main Results

- `FilteredWorld.finite`: The filtered world type is finite
- `FiniteFilteredFrame`: The filtered task frame is finite

## References

- Blackburn, de Rijke, Venema: Modal Logic (Ch 2.3)
- Ported from BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/FiniteModel.lean
-/

namespace Cslib.Logic.Bimodal.Metalogic.Decidability.FMP

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type} [DecidableEq Atom]

/-!
## Characteristic Sets

Each closure MCS is determined by which closure formulas it contains.
We represent this as a subset (Set) of the closure.
-/

/--
The characteristic set of a closure MCS: the set of closure formulas it contains.
-/
def characteristicSet (phi : Formula Atom) (Omega : ClosureMCSBundle phi) :
    Set (subformulaClosure phi) :=
  {x | x.val ∈ Omega.carrier}

/--
Two closure MCS have the same characteristic set iff they are equivalent.
-/
theorem characteristicSet_eq_iff_equiv (phi : Formula Atom)
    (Omega Theta : ClosureMCSBundle phi) :
    characteristicSet phi Omega = characteristicSet phi Theta ↔
    ClosureMCSEquiv phi Omega Theta := by
  constructor
  · intro h_eq ψ hψ
    have h1 : (⟨ψ, hψ⟩ : subformulaClosure phi) ∈ characteristicSet phi Omega ↔
              (⟨ψ, hψ⟩ : subformulaClosure phi) ∈ characteristicSet phi Theta := by
      rw [h_eq]
    simp only [characteristicSet, Set.mem_setOf_eq] at h1
    exact h1
  · intro h_equiv
    ext ⟨ψ, hψ⟩
    simp only [characteristicSet, Set.mem_setOf_eq]
    exact h_equiv ψ hψ

/--
The characteristic set respects equivalence.
-/
theorem characteristicSet_respects_equiv (phi : Formula Atom)
    {Omega Theta : ClosureMCSBundle phi} (h : ClosureMCSEquiv phi Omega Theta) :
    characteristicSet phi Omega = characteristicSet phi Theta :=
  (characteristicSet_eq_iff_equiv phi Omega Theta).mpr h

/--
Lift characteristic set to filtered worlds.
-/
def filteredCharacteristicSet (phi : Formula Atom) (w : FilteredWorld phi) :
    Set (subformulaClosure phi) :=
  Quotient.lift (characteristicSet phi)
    (fun Omega Theta h => characteristicSet_respects_equiv phi h) w

/--
The filtered characteristic set map is injective.
-/
theorem filteredCharacteristicSet_injective (phi : Formula Atom) :
    Function.Injective (filteredCharacteristicSet phi) := by
  intro w v h
  -- Get representatives
  obtain ⟨Omega, hOmega⟩ := Quotient.exists_rep w
  obtain ⟨Theta, hTheta⟩ := Quotient.exists_rep v
  -- Show they are equivalent
  have h_char : characteristicSet phi Omega = characteristicSet phi Theta := by
    simp only [← hOmega, ← hTheta, filteredCharacteristicSet] at h
    exact h
  have h_equiv : ClosureMCSEquiv phi Omega Theta :=
    (characteristicSet_eq_iff_equiv phi Omega Theta).mp h_char
  -- Use quotient exactness
  rw [← hOmega, ← hTheta]
  exact Quotient.sound h_equiv

/-!
## Main Finiteness Theorem

The filtered world type is finite.
-/

/--
The subformula closure is a Finset, which gives us a Fintype instance.
-/
instance subformulaClosure_fintype (phi : Formula Atom) :
    Fintype (subformulaClosure phi) :=
  (subformulaClosure phi).fintypeCoeSort

/--
The subformula closure elements form a finite type, so its powerset is also finite.
-/
noncomputable instance set_finite (phi : Formula Atom) :
    Finite (Set (subformulaClosure phi)) := by
  haveI : Finite (subformulaClosure phi) :=
    Finite.of_fintype (subformulaClosure phi)
  exact Set.instFinite

/--
FilteredWorld is finite because it injects into a finite type.
-/
noncomputable instance FilteredWorld.finite (phi : Formula Atom) :
    Finite (FilteredWorld phi) := by
  haveI : Finite (Set (subformulaClosure phi)) := set_finite phi
  exact Finite.of_injective (filteredCharacteristicSet phi)
    (filteredCharacteristicSet_injective phi)

/-!
## Finite Filtered Task Frame

Bundle the filtered frame with its finiteness proof.
-/

variable (D : Type*) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/--
The finite filtered task frame.

This bundles the refined filtered task frame with the proof
that its world states are finite.
-/
noncomputable def FiniteFilteredTaskFrame (phi : Formula Atom) :
    FiniteTaskFrame D where
  toTaskFrame := RefinedFilteredTaskFrame D phi
  finite_world := FilteredWorld.finite phi

/--
The finite filtered frame has the same world state type as the refined frame.
-/
theorem FiniteFilteredTaskFrame.worldState_eq (phi : Formula Atom) :
    (FiniteFilteredTaskFrame D phi).WorldState = FilteredWorld phi :=
  rfl

end Cslib.Logic.Bimodal.Metalogic.Decidability.FMP
