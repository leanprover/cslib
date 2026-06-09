/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.ClosureMCS
import Cslib.Logics.Bimodal.Semantics.Validity
import Cslib.Logics.Bimodal.Semantics.Truth
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Quotient

/-!
# Filtration Construction for FMP

This module defines the filtration equivalence and quotient model construction
for the Finite Model Property (FMP).

## Overview

Filtration is a technique to construct finite models from infinite ones:
1. Define equivalence: w ≡_φ v iff they agree on truth of all closure formulas
2. Take quotient of world states by this equivalence
3. Define filtered accessibility as lifting of original accessibility
4. Show the filtered model is finite (bounded by 2^|closure φ|)

## Main Definitions

- `MCSFiltrationEquiv`: Equivalence relation based on membership agreement on closure
- `ClosureMCSSetoid`: The setoid structure for quotient construction
- `FilteredWorld`: Quotient type of closure MCS under filtration equivalence
- `FilteredTaskFrame`: Task frame on filtered worlds

## References

- Blackburn, de Rijke, Venema: Modal Logic (Ch 2.3 Filtrations)
- Ported from BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/Filtration.lean
-/

namespace Cslib.Logic.Bimodal.Metalogic.Decidability.FMP

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type} [DecidableEq Atom]

/-!
## MCS-Based Filtration Equivalence

Two closure MCS are equivalent if they contain exactly the same
formulas from the subformula closure.
-/

/--
MCS-based filtration equivalence.

Two sets are equivalent if they agree on membership for all
formulas in the subformula closure.
-/
def MCSFiltrationEquiv (phi : Formula Atom)
    (Omega Theta : Set (Formula Atom)) : Prop :=
  ∀ ψ ∈ subformulaClosure phi, (ψ ∈ Omega ↔ ψ ∈ Theta)

/--
MCS filtration equivalence is reflexive.
-/
theorem mcs_filtration_equiv_refl (phi : Formula Atom) (Omega : Set (Formula Atom)) :
    MCSFiltrationEquiv phi Omega Omega := by
  intro ψ _
  rfl

/--
MCS filtration equivalence is symmetric.
-/
theorem mcs_filtration_equiv_symm (phi : Formula Atom)
    {Omega Theta : Set (Formula Atom)}
    (h : MCSFiltrationEquiv phi Omega Theta) :
    MCSFiltrationEquiv phi Theta Omega := by
  intro ψ hψ
  exact (h ψ hψ).symm

/--
MCS filtration equivalence is transitive.
-/
theorem mcs_filtration_equiv_trans (phi : Formula Atom)
    {Omega Theta Sigma : Set (Formula Atom)}
    (h1 : MCSFiltrationEquiv phi Omega Theta)
    (h2 : MCSFiltrationEquiv phi Theta Sigma) :
    MCSFiltrationEquiv phi Omega Sigma := by
  intro ψ hψ
  exact (h1 ψ hψ).trans (h2 ψ hψ)

/--
MCS filtration equivalence is an equivalence relation.
-/
theorem mcs_filtration_equiv_equivalence (phi : Formula Atom) :
    Equivalence (MCSFiltrationEquiv phi) :=
  ⟨mcs_filtration_equiv_refl phi,
   fun h => mcs_filtration_equiv_symm phi h,
   fun h1 h2 => mcs_filtration_equiv_trans phi h1 h2⟩

/--
The setoid for MCS filtration.
-/
def MCSFiltrationSetoid (phi : Formula Atom) : Setoid (Set (Formula Atom)) where
  r := MCSFiltrationEquiv phi
  iseqv := mcs_filtration_equiv_equivalence phi

/-!
## Closure MCS Bundle

A closure MCS bundled with its proof of maximality.
-/

/--
A closure MCS bundled with its proof.
-/
structure ClosureMCSBundle (phi : Formula Atom) where
  /-- The underlying set of formulas -/
  carrier : Set (Formula Atom)
  /-- Proof that the carrier is a closure MCS -/
  is_mcs : ClosureMCS phi carrier

/--
Filtration equivalence on bundled closure MCS.
-/
def ClosureMCSEquiv (phi : Formula Atom)
    (Omega Theta : ClosureMCSBundle phi) : Prop :=
  MCSFiltrationEquiv phi Omega.carrier Theta.carrier

/--
ClosureMCS equivalence is an equivalence relation.
-/
theorem closure_mcs_equiv_equivalence (phi : Formula Atom) :
    Equivalence (ClosureMCSEquiv phi) :=
  ⟨fun Omega => mcs_filtration_equiv_refl phi Omega.carrier,
   fun h => mcs_filtration_equiv_symm phi h,
   fun h1 h2 => mcs_filtration_equiv_trans phi h1 h2⟩

/--
Setoid for closure MCS.
-/
def ClosureMCSSetoid (phi : Formula Atom) : Setoid (ClosureMCSBundle phi) where
  r := ClosureMCSEquiv phi
  iseqv := closure_mcs_equiv_equivalence phi

/-!
## Filtered World Type
-/

/--
Filtered world type: quotient of closure MCS bundles by equivalence.

Each equivalence class represents a "world" in the filtered model.
The number of equivalence classes is bounded by 2^|subformulaClosure phi|.
-/
def FilteredWorld (phi : Formula Atom) :=
  Quotient (ClosureMCSSetoid phi)

/--
Quotient map: lift a closure MCS bundle to its equivalence class.
-/
def toFilteredWorld (phi : Formula Atom)
    (Omega : ClosureMCSBundle phi) : FilteredWorld phi :=
  Quotient.mk (ClosureMCSSetoid phi) Omega

/-!
## Filtered Task Frame

We construct a task frame on the filtered worlds.

For the FMP construction, we use a refined filtration where
the task relation is universal at nonzero durations and
identity at zero duration.
-/

variable (D : Type*) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/--
Refined filtered task relation.

At duration 0: relate only identical equivalence classes
At non-zero duration: universal relation
-/
def refinedFilteredTaskRel (phi : Formula Atom)
    (w : FilteredWorld phi) (d : D) (u : FilteredWorld phi) : Prop :=
  if d = 0 then w = u else True

/--
The refined filtered task frame with proper nullity_identity.
-/
noncomputable def RefinedFilteredTaskFrame (phi : Formula Atom) :
    TaskFrame D where
  WorldState := FilteredWorld phi
  task_rel w d u := if d = 0 then w = u else True
  nullity_identity := by
    intro w u
    simp
  forward_comp := by
    intro w u v x y hx hy h_wu h_uv
    split
    · next hxy =>
      have hx0 : x = 0 := by
        have h1 : y = -x := (neg_eq_of_add_eq_zero_right hxy).symm
        rw [h1] at hy
        exact le_antisymm (neg_nonneg.mp hy) hx
      have hy0 : y = 0 := by
        have h1 : y = -x := (neg_eq_of_add_eq_zero_right hxy).symm
        rw [hx0] at h1; simp at h1; exact h1
      have h1 : w = u := by simpa [hx0] using h_wu
      have h2 : u = v := by simpa [hy0] using h_uv
      exact h1.trans h2
    · trivial
  converse := by
    intro w d u
    constructor
    · intro h
      by_cases hd : d = 0
      · subst hd; simp only [neg_zero, ↓reduceIte] at h ⊢; exact h.symm
      · simp only [show -d ≠ 0 from neg_ne_zero.mpr hd, ↓reduceIte]
    · intro h
      by_cases hd : d = 0
      · subst hd; simp only [neg_zero, ↓reduceIte] at h ⊢; exact h.symm
      · simp only [hd, ↓reduceIte]

/-!
## Equivalence Class Representatives

For working with filtered worlds, we often need to extract representatives.
-/

/--
Every filtered world has a representative closure MCS.
-/
theorem filtered_world_has_rep (phi : Formula Atom)
    (w : FilteredWorld phi) :
    ∃ Omega : ClosureMCSBundle phi, toFilteredWorld phi Omega = w := by
  exact Quotient.exists_rep w

/--
Lift a property from representatives to the quotient (if it respects equivalence).
-/
theorem filtered_world_lift_prop (phi : Formula Atom)
    (Prop_ : ClosureMCSBundle phi → Prop)
    (h_resp : ∀ Omega Theta : ClosureMCSBundle phi,
      ClosureMCSEquiv phi Omega Theta → (Prop_ Omega ↔ Prop_ Theta))
    (w : FilteredWorld phi) :
    (∀ Omega : ClosureMCSBundle phi, toFilteredWorld phi Omega = w → Prop_ Omega) ↔
    (∃ Omega : ClosureMCSBundle phi, toFilteredWorld phi Omega = w ∧ Prop_ Omega) := by
  constructor
  · intro h_all
    obtain ⟨Omega, hOmega⟩ := filtered_world_has_rep phi w
    exact ⟨Omega, hOmega, h_all Omega hOmega⟩
  · intro ⟨Omega, hOmega, hPOmega⟩ Theta hTheta
    have h_eq : toFilteredWorld phi Omega = toFilteredWorld phi Theta :=
      hOmega.trans hTheta.symm
    have h_equiv : ClosureMCSEquiv phi Omega Theta := Quotient.exact h_eq
    exact (h_resp Omega Theta h_equiv).mp hPOmega

/-!
## Formula Membership in Filtered Worlds

A key property: membership of closure formulas is well-defined on equivalence classes.
-/

/--
Formula membership in a closure MCS respects filtration equivalence
(for formulas in the closure).
-/
theorem formula_mem_respects_equiv (phi ψ : Formula Atom)
    (hψ : ψ ∈ subformulaClosure phi)
    {Omega Theta : ClosureMCSBundle phi}
    (h : ClosureMCSEquiv phi Omega Theta) :
    ψ ∈ Omega.carrier ↔ ψ ∈ Theta.carrier :=
  h ψ hψ

/--
Lift formula membership to filtered worlds (for closure formulas).
-/
def filteredWorldMem (phi ψ : Formula Atom) (hψ : ψ ∈ subformulaClosure phi)
    (w : FilteredWorld phi) : Prop :=
  Quotient.lift (s := ClosureMCSSetoid phi)
    (fun (Omega : ClosureMCSBundle phi) => ψ ∈ Omega.carrier)
    (fun (Omega Theta : ClosureMCSBundle phi)
      (h : ClosureMCSEquiv phi Omega Theta) =>
      propext (formula_mem_respects_equiv phi ψ hψ h)) w

/--
Filtered world membership agrees with representative membership.
-/
theorem filteredWorldMem_iff (phi ψ : Formula Atom)
    (hψ : ψ ∈ subformulaClosure phi)
    (Omega : ClosureMCSBundle phi) :
    filteredWorldMem phi ψ hψ (toFilteredWorld phi Omega) ↔ ψ ∈ Omega.carrier := by
  simp only [filteredWorldMem, toFilteredWorld]
  rfl

end Cslib.Logic.Bimodal.Metalogic.Decidability.FMP
