/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Algebraic.UltrafilterMCS
import Cslib.Logics.Bimodal.Metalogic.Bundle.CanonicalFrame
import Cslib.Logics.Bimodal.Semantics.TaskFrame

/-!
# D-Parametric Canonical TaskFrame

This module defines a D-parametric canonical TaskFrame construction for the
Lindenbaum-Tarski algebraic completeness theorem.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/ParametricCanonical.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricCanonical

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.Algebraic.UltrafilterMCS

variable {Atom : Type}

/-- Parametric canonical world state: a maximal consistent set packaged as a subtype. -/
def ParametricCanonicalWorldState (Atom : Type) (fc : FrameClass := FrameClass.Base) :=
  { M : Set (Formula Atom) // SetMaximalConsistent (fc := fc) M }

section TaskRel

variable {fc : FrameClass} {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/-- Parametric canonical task relation: forward accessibility with converse for negative durations. -/
def parametric_canonical_task_rel (M : ParametricCanonicalWorldState Atom fc) (d : D)
    (N : ParametricCanonicalWorldState Atom fc) : Prop :=
  if d > 0 then ExistsTask M.val N.val
  else if d < 0 then ExistsTask N.val M.val
  else M = N

omit [IsOrderedAddMonoid D] in
/-- Nullity identity: parametric_canonical_task_rel M 0 N iff M = N. -/
theorem parametric_task_rel_nullity_identity (M N : ParametricCanonicalWorldState Atom fc) :
    parametric_canonical_task_rel M (0 : D) N ↔ M = N := by
  unfold parametric_canonical_task_rel
  simp only [lt_irrefl, ite_false]

/-- Forward compositionality. -/
theorem parametric_task_rel_forward_comp
    (M W V : ParametricCanonicalWorldState Atom fc) (x y : D)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : parametric_canonical_task_rel M x W)
    (h2 : parametric_canonical_task_rel W y V) :
    parametric_canonical_task_rel M (x + y) V := by
  unfold parametric_canonical_task_rel at *
  by_cases hx_pos : x > 0
  · have hx_neg : ¬(x < 0) := not_lt.mpr (le_of_lt hx_pos)
    simp only [hx_pos, ite_true, hx_neg, ite_false] at h1
    by_cases hy_pos : y > 0
    · have hy_neg : ¬(y < 0) := not_lt.mpr (le_of_lt hy_pos)
      simp only [hy_pos, ite_true, hy_neg, ite_false] at h2
      have hsum_pos : x + y > 0 := add_pos hx_pos hy_pos
      simp only [hsum_pos, ite_true]
      exact canonicalR_transitive M.val W.val V.val M.property h1 h2
    · have hy_eq : y = 0 := le_antisymm (not_lt.mp hy_pos) hy
      subst hy_eq
      have hy_neg : ¬((0 : D) < 0) := lt_irrefl 0
      have hy_npos : ¬((0 : D) > 0) := lt_irrefl 0
      simp only [hy_npos, ite_false] at h2
      subst h2
      simp only [add_zero, hx_pos, ite_true]
      exact h1
  · have hx_eq : x = 0 := le_antisymm (not_lt.mp hx_pos) hx
    subst hx_eq
    have hx_neg : ¬((0 : D) < 0) := lt_irrefl 0
    have hx_npos : ¬((0 : D) > 0) := lt_irrefl 0
    simp only [hx_npos, ite_false] at h1
    subst h1
    simp only [zero_add]
    exact h2

/-- Converse axiom. -/
theorem parametric_task_rel_converse
    (M : ParametricCanonicalWorldState Atom fc) (d : D)
    (N : ParametricCanonicalWorldState Atom fc) :
    parametric_canonical_task_rel M d N ↔ parametric_canonical_task_rel N (-d) M := by
  unfold parametric_canonical_task_rel
  by_cases hd_pos : d > 0
  · have hd_neg : ¬(d < 0) := not_lt.mpr (le_of_lt hd_pos)
    have hnd_neg : -d < 0 := neg_neg_of_pos hd_pos
    have hnd_npos : ¬(-d > 0) := not_lt.mpr (le_of_lt hnd_neg)
    simp only [hd_pos, ite_true, hd_neg, ite_false, hnd_npos, hnd_neg]
  · by_cases hd_neg : d < 0
    · have hd_npos : ¬(d > 0) := not_lt.mpr (le_of_lt hd_neg)
      have hnd_pos : -d > 0 := neg_pos_of_neg hd_neg
      have hnd_nneg : ¬(-d < 0) := not_lt.mpr (le_of_lt hnd_pos)
      simp only [hd_npos, ite_false, hd_neg, ite_true, hnd_pos, hnd_nneg]
    · have hd_eq : d = 0 := le_antisymm (not_lt.mp hd_pos) (not_lt.mp hd_neg)
      subst hd_eq
      simp only [neg_zero, lt_irrefl, ite_false]
      exact ⟨Eq.symm, Eq.symm⟩

/-- The D-parametric canonical task frame. -/
noncomputable def ParametricCanonicalTaskFrame : TaskFrame D where
  WorldState := ParametricCanonicalWorldState Atom fc
  task_rel := parametric_canonical_task_rel
  nullity_identity := parametric_task_rel_nullity_identity
  forward_comp := fun M W V x y hx hy h1 h2 =>
    parametric_task_rel_forward_comp M W V x y hx hy h1 h2
  converse := parametric_task_rel_converse

omit [IsOrderedAddMonoid D] in
/-- Nullity theorem: zero-duration task is reflexive. -/
theorem parametric_task_rel_nullity (M : ParametricCanonicalWorldState Atom fc) :
    parametric_canonical_task_rel M (0 : D) M :=
  (parametric_task_rel_nullity_identity M M).mpr rfl

omit [IsOrderedAddMonoid D] in
/-- Forward-positive case. -/
theorem parametric_task_rel_pos {d : D} (hd : d > 0)
    (M N : ParametricCanonicalWorldState Atom fc) :
    parametric_canonical_task_rel M d N ↔ ExistsTask M.val N.val := by
  unfold parametric_canonical_task_rel
  simp only [hd, ite_true]

omit [IsOrderedAddMonoid D] in
/-- Zero case. -/
theorem parametric_task_rel_zero (M N : ParametricCanonicalWorldState Atom fc) :
    parametric_canonical_task_rel M (0 : D) N ↔ M = N :=
  parametric_task_rel_nullity_identity M N

omit [IsOrderedAddMonoid D] in
/-- Negative case. -/
theorem parametric_task_rel_neg {d : D} (hd : d < 0)
    (M N : ParametricCanonicalWorldState Atom fc) :
    parametric_canonical_task_rel M d N ↔ ExistsTask N.val M.val := by
  unfold parametric_canonical_task_rel
  have hd_npos : ¬(d > 0) := not_lt.mpr (le_of_lt hd)
  simp only [hd_npos, ite_false, hd, ite_true]

end TaskRel

end Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricCanonical
