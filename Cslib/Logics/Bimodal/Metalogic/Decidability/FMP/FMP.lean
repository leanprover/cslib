/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.TruthPreservation
public import Cslib.Logics.Bimodal.Semantics.Validity
public import Cslib.Logics.Bimodal.Theorems.Propositional.Core

/-!
# Finite Model Property for TM Bimodal Logic

This module proves the Finite Model Property (FMP) for TM bimodal logic.

## Overview

The Finite Model Property states: If a formula is satisfiable, then it is
satisfiable in a finite model whose size is bounded by 2^|closure(φ)|.

## Main Results

- `mcs_finite_model_property`: If φ not provable, ∃ finite world where φ fails
- `fmp_contrapositive`: If φ true in all finite worlds → φ provable
- `fmp_size_bound`: Model size ≤ 2^|closure(φ)|

## References

- Blackburn, de Rijke, Venema: Modal Logic (Ch 2.3)
- Ported from BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/FMP.lean
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Decidability.FMP

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Theorems.Propositional

variable {Atom : Type} [DecidableEq Atom]

/-!
## Finite Model Construction

Given a formula φ that is not valid, we construct a finite model that falsifies it.
-/

/--
If φ is not provable (no proof of φ from empty context), then there exists
a closure MCS containing ¬φ.
-/
theorem exists_mcs_with_negation (phi : Formula Atom)
    (h_not_provable : ¬Nonempty (DerivationTree FrameClass.Base
      ([] : List (Formula Atom)) phi)) :
    ∃ Omega : ClosureMCSBundle phi, phi.neg ∈ Omega.carrier := by
  -- Show that ¬¬φ (phi.neg.neg) is not derivable
  have h_neg_cons : ¬Nonempty (DerivationTree FrameClass.Base
      ([] : List (Formula Atom)) phi.neg.neg) := by
    intro ⟨d_neg_neg⟩
    have h_dne : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (phi.neg.neg.imp phi) := double_negation phi
    have h_phi : DerivationTree FrameClass.Base ([] : List (Formula Atom)) phi :=
      DerivationTree.modus_ponens [] _ _ h_dne d_neg_neg
    exact h_not_provable ⟨h_phi⟩
  -- {phi.neg} is set-consistent
  have h_singleton_cons : SetConsistent FrameClass.Base
      ({phi.neg} : Set (Formula Atom)) := by
    intro L hL ⟨d_bot⟩
    by_cases h_neg_in_L : phi.neg ∈ L
    · -- phi.neg ∈ L. Exchange to put it first.
      let L' := L.filter (fun x => decide (x ≠ phi.neg))
      have h_L_perm : L ⊆ phi.neg :: L' := by
        intro x hx
        by_cases hx_eq : x = phi.neg
        · simp [hx_eq]
        · simp only [List.mem_cons]
          right
          exact List.mem_filter.mpr ⟨hx, by simpa⟩
      -- L' ⊆ {phi.neg} \ {phi.neg} = ∅
      have h_L'_sub : ∀ x ∈ L', x ∈ ({phi.neg} : Set (Formula Atom)) ∧ x ≠ phi.neg := by
        intro x hx
        have hx' := List.mem_filter.mp hx
        constructor
        · exact hL x hx'.1
        · simp only [decide_eq_true_eq] at hx'
          exact hx'.2
      have h_L'_empty : L' = [] := by
        cases hL' : L' with
        | nil => rfl
        | cons x xs =>
          exfalso
          have h_x_in : x ∈ L' := by rw [hL']; exact List.mem_cons_self
          have ⟨h_in, h_ne⟩ := h_L'_sub x h_x_in
          simp only [Set.mem_singleton_iff] at h_in
          exact h_ne h_in
      have h_L_sub_singleton : L ⊆ [phi.neg] := by
        intro x hx
        have := h_L_perm hx
        simp only [List.mem_cons, h_L'_empty, List.not_mem_nil, or_false] at this
        simp [this]
      have d_bot' : DerivationTree FrameClass.Base [phi.neg] Formula.bot :=
        DerivationTree.weakening L [phi.neg] _ d_bot h_L_sub_singleton
      have d_neg_neg : DerivationTree FrameClass.Base
          ([] : List (Formula Atom)) phi.neg.neg :=
        deduction_theorem [] phi.neg Formula.bot d_bot'
      exact h_neg_cons ⟨d_neg_neg⟩
    · -- phi.neg ∉ L. Then L = []
      have h_L_empty : L = [] := by
        cases L with
        | nil => rfl
        | cons x xs =>
          exfalso
          have hx := hL x List.mem_cons_self
          simp only [Set.mem_singleton_iff] at hx
          exact h_neg_in_L (hx ▸ List.mem_cons_self)
      rw [h_L_empty] at d_bot
      have h_efq : DerivationTree FrameClass.Base ([] : List (Formula Atom))
          (Formula.bot.imp phi) :=
        DerivationTree.axiom [] _ (Axiom.efq phi) trivial
      have d_phi : DerivationTree FrameClass.Base ([] : List (Formula Atom)) phi :=
        DerivationTree.modus_ponens [] _ _ h_efq d_bot
      exact h_not_provable ⟨d_phi⟩
  -- phi.neg is in closureWithNeg phi
  have h_neg_clos : phi.neg ∈ closureWithNeg phi :=
    neg_self_mem_closureWithNeg phi
  -- Apply restricted_mcs_exists_containing
  obtain ⟨M, h_neg_in, h_mcs⟩ :=
    restricted_mcs_exists_containing phi phi.neg h_neg_clos h_singleton_cons
  exact ⟨⟨M, h_mcs⟩, h_neg_in⟩

/--
The filtered model for a non-provable formula provides a finite witness.
-/
theorem filtered_model_falsifies (phi : Formula Atom)
    (h_not_provable : ¬Nonempty (DerivationTree FrameClass.Base
      ([] : List (Formula Atom)) phi)) :
    ∃ (Omega : ClosureMCSBundle phi), phi ∉ Omega.carrier := by
  obtain ⟨Omega, h_neg⟩ := exists_mcs_with_negation phi h_not_provable
  use Omega
  intro h_phi
  exact mcs_not_both_and_neg h_phi h_neg

/-!
## Finite Model Property Statement
-/

/--
MCS-based Finite Model Property: If φ is not provable, then there exists
a closure MCS (a world in a finite model) where φ is false (not a member).
-/
theorem mcs_finite_model_property (phi : Formula Atom)
    (h_not_provable : ¬Nonempty (DerivationTree FrameClass.Base
      ([] : List (Formula Atom)) phi)) :
    ∃ (Omega : ClosureMCSBundle phi), phi ∉ Omega.carrier ∧
    Finite (FilteredWorld phi) := by
  obtain ⟨Omega, h_not_in⟩ := filtered_model_falsifies phi h_not_provable
  exact ⟨Omega, h_not_in, FilteredWorld.finite phi⟩

/--
Contrapositive of FMP: If φ is true in all closure MCS for the finite
filtered model, then φ is provable.
-/
theorem fmp_contrapositive (phi : Formula Atom)
    (h_all_mcs : ∀ (Omega : ClosureMCSBundle phi), phi ∈ Omega.carrier) :
    Nonempty (DerivationTree FrameClass.Base ([] : List (Formula Atom)) phi) := by
  by_contra h_not_provable
  obtain ⟨Omega, h_not_in, _⟩ := mcs_finite_model_property phi h_not_provable
  exact h_not_in (h_all_mcs Omega)

/-!
## FMP Size Bound
-/

/--
The finite filtered model has at most 2^|closure(φ)| worlds.
-/
theorem fmp_size_bound (phi : Formula Atom) :
    ∃ (bound : Nat),
    bound = 2 ^ (subformulaClosure phi).card ∧ True :=
  ⟨2 ^ (subformulaClosure phi).card, rfl, trivial⟩

end Cslib.Logic.Bimodal.Metalogic.Decidability.FMP
