/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Syntax.Formula
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Theorems.GeneralizedNecessitation
public import Cslib.Logics.Bimodal.Theorems.Combinators

/-!
# Temporal Content Definitions

Shared definitions for g_content, h_content, f_content, p_content, u_content, s_content.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/TemporalContent.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal

variable {Atom : Type*}

def g_content (M : Set (Formula Atom)) : Set (Formula Atom) :=
  {phi | Formula.allFuture phi ∈ M}

def h_content (M : Set (Formula Atom)) : Set (Formula Atom) :=
  {phi | Formula.allPast phi ∈ M}

def f_content (M : Set (Formula Atom)) : Set (Formula Atom) :=
  {phi | Formula.someFuture phi ∈ M}

def p_content (M : Set (Formula Atom)) : Set (Formula Atom) :=
  {phi | Formula.somePast phi ∈ M}

def u_content (M : Set (Formula Atom)) : Set (Formula Atom × Formula Atom) :=
  { p | Formula.untl p.1 p.2 ∈ M }

def s_content (M : Set (Formula Atom)) : Set (Formula Atom × Formula Atom) :=
  { p | Formula.snce p.1 p.2 ∈ M }

/-! ## Membership Lemmas -/

@[simp]
lemma mem_g_content_iff {M : Set (Formula Atom)} {phi : Formula Atom} :
    phi ∈ g_content M ↔ Formula.allFuture phi ∈ M := Iff.rfl

@[simp]
lemma mem_h_content_iff {M : Set (Formula Atom)} {phi : Formula Atom} :
    phi ∈ h_content M ↔ Formula.allPast phi ∈ M := Iff.rfl

@[simp]
lemma mem_f_content_iff {M : Set (Formula Atom)} {phi : Formula Atom} :
    phi ∈ f_content M ↔ Formula.someFuture phi ∈ M := Iff.rfl

@[simp]
lemma mem_p_content_iff {M : Set (Formula Atom)} {phi : Formula Atom} :
    phi ∈ p_content M ↔ Formula.somePast phi ∈ M := Iff.rfl

@[simp]
lemma mem_u_content_iff {M : Set (Formula Atom)} {p : Formula Atom × Formula Atom} :
    p ∈ u_content M ↔ Formula.untl p.1 p.2 ∈ M := Iff.rfl

@[simp]
lemma mem_s_content_iff {M : Set (Formula Atom)} {p : Formula Atom × Formula Atom} :
    p ∈ s_content M ↔ Formula.snce p.1 p.2 ∈ M := Iff.rfl

/-! ## Duality Lemmas -/

open Metalogic.Core in
/--
Duality between f_content and g_content for MCS.
phi in f_content(M) iff neg phi not in g_content(M).
-/
theorem f_content_iff_not_neg_in_g_content {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent FrameClass.Base M) (phi : Formula Atom) :
    phi ∈ f_content M ↔ phi.neg ∉ g_content M := by
  simp only [mem_f_content_iff, mem_g_content_iff]
  have h_af_eq : Formula.allFuture phi.neg = (Formula.someFuture phi.neg.neg).neg := rfl
  constructor
  · intro h_sf_in h_af_in
    rw [h_af_eq] at h_af_in
    have h_dni : DerivationTree FrameClass.Base [] (phi.imp phi.neg.neg) :=
      Theorems.Combinators.dni phi
    have h_G_dni : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).allFuture) :=
      DerivationTree.temporal_necessitation _ h_dni
    have h_bx3 : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).allFuture.imp
        ((Formula.untl phi Formula.top).imp (Formula.untl phi.neg.neg Formula.top))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_until phi phi.neg.neg Formula.top) trivial
    have h_sf_impl : DerivationTree FrameClass.Base [] ((Formula.someFuture phi).imp (Formula.someFuture phi.neg.neg)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dni
    have h_sf_nn_in : Formula.someFuture phi.neg.neg ∈ M :=
      SetMaximalConsistent.implication_property h_mcs
        (theorem_in_mcs_fc h_mcs h_sf_impl) h_sf_in
    exact set_consistent_not_both h_mcs.1 (Formula.someFuture phi.neg.neg) h_sf_nn_in h_af_in
  · intro h_af_not_in
    rw [h_af_eq] at h_af_not_in
    cases SetMaximalConsistent.negation_complete h_mcs (Formula.someFuture phi.neg.neg) with
    | inl h_in =>
      have h_dne : DerivationTree FrameClass.Base [] (phi.neg.neg.imp phi) :=
        Theorems.Propositional.double_negation phi
      have h_G_dne : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allFuture) :=
        DerivationTree.temporal_necessitation _ h_dne
      have h_bx3 : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allFuture.imp
          ((Formula.untl phi.neg.neg Formula.top).imp (Formula.untl phi Formula.top))) :=
        DerivationTree.axiom [] _ (Axiom.right_mono_until phi.neg.neg phi Formula.top) trivial
      have h_sf_impl : DerivationTree FrameClass.Base [] ((Formula.someFuture phi.neg.neg).imp (Formula.someFuture phi)) :=
        DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dne
      exact SetMaximalConsistent.implication_property h_mcs
        (theorem_in_mcs_fc h_mcs h_sf_impl) h_in
    | inr h_neg_in => exact absurd h_neg_in h_af_not_in

open Metalogic.Core in
/--
Duality between p_content and h_content for MCS.
phi in p_content(M) iff neg phi not in h_content(M).
-/
theorem p_content_iff_not_neg_in_h_content {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent FrameClass.Base M) (phi : Formula Atom) :
    phi ∈ p_content M ↔ phi.neg ∉ h_content M := by
  simp only [mem_p_content_iff, mem_h_content_iff]
  have h_ap_eq : Formula.allPast phi.neg = (Formula.somePast phi.neg.neg).neg := rfl
  constructor
  · intro h_sp_in h_ap_in
    rw [h_ap_eq] at h_ap_in
    have h_dni : DerivationTree FrameClass.Base [] (phi.imp phi.neg.neg) :=
      Theorems.Combinators.dni phi
    have h_H_dni : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).allPast) :=
      Theorems.past_necessitation _ h_dni
    have h_bx3p : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).allPast.imp
        ((Formula.snce phi Formula.top).imp (Formula.snce phi.neg.neg Formula.top))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_since phi phi.neg.neg Formula.top) trivial
    have h_sp_impl : DerivationTree FrameClass.Base [] ((Formula.somePast phi).imp (Formula.somePast phi.neg.neg)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3p h_H_dni
    have h_sp_nn_in : Formula.somePast phi.neg.neg ∈ M :=
      SetMaximalConsistent.implication_property h_mcs
        (theorem_in_mcs_fc h_mcs h_sp_impl) h_sp_in
    exact set_consistent_not_both h_mcs.1 (Formula.somePast phi.neg.neg) h_sp_nn_in h_ap_in
  · intro h_ap_not_in
    rw [h_ap_eq] at h_ap_not_in
    cases SetMaximalConsistent.negation_complete h_mcs (Formula.somePast phi.neg.neg) with
    | inl h_in =>
      have h_dne : DerivationTree FrameClass.Base [] (phi.neg.neg.imp phi) :=
        Theorems.Propositional.double_negation phi
      have h_H_dne : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allPast) :=
        Theorems.past_necessitation _ h_dne
      have h_bx3p : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allPast.imp
          ((Formula.snce phi.neg.neg Formula.top).imp (Formula.snce phi Formula.top))) :=
        DerivationTree.axiom [] _ (Axiom.right_mono_since phi.neg.neg phi Formula.top) trivial
      have h_sp_impl : DerivationTree FrameClass.Base [] ((Formula.somePast phi.neg.neg).imp (Formula.somePast phi)) :=
        DerivationTree.modus_ponens [] _ _ h_bx3p h_H_dne
      exact SetMaximalConsistent.implication_property h_mcs
        (theorem_in_mcs_fc h_mcs h_sp_impl) h_in
    | inr h_neg_in => exact absurd h_neg_in h_ap_not_in

end Cslib.Logic.Bimodal.Metalogic.Bundle
