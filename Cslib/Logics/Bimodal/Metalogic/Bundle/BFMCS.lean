/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Bundle.FMCS
public import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Syntax.Formula

/-!
# Bundle of Maximal Consistent Sets (BFMCS)

A BFMCS is a bundle of indexed MCS families (FMCS instances) with modal
coherence conditions. This enables a Henkin-style completeness proof where box
quantifies over bundled histories rather than all histories.

## Key Insight

Completeness is an existential statement: If Gamma is consistent, then
there exists a model where Gamma is satisfiable. The BFMCS construction provides
exactly one such satisfying model.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/BFMCS.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*}

/-!
## BFMCS Structure Definition
-/

variable (Atom : Type*) (D : Type*) [Preorder D]

/--
A Bundle of Maximal Consistent Sets (BFMCS) is a collection of indexed MCS families
with modal coherence conditions that enable a provable truth lemma.
-/
structure BFMCS (fc : FrameClass := FrameClass.Base) where
  /-- The collection of indexed MCS families forming the bundle -/
  families : Set (FMCS Atom D fc)

  /-- The bundle is non-empty -/
  nonempty : families.Nonempty

  /-- Modal forward coherence: Box phi in any family's MCS implies phi in ALL families' MCSes. -/
  modal_forward : ∀ fam ∈ families, ∀ φ t, Formula.box φ ∈ fam.mcs t →
    ∀ fam' ∈ families, φ ∈ fam'.mcs t

  /-- Modal backward coherence: phi in ALL families' MCSes implies Box phi in each family's MCS. -/
  modal_backward : ∀ fam ∈ families, ∀ φ t,
    (∀ fam' ∈ families, φ ∈ fam'.mcs t) → Formula.box φ ∈ fam.mcs t

  /-- The distinguished evaluation family where we start truth evaluation. -/
  eval_family : FMCS Atom D fc

  /-- The evaluation family is in the bundle -/
  eval_family_mem : eval_family ∈ families

variable {Atom : Type*} {D : Type*} [Preorder D]

/-!
## S5 Properties from Modal Coherence
-/

/--
Reflexivity: Box phi in MCS implies phi in MCS (from modal_forward applied to self).
-/
theorem BFMCS.reflexivity (B : BFMCS Atom D) (fam : FMCS Atom D) (hfam : fam ∈ B.families)
    (φ : Formula Atom) (t : D) (h : Formula.box φ ∈ fam.mcs t) : φ ∈ fam.mcs t :=
  B.modal_forward fam hfam φ t h fam hfam

/--
Transitivity: Box (Box phi) implies Box phi.
-/
theorem BFMCS.transitivity (B : BFMCS Atom D) (fam : FMCS Atom D) (hfam : fam ∈ B.families)
    (φ : Formula Atom) (t : D) (h : Formula.box (Formula.box φ) ∈ fam.mcs t) :
    Formula.box φ ∈ fam.mcs t :=
  B.reflexivity fam hfam (Formula.box φ) t h

/-- The MCS at any family and time is consistent (used by BFMCS.diamond_witness) -/
lemma BFMCS.consistent (B : BFMCS Atom D) (fam : FMCS Atom D) (hfam : fam ∈ B.families) (t : D) :
    SetConsistent FrameClass.Base (fam.mcs t) :=
  (fam.is_mcs t).1

/-!
## Diamond (Possibility) Properties
-/

/--
Diamond coherence: neg (Box (neg phi)) in fam.mcs t implies
there exists fam' in families where phi in fam'.mcs t.
-/
theorem BFMCS.diamond_witness (B : BFMCS Atom D) (fam : FMCS Atom D) (hfam : fam ∈ B.families)
    (φ : Formula Atom) (t : D)
    (h_diamond : Formula.neg (Formula.box (Formula.neg φ)) ∈ fam.mcs t) :
    ∃ fam' ∈ B.families, φ ∈ fam'.mcs t := by
  by_contra h_no_witness
  push Not at h_no_witness
  -- So for all fam' in families, phi not in fam'.mcs t
  -- By MCS negation completeness, neg phi in fam'.mcs t for all fam'
  have h_all_neg : ∀ fam' ∈ B.families, Formula.neg φ ∈ fam'.mcs t := by
    intro fam' hfam'
    have h_not_phi := h_no_witness fam' hfam'
    have h_mcs := fam'.is_mcs t
    rcases SetMaximalConsistent.negation_complete h_mcs φ with h_phi | h_neg_phi
    · exact absurd h_phi h_not_phi
    · exact h_neg_phi
  -- By modal_backward, Box neg phi in fam.mcs t
  have h_box_neg : Formula.box (Formula.neg φ) ∈ fam.mcs t :=
    B.modal_backward fam hfam (Formula.neg φ) t h_all_neg
  -- But neg (Box neg phi) is also in fam.mcs t, contradicting consistency
  exact set_consistent_not_both (B.consistent fam hfam t) (Formula.box (Formula.neg φ)) h_box_neg h_diamond

end Cslib.Logic.Bimodal.Metalogic.Bundle
