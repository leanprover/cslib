/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleToCountermodelBasic
-- WeakCanonical.IntegerModel.GoodStructuresModelSurgery not yet ported (task 36)

/-!
# Chronicle-to-Countermodel Integration (Gap Elimination and Discrete Pipeline)

This file contains the gap elimination proof (`chronicle_gap_contradiction`)
and the discrete countermodel pipeline (succ-embedding, BFMCS on Z, etc.)
for the BX completeness theorem.

## Port Status

The discrete pipeline and gap elimination depend on `WeakCanonical.IntegerModel.
GoodStructuresModelSurgery` which is not yet ported (task 36). All declarations
from the source are preserved with sorry-stubs where WeakCanonical is needed.

The `mcs_mixed_case_absurd` theorem is fully ported (no sorry) since it depends
only on S5 axioms and K-distribution.

## References

- Burgess 1982: "Axioms for tense logic II: Time periods"
- Reynolds 1994: "Axiomatising first-order temporal logic: Until and Since over linear time"
-/

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}
variable [Denumerable (Formula Atom)]

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical
open Cslib.Logic.Bimodal.Metalogic.BXCanonical.CanonicalModel
open Cslib.Logic.Bimodal.Theorems.Propositional
open Classical

/-! ## Gap Elimination and IsSuccArchimedean

The gap elimination proof (`chronicle_gap_contradiction`) depends on
`GoodStructuresModelSurgery.lean` from WeakCanonical (not yet ported, task 36).
-/

/-- Core gap elimination theorem. Depends on WeakCanonical (task 36). -/
theorem chronicle_gap_contradiction (fc : FrameClass) (A : Set (Formula Atom))
    (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x)
    (a b : LimitDomSubtype fc A h_mcs)
    (h_lt : a < b)
    (h_gap : ∀ k : Nat, (limitDomSubtype_succ fc A h_mcs h_discrete)^[k] a ≠ b) :
    False := by
  sorry  -- depends on gap_contradicts_prior from GoodStructuresModelSurgery (task 36)

/-- Succ-cofinality from gap elimination. -/
theorem succ_cofinal (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x)
    (a b : LimitDomSubtype fc A h_mcs) (h_lt : a < b) :
    ∃ k : Nat, (limitDomSubtype_succ fc A h_mcs h_discrete)^[k] a = b := by
  by_contra h_all
  push_neg at h_all
  exact chronicle_gap_contradiction fc A h_mcs h_discrete a b h_lt (fun k => h_all k)

/-- `IsSuccArchimedean` for `LimitDomSubtype` in the discrete case. -/
noncomputable def limitDomSubtype_isSuccArchimedean (fc : FrameClass)
    (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x) :
    @IsSuccArchimedean _ _ (limitDomSubtype_succOrder fc A h_mcs h_discrete) := by
  letI := limitDomSubtype_succOrder fc A h_mcs h_discrete
  constructor
  intro a b h_le
  rcases lt_or_eq_of_le h_le with h_lt | rfl
  · obtain ⟨k, hk⟩ := succ_cofinal fc A h_mcs h_discrete a b h_lt
    exact ⟨k, hk⟩
  · exact ⟨0, by simp⟩

/-! ## Discrete Pipeline (sorry-stubbed, task 36) -/

/-- Forward embedding into LimitDomSubtype. -/
noncomputable def embed_forward (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x) :
    Nat → LimitDomSubtype fc A h_mcs :=
  fun n => (limitDomSubtype_succ fc A h_mcs h_discrete)^[n] ⟨0, zero_mem_limit_dom fc A h_mcs⟩

/-- Backward embedding into LimitDomSubtype. -/
noncomputable def embed_backward (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x) :
    Nat → LimitDomSubtype fc A h_mcs :=
  fun n => (limitDomSubtype_pred fc A h_mcs h_discrete)^[n] ⟨0, zero_mem_limit_dom fc A h_mcs⟩

/-- Discrete embedding: Int → LimitDomSubtype. -/
noncomputable def discrete_embed (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x) :
    Int → LimitDomSubtype fc A h_mcs :=
  fun z =>
    if 0 ≤ z
    then embed_forward fc A h_mcs h_discrete z.toNat
    else embed_backward fc A h_mcs h_discrete (-z).toNat

/-- Discrete f: MCS assignment via discrete embedding. -/
noncomputable def discrete_f (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x) :
    Int → Set (Formula Atom) :=
  fun z => limit_f fc A h_mcs (discrete_embed fc A h_mcs h_discrete z).val

theorem discrete_f_at_zero (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x) :
    discrete_f fc A h_mcs h_discrete 0 = A := by
  simp only [discrete_f, discrete_embed, embed_forward, Function.iterate_zero, id_eq]
  exact limit_f_zero fc A h_mcs

theorem discrete_f_is_mcs (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x)
    (z : Int) : SetMaximalConsistent fc (discrete_f fc A h_mcs h_discrete z) :=
  limit_c0 fc A h_mcs _ (discrete_embed fc A h_mcs h_discrete z).property

/-- FMCS on Int (discrete case). Sorry-stubbed for forward_G/backward_H (task 36). -/
noncomputable def discrete_fmcs (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x) :
    FMCS Atom Int fc where
  mcs := discrete_f fc A h_mcs h_discrete
  is_mcs := discrete_f_is_mcs fc A h_mcs h_discrete
  forward_G := by sorry  -- TODO: depends on discrete_embed_strictMono (task 36)
  backward_H := by sorry  -- TODO: depends on discrete_embed_strictMono (task 36)

/-- Succ-embedding: LimitDomSubtype → Int. Sorry-stubbed (task 36). -/
noncomputable def succ_embed (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limit_dom fc A h_mcs, next_top ∈ limit_f fc A h_mcs x) :
    LimitDomSubtype fc A h_mcs → Int := by
  sorry

/-- Rooted succ-discrete FMCS. Sorry-stubbed (task 36). -/
noncomputable def rooted_succ_discrete_fmcs (fc : FrameClass) (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
    (h_box_discrete_N : Formula.box next_top ∈ N) (s : Int) : FMCS Atom Int fc := by
  sorry

theorem rooted_succ_discrete_fmcs_at_s (fc : FrameClass) (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
    (h_box_discrete_N : Formula.box next_top ∈ N) (s : Int) :
    (rooted_succ_discrete_fmcs fc N h_N h_box_discrete_N s).mcs s = N := by
  sorry

/-- BFMCS on Int (discrete case). Sorry-stubbed (task 36). -/
noncomputable def cantor_bfmcs_discrete (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_box_discrete : Formula.box next_top ∈ A) :
    BFMCS Atom Int fc where
  families := { fam | ∃ (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
    (h_box_N : Formula.box next_top ∈ N) (s : Int),
    (∀ ψ, Formula.box ψ ∈ A ↔ Formula.box ψ ∈ N) ∧
    fam = rooted_succ_discrete_fmcs fc N h_N h_box_N s }
  nonempty := sorry
  modal_forward := by sorry
  modal_backward := by sorry
  eval_family := sorry
  eval_family_mem := sorry

/-- Discrete countermodel. Sorry-stubbed (task 36). -/
theorem dd_countermodel_chronicle_discrete (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (φ : Formula Atom) (h_neg_in : φ.neg ∈ A)
    (h_box_discrete : Formula.box next_top ∈ A) :
    ∃ (D : Type _) (_ : AddCommGroup D) (_ : LinearOrder D) (_ : IsOrderedAddMonoid D)
      (_ : Nontrivial D) (TF : TaskFrame D) (TM : TaskModel Atom TF)
      (Omega : Set (WorldHistory TF)) (_ : ShiftClosed Omega)
      (τ : WorldHistory TF) (_ : τ ∈ Omega) (t : D),
      ¬truth_at TM Omega τ t φ := by
  sorry  -- TODO: discrete pipeline (task 36)

/-! ## Mixed Case: Impossible by S5

The mixed case (neither □(F'T) nor □(U(T,bot)) in A) is impossible.
This proof is complete (no sorry) since it uses only S5 axioms.
-/

/--
Mixed case is absurd: if ¬□(F'T) ∈ A and ¬□(U(T,bot)) ∈ A, then False.
-/
theorem mcs_mixed_case_absurd (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_not_box_dense : (Formula.box next_top.neg).neg ∈ A)
    (h_not_box_discrete : (Formula.box (next_top (Atom := Atom))).neg ∈ A) : False := by
  have h_axiom_base : DerivationTree FrameClass.Base [] ((next_top (Atom := Atom)).imp (Formula.box next_top)) :=
    DerivationTree.axiom [] _ Axiom.discrete_box_necessity trivial
  have h_contra_base : DerivationTree FrameClass.Base [] ((Formula.box (next_top (Atom := Atom))).neg.imp next_top.neg) :=
    contraposition h_axiom_base
  have h_contra : DerivationTree fc [] ((Formula.box (next_top (Atom := Atom))).neg.imp next_top.neg) :=
    liftBase fc h_contra_base
  have h_nec : DerivationTree fc [] (Formula.box ((Formula.box (next_top (Atom := Atom))).neg.imp next_top.neg)) :=
    DerivationTree.necessitation _ h_contra
  have h_k_dist : DerivationTree fc [] ((Formula.box ((Formula.box (next_top (Atom := Atom))).neg.imp next_top.neg)).imp
      ((Formula.box (Formula.box next_top).neg).imp (Formula.box next_top.neg))) :=
    DerivationTree.axiom [] _ (Axiom.modal_k_dist (Formula.box (next_top (Atom := Atom))).neg next_top.neg) trivial
  have h_box_chain : DerivationTree fc [] ((Formula.box (Formula.box (next_top (Atom := Atom))).neg).imp (Formula.box next_top.neg)) :=
    DerivationTree.modus_ponens [] _ _ h_k_dist h_nec
  have h_box_neg_box : Formula.box (Formula.box (next_top (Atom := Atom))).neg ∈ A :=
    SetMaximalConsistent.neg_box_implies_box_neg_box h_mcs next_top h_not_box_discrete
  have h_box_dense : Formula.box next_top.neg ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc h_mcs h_box_chain) h_box_neg_box
  exact set_consistent_not_both h_mcs.1 (Formula.box next_top.neg) h_box_dense h_not_box_dense

/-- Mixed-case countermodel: vacuously true since the mixed case is impossible. -/
theorem dd_countermodel_chronicle_mixed_sorry (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (φ : Formula Atom) (h_neg_in : φ.neg ∈ A)
    (h_not_box_dense : (Formula.box next_top.neg).neg ∈ A)
    (h_not_box_discrete : (Formula.box (next_top (Atom := Atom))).neg ∈ A) :
    ∃ (D : Type _) (_ : AddCommGroup D) (_ : LinearOrder D) (_ : IsOrderedAddMonoid D)
      (_ : Nontrivial D) (TF : TaskFrame D) (TM : TaskModel Atom TF)
      (Omega : Set (WorldHistory TF)) (_ : ShiftClosed Omega)
      (τ : WorldHistory TF) (_ : τ ∈ Omega) (t : D),
      ¬truth_at TM Omega τ t φ :=
  False.elim (mcs_mixed_case_absurd fc A h_mcs h_not_box_dense h_not_box_discrete)

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle
