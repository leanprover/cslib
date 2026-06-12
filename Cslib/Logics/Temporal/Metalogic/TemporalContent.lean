/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.MCS

/-!
# Temporal Content Definitions

Shared definitions for gContent, hContent, fContent, pContent, uContent, sContent
for temporal logic. These are the foundational definitions used by all Chronicle files.

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalContent.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic

open Cslib.Logic.Temporal

variable {Atom : Type*}

/-! ## Content Definitions -/

def gContent (M : Set (Formula Atom)) : Set (Formula Atom) :=
  {phi | (𝐆phi) ∈ M}

def hContent (M : Set (Formula Atom)) : Set (Formula Atom) :=
  {phi | (𝐇phi) ∈ M}

def fContent (M : Set (Formula Atom)) : Set (Formula Atom) :=
  {phi | (𝐅phi) ∈ M}

def pContent (M : Set (Formula Atom)) : Set (Formula Atom) :=
  {phi | (𝐏phi) ∈ M}

def uContent (M : Set (Formula Atom)) : Set (Formula Atom × Formula Atom) :=
  { p | Formula.untl p.1 p.2 ∈ M }

def sContent (M : Set (Formula Atom)) : Set (Formula Atom × Formula Atom) :=
  { p | Formula.snce p.1 p.2 ∈ M }

/-! ## Membership Lemmas -/

@[simp]
lemma mem_g_content_iff {M : Set (Formula Atom)} {phi : Formula Atom} :
    phi ∈ gContent M ↔ (𝐆phi) ∈ M := Iff.rfl

@[simp]
lemma mem_h_content_iff {M : Set (Formula Atom)} {phi : Formula Atom} :
    phi ∈ hContent M ↔ (𝐇phi) ∈ M := Iff.rfl

@[simp]
lemma mem_f_content_iff {M : Set (Formula Atom)} {phi : Formula Atom} :
    phi ∈ fContent M ↔ (𝐅phi) ∈ M := Iff.rfl

@[simp]
lemma mem_p_content_iff {M : Set (Formula Atom)} {phi : Formula Atom} :
    phi ∈ pContent M ↔ (𝐏phi) ∈ M := Iff.rfl

@[simp]
lemma mem_u_content_iff {M : Set (Formula Atom)} {p : Formula Atom × Formula Atom} :
    p ∈ uContent M ↔ Formula.untl p.1 p.2 ∈ M := Iff.rfl

@[simp]
lemma mem_s_content_iff {M : Set (Formula Atom)} {p : Formula Atom × Formula Atom} :
    p ∈ sContent M ↔ Formula.snce p.1 p.2 ∈ M := Iff.rfl

/-! ## Duality Lemmas -/

/--
Duality between fContent and gContent for MCS.
phi in fContent(M) iff neg phi not in gContent(M).
-/
theorem f_content_iff_not_neg_in_g_content {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (phi : Formula Atom) :
    phi ∈ fContent M ↔ (¬phi) ∉ gContent M := by
  simp only [mem_f_content_iff, mem_g_content_iff]
  constructor
  · intro h_sf_in h_af_in
    -- F(φ) ∈ M and G(¬φ) ∈ M. G(¬φ) = ¬F(¬¬φ).
    -- Derive F(¬¬φ) from F(φ) via BX3 + DNI, contradicting G(¬φ).
    have h_dni : DerivationTree FrameClass.Base [] (phi.imp phi.neg.neg) := by
      let ctx := [phi]
      have d_dn : DerivationTree FrameClass.Base ctx (phi.neg.neg) := by
        have d_neg_phi_assum : DerivationTree FrameClass.Base [phi.neg, phi] Formula.bot :=
          .modus_ponens [phi.neg, phi] phi Formula.bot
            (.assumption [phi.neg, phi] phi.neg (by simp [List.mem_cons]))
            (.assumption [phi.neg, phi] phi (by simp [List.mem_cons]))
        exact deductionTheorem [phi] phi.neg Formula.bot d_neg_phi_assum
      exact deductionTheorem [] phi phi.neg.neg d_dn
    have h_G_dni : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).allFuture) :=
      DerivationTree.temporal_necessitation _ h_dni
    have h_bx3 : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).allFuture.imp
        ((Formula.untl phi Formula.top).imp (Formula.untl phi.neg.neg Formula.top))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_until phi phi.neg.neg Formula.top) trivial
    have h_sf_impl : DerivationTree FrameClass.Base [] ((Formula.someFuture phi).imp (Formula.someFuture phi.neg.neg)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dni
    have h_sf_nn_in : Formula.someFuture phi.neg.neg ∈ M :=
      temporal_implication_property h_mcs (theoremInMcs h_mcs h_sf_impl) h_sf_in
    -- G(¬φ) = ¬F(¬¬φ). So ¬F(¬¬φ) ∈ M and F(¬¬φ) ∈ M. Contradiction.
    exact mcs_not_mem_of_neg h_mcs h_af_in h_sf_nn_in
  · intro h_af_not_in
    -- ¬φ ∉ gContent(M) means G(¬φ) ∉ M.
    -- G(¬φ) = ¬F(¬¬φ). So ¬F(¬¬φ) ∉ M. By negation completeness, F(¬¬φ) ∈ M.
    -- Then derive F(φ) from F(¬¬φ) via BX3 + DNE.
    have h_F_nn : Formula.someFuture phi.neg.neg ∈ M :=
      (mcs_mem_iff_neg_not_mem h_mcs).mpr h_af_not_in
    have h_dne : DerivationTree FrameClass.Base [] (phi.neg.neg.imp phi) := by
      let ctx := [Formula.neg (Formula.neg phi)]
      have d_peirce : DerivationTree FrameClass.Base ctx (((phi.imp Formula.bot).imp phi).imp phi) :=
        .weakening [] ctx _ (.axiom [] _ (.peirce phi Formula.bot) trivial) (fun _ h => nomatch h)
      let ctx2 := [phi.imp Formula.bot, Formula.neg (Formula.neg phi)]
      have d_bot : DerivationTree FrameClass.Base ctx2 Formula.bot :=
        .modus_ponens ctx2 (phi.imp Formula.bot) Formula.bot
          (.assumption ctx2 (Formula.neg (Formula.neg phi)) (by simp [List.mem_cons, ctx2]))
          (.assumption ctx2 (phi.imp Formula.bot) (by simp [List.mem_cons, ctx2]))
      have d_efq : DerivationTree FrameClass.Base ctx2 phi :=
        .modus_ponens ctx2 Formula.bot phi
          (.weakening [] ctx2 _ (.axiom [] _ (.efq phi) trivial) (fun _ h => nomatch h))
          d_bot
      have d_imp := deductionTheorem [Formula.neg (Formula.neg phi)] (phi.imp Formula.bot) phi d_efq
      exact deductionTheorem [] (Formula.neg (Formula.neg phi)) phi
        (DerivationTree.modus_ponens ctx _ _ d_peirce d_imp)
    have h_G_dne : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allFuture) :=
      DerivationTree.temporal_necessitation _ h_dne
    have h_bx3 : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allFuture.imp
        ((Formula.untl phi.neg.neg Formula.top).imp (Formula.untl phi Formula.top))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_until phi.neg.neg phi Formula.top) trivial
    have h_sf_impl : DerivationTree FrameClass.Base [] ((Formula.someFuture phi.neg.neg).imp (Formula.someFuture phi)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dne
    exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_sf_impl) h_F_nn

/--
Duality between pContent and hContent for MCS.
phi in pContent(M) iff neg phi not in hContent(M).
-/
theorem p_content_iff_not_neg_in_h_content {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (phi : Formula Atom) :
    phi ∈ pContent M ↔ (¬phi) ∉ hContent M := by
  simp only [mem_p_content_iff, mem_h_content_iff]
  constructor
  · intro h_sp_in h_ap_in
    -- P(φ) ∈ M and H(¬φ) ∈ M. Derive contradiction via BX3' + DNI.
    have h_dni : DerivationTree FrameClass.Base [] (phi.imp phi.neg.neg) := by
      let ctx := [phi]
      have d_dn : DerivationTree FrameClass.Base ctx (phi.neg.neg) := by
        have d_neg_phi_assum : DerivationTree FrameClass.Base [phi.neg, phi] Formula.bot :=
          .modus_ponens [phi.neg, phi] phi Formula.bot
            (.assumption [phi.neg, phi] phi.neg (by simp [List.mem_cons]))
            (.assumption [phi.neg, phi] phi (by simp [List.mem_cons]))
        exact deductionTheorem [phi] phi.neg Formula.bot d_neg_phi_assum
      exact deductionTheorem [] phi phi.neg.neg d_dn
    -- H-necessitation of DNI via duality
    have h_H_dni : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).allPast) := by
      have d_swap := DerivationTree.temporal_duality _ h_dni
      have d_g_swap := DerivationTree.temporal_necessitation _ d_swap
      have d_h := DerivationTree.temporal_duality _ d_g_swap
      have h_eq : (Formula.allFuture (phi.imp phi.neg.neg).swapTemporal).swapTemporal =
          Formula.allPast ((phi.imp phi.neg.neg).swapTemporal.swapTemporal) := by
        simp only [Formula.allPast, Formula.somePast, Formula.neg,
          Formula.top, Formula.swapTemporal]
      rw [Formula.swapTemporal_involution] at h_eq
      exact h_eq ▸ d_h
    have h_bx3p : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).allPast.imp
        ((Formula.snce phi Formula.top).imp (Formula.snce phi.neg.neg Formula.top))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_since phi phi.neg.neg Formula.top) trivial
    have h_sp_impl : DerivationTree FrameClass.Base [] ((Formula.somePast phi).imp (Formula.somePast phi.neg.neg)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3p h_H_dni
    have h_sp_nn_in : Formula.somePast phi.neg.neg ∈ M :=
      temporal_implication_property h_mcs (theoremInMcs h_mcs h_sp_impl) h_sp_in
    exact mcs_not_mem_of_neg h_mcs h_ap_in h_sp_nn_in
  · intro h_ap_not_in
    have h_P_nn : Formula.somePast phi.neg.neg ∈ M :=
      (mcs_mem_iff_neg_not_mem h_mcs).mpr h_ap_not_in
    have h_dne : DerivationTree FrameClass.Base [] (phi.neg.neg.imp phi) := by
      let ctx := [Formula.neg (Formula.neg phi)]
      have d_peirce : DerivationTree FrameClass.Base ctx (((phi.imp Formula.bot).imp phi).imp phi) :=
        .weakening [] ctx _ (.axiom [] _ (.peirce phi Formula.bot) trivial) (fun _ h => nomatch h)
      let ctx2 := [phi.imp Formula.bot, Formula.neg (Formula.neg phi)]
      have d_bot : DerivationTree FrameClass.Base ctx2 Formula.bot :=
        .modus_ponens ctx2 (phi.imp Formula.bot) Formula.bot
          (.assumption ctx2 (Formula.neg (Formula.neg phi)) (by simp [List.mem_cons, ctx2]))
          (.assumption ctx2 (phi.imp Formula.bot) (by simp [List.mem_cons, ctx2]))
      have d_efq : DerivationTree FrameClass.Base ctx2 phi :=
        .modus_ponens ctx2 Formula.bot phi
          (.weakening [] ctx2 _ (.axiom [] _ (.efq phi) trivial) (fun _ h => nomatch h))
          d_bot
      have d_imp := deductionTheorem [Formula.neg (Formula.neg phi)] (phi.imp Formula.bot) phi d_efq
      exact deductionTheorem [] (Formula.neg (Formula.neg phi)) phi
        (DerivationTree.modus_ponens ctx _ _ d_peirce d_imp)
    -- H-necessitation of DNE via duality
    have h_H_dne : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allPast) := by
      have d_swap := DerivationTree.temporal_duality _ h_dne
      have d_g_swap := DerivationTree.temporal_necessitation _ d_swap
      have d_h := DerivationTree.temporal_duality _ d_g_swap
      have h_eq : (Formula.allFuture (phi.neg.neg.imp phi).swapTemporal).swapTemporal =
          Formula.allPast ((phi.neg.neg.imp phi).swapTemporal.swapTemporal) := by
        simp only [Formula.allPast, Formula.somePast, Formula.neg,
          Formula.top, Formula.swapTemporal]
      rw [Formula.swapTemporal_involution] at h_eq
      exact h_eq ▸ d_h
    have h_bx3p : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allPast.imp
        ((Formula.snce phi.neg.neg Formula.top).imp (Formula.snce phi Formula.top))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_since phi.neg.neg phi Formula.top) trivial
    have h_sp_impl : DerivationTree FrameClass.Base [] ((Formula.somePast phi.neg.neg).imp (Formula.somePast phi)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3p h_H_dne
    exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_sp_impl) h_P_nn

end Cslib.Logic.Temporal.Metalogic
