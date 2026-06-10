/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem
import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent

/-!
# MCS Properties for Canonical Model Construction

This module provides essential lemmas about Set-based Maximal Consistent Sets (MCS)
needed for the Representation layer's canonical model construction.

The `fc`-parameterized `SetConsistent` and `SetMaximalConsistent` definitions allow
working with arbitrary frame classes (Base, Dense, Discrete), unlike the generic
framework wrappers in `MaximalConsistent.lean` which are specialized to `FrameClass.Base`.

## Main Results

- `cons_filter_neq_perm`: Helper for context permutation with filter
- `derivation_exchange`: Derivability preserved under context permutation
- `SetMaximalConsistent.closed_under_derivation`: Derivable formulas are in MCS
- `SetMaximalConsistent.implication_property`: Modus ponens reflected in membership
- `SetMaximalConsistent.negation_complete`: Either phi or neg phi in MCS
- `temp_4_derived`: Derived temporal 4 axiom for future (G phi -> GG phi)
- `temp_4_past`: Derived temporal 4 axiom for past (H phi -> HH phi)
- `SetMaximalConsistent.allFuture_allFuture`: G phi in Omega implies GG phi in Omega
- `SetMaximalConsistent.allPast_allPast`: H phi in Omega implies HH phi in Omega
- `set_consistent_not_both`: phi and neg phi cannot both be in a consistent set
- `SetMaximalConsistent.neg_excludes`: neg phi in MCS implies phi not in MCS

## Dependencies

Depends on `DeductionTheorem.lean` for the deduction theorem and
`MaximalConsistent.lean` for MCS definitions.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Core/MCSProperties.lean
* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS framework
-/

set_option linter.style.emptyLine false
set_option linter.flexible false

namespace Cslib.Logic.Bimodal.Metalogic.Core

open Cslib.Logic.Bimodal
open Cslib.Logic

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Set-Based Consistency Definitions

These `fc`-parameterized definitions allow working with arbitrary frame classes,
complementing the `BimodalSetConsistent`/`BimodalSetMaximalConsistent` abbreviations
in `MaximalConsistent.lean` which are specialized to `FrameClass.Base`.
-/

/--
Set-based consistency parameterized by frame class.

A set `Omega` is consistent at frame class `fc` if every finite subset is consistent.
-/
def SetConsistent (fc : FrameClass) (Omega : Set (Formula Atom)) : Prop :=
  ∀ L : List (Formula Atom), (∀ phi ∈ L, phi ∈ Omega) → Consistent (fc := fc) L

/--
Set-based maximal consistency parameterized by frame class.

A set `Omega` is maximally consistent at `fc` if it is consistent and cannot be
properly extended while remaining consistent.
-/
def SetMaximalConsistent (fc : FrameClass) (Omega : Set (Formula Atom)) : Prop :=
  SetConsistent fc Omega ∧
  ∀ phi : Formula Atom, phi ∉ Omega → ¬SetConsistent fc (insert phi Omega)

/-! ## Helper Lemmas -/

/--
Helper: If `A in Gamma'`, then `A :: Gamma'.filter (fun x => decide (x != A))` has the
same elements as `Gamma'`.
-/
lemma cons_filter_neq_perm {A : Formula Atom} {Gamma' : Context Atom}
    (h_mem : A ∈ Gamma') :
    ∀ x, x ∈ A :: Gamma'.filter (fun y => decide (y ≠ A)) ↔ x ∈ Gamma' := by
  intro x
  constructor
  · intro h
    simp only [List.mem_cons] at h
    cases h with
    | inl h_eq =>
      subst h_eq
      exact h_mem
    | inr h_in =>
      simp only [List.mem_filter, decide_eq_true_eq] at h_in
      exact h_in.1
  · intro h
    by_cases hx : x = A
    · subst hx
      simp only [List.mem_cons, true_or]
    · simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
      right
      exact ⟨h, hx⟩

/--
Exchange lemma for derivations: If Gamma and Gamma' have the same elements,
derivation is preserved.
-/
def derivation_exchange {fc : FrameClass} {Gamma Gamma' : Context Atom} {phi : Formula Atom}
    (h : DerivationTree fc Gamma phi) (h_perm : ∀ x, x ∈ Gamma ↔ x ∈ Gamma') :
    DerivationTree fc Gamma' phi :=
  DerivationTree.weakening Gamma Gamma' phi h (fun x hx => (h_perm x).mp hx)

/-! ## Set-Based MCS Properties -/

/--
For set-based MCS, derivable formulas are in the set.

If Omega is SetMaximalConsistent and L subs Omega derives phi, then phi in Omega.
-/
lemma SetMaximalConsistent.closed_under_derivation {fc : FrameClass}
    {Omega : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (L : List (Formula Atom)) (h_sub : ∀ psi ∈ L, psi ∈ Omega)
    (h_deriv : DerivationTree fc L phi) : phi ∈ Omega := by
  -- By contradiction: assume phi not in Omega
  by_contra h_not_mem
  -- By SetMaximalConsistent definition, insert phi Omega is inconsistent
  have h_incons : ¬SetConsistent fc (insert phi Omega) := h_mcs.2 phi h_not_mem
  -- SetConsistent means all finite subsets are consistent
  unfold SetConsistent at h_incons
  push Not at h_incons
  obtain ⟨L', h_L'_sub, h_L'_incons⟩ := h_incons
  -- L' subs insert phi Omega and L' is inconsistent
  by_cases h_phi_in_L' : phi ∈ L'
  · -- phi in L'. Use exchange to put phi first, then deduction theorem.
    have ⟨d_bot⟩ : Nonempty (DerivationTree fc L' Formula.bot) := by
      unfold Consistent at h_L'_incons
      push Not at h_L'_incons
      exact h_L'_incons
    -- Exchange to put phi first
    let L'_filt := L'.filter (fun y => decide (y ≠ phi))
    have h_perm := cons_filter_neq_perm h_phi_in_L'
    have d_bot_reord : DerivationTree fc (phi :: L'_filt) Formula.bot :=
      derivation_exchange d_bot (fun x => (h_perm x).symm)
    -- Apply deduction theorem
    have d_neg_phi : DerivationTree fc L'_filt (Formula.neg phi) :=
      deduction_theorem L'_filt phi Formula.bot d_bot_reord
    -- L'_filt subs Omega
    have h_filt_sub : ∀ psi, psi ∈ L'_filt → psi ∈ Omega := by
      intro psi h_mem
      have h_and := List.mem_filter.mp h_mem
      have h_in_L' : psi ∈ L' := h_and.1
      have h_ne : psi ≠ phi := by
        simp only [decide_eq_true_eq] at h_and
        exact h_and.2
      have := h_L'_sub psi h_in_L'
      cases Set.mem_insert_iff.mp this with
      | inl h_eq => exact absurd h_eq h_ne
      | inr h_in_S => exact h_in_S
    -- From L derives phi (weakened) and L'_filt derives neg phi, derive bot
    let Gamma := L ++ L'_filt
    have h_Gamma_sub : ∀ psi ∈ Gamma, psi ∈ Omega := by
      intro psi h_mem
      cases List.mem_append.mp h_mem with
      | inl h_L => exact h_sub psi h_L
      | inr h_filt => exact h_filt_sub psi h_filt
    have d_phi_Gamma : DerivationTree fc Gamma phi :=
      DerivationTree.weakening L Gamma phi h_deriv (List.subset_append_left L _)
    have d_neg_Gamma : DerivationTree fc Gamma (Formula.neg phi) :=
      DerivationTree.weakening L'_filt Gamma (Formula.neg phi) d_neg_phi
        (List.subset_append_right L _)
    have d_bot_Gamma : DerivationTree fc Gamma Formula.bot :=
      derives_bot_from_phi_neg_phi d_phi_Gamma d_neg_Gamma
    -- This contradicts Omega being consistent
    exact h_mcs.1 Gamma h_Gamma_sub ⟨d_bot_Gamma⟩
  · -- phi not in L', so L' subs Omega
    have h_L'_in_Omega : ∀ psi ∈ L', psi ∈ Omega := by
      intro psi h_mem
      have := h_L'_sub psi h_mem
      cases Set.mem_insert_iff.mp this with
      | inl h_eq => exact absurd h_eq (fun h' => h_phi_in_L' (h' ▸ h_mem))
      | inr h_in_S => exact h_in_S
    -- L' subs Omega and L' is inconsistent contradicts Omega consistent
    unfold Consistent at h_L'_incons
    push Not at h_L'_incons
    exact h_mcs.1 L' h_L'_in_Omega h_L'_incons

/--
Set-based MCS implication property: modus ponens is reflected in membership.

If (phi -> psi) in Omega and phi in Omega for a SetMaximalConsistent Omega, then psi in Omega.
-/
theorem SetMaximalConsistent.implication_property {fc : FrameClass}
    {Omega : Set (Formula Atom)} {phi psi : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h_imp : (phi.imp psi) ∈ Omega) (h_phi : phi ∈ Omega) : psi ∈ Omega := by
  have h_sub : ∀ chi ∈ [phi, phi.imp psi], chi ∈ Omega := by
    intro chi h_mem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_mem
    cases h_mem with
    | inl h_eq => exact h_eq ▸ h_phi
    | inr h_eq => exact h_eq ▸ h_imp
  -- Derive psi from [phi, phi -> psi]
  have h_deriv : DerivationTree fc [phi, phi.imp psi] psi := by
    have h_assume_phi : DerivationTree fc [phi, phi.imp psi] phi :=
      DerivationTree.assumption [phi, phi.imp psi] phi (by simp)
    have h_assume_imp : DerivationTree fc [phi, phi.imp psi] (phi.imp psi) :=
      DerivationTree.assumption [phi, phi.imp psi] (phi.imp psi) (by simp)
    exact DerivationTree.modus_ponens [phi, phi.imp psi] phi psi h_assume_imp h_assume_phi
  exact SetMaximalConsistent.closed_under_derivation h_mcs [phi, phi.imp psi] h_sub h_deriv

/--
Set-based MCS: negation completeness.

For SetMaximalConsistent Omega, either phi in Omega or (neg phi) in Omega.
-/
theorem SetMaximalConsistent.negation_complete {fc : FrameClass}
    {Omega : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc Omega) (phi : Formula Atom) :
    phi ∈ Omega ∨ (Formula.neg phi) ∈ Omega := by
  by_cases h : phi ∈ Omega
  · left; exact h
  · right
    -- If phi not in Omega, then insert phi Omega is inconsistent
    have h_incons : ¬SetConsistent fc (insert phi Omega) := h_mcs.2 phi h
    unfold SetConsistent at h_incons
    push Not at h_incons
    obtain ⟨L', h_L'_sub, h_L'_incons⟩ := h_incons
    by_cases h_phi_in_L' : phi ∈ L'
    · -- phi in L'. Use exchange and deduction theorem.
      have ⟨d_bot⟩ : Nonempty (DerivationTree fc L' Formula.bot) := by
        unfold Consistent at h_L'_incons
        push Not at h_L'_incons
        exact h_L'_incons
      -- Exchange to put phi first using filter
      let L'_filt := L'.filter (fun y => decide (y ≠ phi))
      have h_perm := cons_filter_neq_perm h_phi_in_L'
      have d_bot_reord : DerivationTree fc (phi :: L'_filt) Formula.bot :=
        derivation_exchange d_bot (fun x => (h_perm x).symm)
      -- Apply deduction theorem
      have d_neg_phi : DerivationTree fc L'_filt (Formula.neg phi) :=
        deduction_theorem L'_filt phi Formula.bot d_bot_reord
      -- L'_filt subs Omega
      have h_filt_sub : ∀ psi, psi ∈ L'_filt → psi ∈ Omega := by
        intro psi h_mem
        have h_and := List.mem_filter.mp h_mem
        have h_in_L' : psi ∈ L' := h_and.1
        have h_ne : psi ≠ phi := by
          simp only [decide_eq_true_eq] at h_and
          exact h_and.2
        have := h_L'_sub psi h_in_L'
        cases Set.mem_insert_iff.mp this with
        | inl h_eq => exact absurd h_eq h_ne
        | inr h_in_S => exact h_in_S
      exact SetMaximalConsistent.closed_under_derivation h_mcs L'_filt h_filt_sub d_neg_phi
    · -- phi not in L', so L' subs Omega
      have h_L'_in_Omega : ∀ psi ∈ L', psi ∈ Omega := by
        intro psi h_mem
        have := h_L'_sub psi h_mem
        cases Set.mem_insert_iff.mp this with
        | inl h_eq => exact absurd h_eq (fun h' => h_phi_in_L' (h' ▸ h_mem))
        | inr h_in_S => exact h_in_S
      -- L' subs Omega and L' is inconsistent contradicts Omega consistent
      unfold Consistent at h_L'_incons
      push Not at h_L'_incons
      exact absurd h_L'_incons (h_mcs.1 L' h_L'_in_Omega)

/-! ## Temporal Properties -/

noncomputable section

open Cslib.Logic.Bimodal.Theorems.Perpetuity (contraposition imp_trans double_negation unwrap)

/--
Derived temp_4: G phi -> GG phi.

Positive introspection for G, derived from BX3 (right_mono_until), BX6
(absorb_until), double negation elimination, and propositional contraposition.

The contrapositive `F(not not F(not phi)) -> F(not phi)` is proved by composing
three F-monotonicity steps, then negated to obtain `G phi -> GG phi`.
-/
def temp_4_derived (phi : Formula Atom) :
    DerivationTree FrameClass.Base ([] : List (Formula Atom))
      (phi.allFuture.imp phi.allFuture.allFuture) := by
  -- Step 1: F(not not F(not phi)) -> F(F(not phi)) via DNE under F
  have dne_lift_F : DerivationTree FrameClass.Base ([] : List (Formula Atom))
      ((Formula.someFuture (Formula.someFuture phi.neg).neg.neg).imp
       (Formula.someFuture (Formula.someFuture phi.neg))) :=
    DerivationTree.modus_ponens [] _ _
      (DerivationTree.axiom [] _
        (Axiom.right_mono_until
          (Formula.someFuture phi.neg).neg.neg (Formula.someFuture phi.neg) Formula.top) trivial)
      (DerivationTree.temporal_necessitation _ (double_negation (Formula.someFuture phi.neg)))
  -- Step 2: F(F(not phi)) -> F(top and F(not phi)) via top_and_intro under F
  -- top_and_intro: X -> top and X
  -- Derived as: mp (pairing top X) (identity bot) where identity bot : |- top
  have top_and_intro : DerivationTree FrameClass.Base ([] : List (Formula Atom))
      ((Formula.someFuture phi.neg).imp
       (Formula.top.and (Formula.someFuture phi.neg))) := by
    -- We need: X -> top and X where top = bot -> bot and and is conjunction
    -- pairing gives: top -> (X -> top and X) (at typeclass level)
    -- identity gives: |- top (i.e., |- bot -> bot)
    -- mp gives: |- X -> top and X
    let X := Formula.someFuture phi.neg
    -- Derive |- top (bot -> bot) using identity
    have h_top : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (Formula.top (Atom := Atom)) :=
      Cslib.Logic.Bimodal.Theorems.Perpetuity.identity (Atom := Atom) Formula.bot
    -- Derive |- top -> (X -> top and X) using pairing
    have h_pair : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (Formula.top.imp (X.imp (Formula.top.and X))) := by
      exact unwrap
        (@Cslib.Logic.Theorems.Combinators.pairing (Formula Atom) _ _
          Bimodal.HilbertTM _ _ (Formula.top (Atom := Atom)) X)
    -- mp: |- X -> top and X
    exact DerivationTree.modus_ponens [] _ _ h_pair h_top
  have ff_to_f_top_and : DerivationTree FrameClass.Base ([] : List (Formula Atom))
      ((Formula.someFuture (Formula.someFuture phi.neg)).imp
       (Formula.someFuture (Formula.top.and (Formula.someFuture phi.neg)))) :=
    DerivationTree.modus_ponens [] _ _
      (DerivationTree.axiom [] _
        (Axiom.right_mono_until
          (Formula.someFuture phi.neg)
          (Formula.top.and (Formula.someFuture phi.neg)) Formula.top) trivial)
      (DerivationTree.temporal_necessitation _ top_and_intro)
  -- Step 3: F(top and F(not phi)) -> F(not phi) via BX6 (absorption)
  have f_top_and_absorb : DerivationTree FrameClass.Base ([] : List (Formula Atom))
      ((Formula.someFuture (Formula.top.and (Formula.someFuture phi.neg))).imp
       (Formula.someFuture phi.neg)) :=
    DerivationTree.axiom [] _ (Axiom.absorb_until Formula.top phi.neg) trivial
  -- Compose: F(not not F(not phi)) -> F(not phi)
  have composed := imp_trans (imp_trans dne_lift_F ff_to_f_top_and) f_top_and_absorb
  -- Contrapose: G phi -> GG phi
  exact contraposition composed

/--
Derivation of temporal 4 axiom for past: H phi -> HH phi.

Derived by applying temporal duality to the temp_4 axiom (G phi -> GG phi).
-/
def temp_4_past (phi : Formula Atom) :
    DerivationTree FrameClass.Base ([] : List (Formula Atom))
      (phi.allPast.imp phi.allPast.allPast) := by
  -- By temporal duality from: G psi -> GG psi where psi = swapTemporal phi
  let psi := phi.swapTemporal
  -- Step 1: Get T4 derived theorem for psi: G psi -> GG psi
  have h1 : DerivationTree FrameClass.Base ([] : List (Formula Atom))
      (psi.allFuture.imp psi.allFuture.allFuture) :=
    temp_4_derived psi
  -- Step 2: Apply temporal duality
  have h2 : DerivationTree FrameClass.Base ([] : List (Formula Atom))
      ((psi.allFuture.imp psi.allFuture.allFuture).swapTemporal) :=
    DerivationTree.temporal_duality _ h1
  -- Step 3: Simplify via swapTemporal involution
  have h3 : (psi.allFuture.imp psi.allFuture.allFuture).swapTemporal =
      phi.allPast.imp phi.allPast.allPast := by
    simp only [Formula.swapTemporal]
    have h_inv : psi.swapTemporal = phi := Formula.swapTemporal_involution phi
    rw [h_inv]
  rw [h3] at h2
  exact h2

/--
Set-based MCS: temporal 4 axiom property for allFuture.

If G phi in Omega for a SetMaximalConsistent Omega, then GG phi in Omega.
-/
theorem SetMaximalConsistent.allFuture_allFuture {fc : FrameClass}
    {Omega : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h_allFuture : Formula.allFuture phi ∈ Omega) :
    (Formula.allFuture phi).allFuture ∈ Omega := by
  -- Temporal 4 axiom: G phi -> GG phi (derived from BX3 + BX6, at Base, then lifted)
  have h_temp_4_base := temp_4_derived (Atom := Atom) phi
  have h_temp_4_thm : DerivationTree fc ([] : List (Formula Atom))
      ((Formula.allFuture phi).imp (Formula.allFuture (Formula.allFuture phi))) :=
    DerivationTree.lift (FrameClass.base_le fc) h_temp_4_base
  -- Weaken to context [G phi]
  have h_temp_4 : DerivationTree fc [Formula.allFuture phi]
      ((Formula.allFuture phi).imp (Formula.allFuture (Formula.allFuture phi))) :=
    DerivationTree.weakening [] _ _ h_temp_4_thm (List.nil_subset _)
  -- Assume G phi in context
  have h_allFuture_assume : DerivationTree fc [Formula.allFuture phi]
      (Formula.allFuture phi) :=
    DerivationTree.assumption _ _ (by simp)
  -- Apply modus ponens to get GG phi
  have h_deriv : DerivationTree fc [Formula.allFuture phi]
      ((Formula.allFuture phi).allFuture) :=
    DerivationTree.modus_ponens _ _ _ h_temp_4 h_allFuture_assume
  -- By closure: GG phi in Omega
  have h_sub : ∀ chi ∈ [Formula.allFuture phi], chi ∈ Omega := by simp [h_allFuture]
  exact SetMaximalConsistent.closed_under_derivation h_mcs [Formula.allFuture phi] h_sub h_deriv

/--
Set-based MCS: temporal 4 axiom property for allPast.

If H phi in Omega for a SetMaximalConsistent Omega, then HH phi in Omega.
-/
theorem SetMaximalConsistent.allPast_allPast {fc : FrameClass}
    {Omega : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h_allPast : Formula.allPast phi ∈ Omega) :
    (Formula.allPast phi).allPast ∈ Omega := by
  -- Derived temporal 4 for past: H phi -> HH phi (at Base, then lifted)
  have h_temp_4_past_base := temp_4_past (Atom := Atom) phi
  have h_temp_4_past_thm : DerivationTree fc ([] : List (Formula Atom))
      ((Formula.allPast phi).imp (Formula.allPast (Formula.allPast phi))) :=
    DerivationTree.lift (FrameClass.base_le fc) h_temp_4_past_base
  -- Weaken to context [H phi]
  have h_temp_4 : DerivationTree fc [Formula.allPast phi]
      ((Formula.allPast phi).imp (Formula.allPast (Formula.allPast phi))) :=
    DerivationTree.weakening [] _ _ h_temp_4_past_thm (List.nil_subset _)
  -- Assume H phi in context
  have h_allPast_assume : DerivationTree fc [Formula.allPast phi]
      (Formula.allPast phi) :=
    DerivationTree.assumption _ _ (by simp)
  -- Apply modus ponens to get HH phi
  have h_deriv : DerivationTree fc [Formula.allPast phi]
      ((Formula.allPast phi).allPast) :=
    DerivationTree.modus_ponens _ _ _ h_temp_4 h_allPast_assume
  -- By closure: HH phi in Omega
  have h_sub : ∀ chi ∈ [Formula.allPast phi], chi ∈ Omega := by simp [h_allPast]
  exact SetMaximalConsistent.closed_under_derivation h_mcs [Formula.allPast phi] h_sub h_deriv

end -- noncomputable section

/-! ## Consistency Properties -/

/--
In a set-consistent set, phi and phi.neg cannot both be members.
-/
theorem set_consistent_not_both {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h_cons : SetConsistent fc Omega)
    (phi : Formula Atom) (h_phi : phi ∈ Omega) (h_neg : phi.neg ∈ Omega) : False := by
  -- [phi, phi.neg] |- bot
  have h_deriv : DerivationTree fc [phi, phi.neg] Formula.bot := by
    have h_phi_assume : DerivationTree fc [phi, phi.neg] phi :=
      DerivationTree.assumption _ _ (by simp)
    have h_neg_assume : DerivationTree fc [phi, phi.neg] phi.neg :=
      DerivationTree.assumption _ _ (by simp)
    exact DerivationTree.modus_ponens _ phi Formula.bot h_neg_assume h_phi_assume
  -- But [phi, phi.neg] subs Omega, so Omega is inconsistent
  have h_sub : ∀ psi ∈ [phi, phi.neg], psi ∈ Omega := by
    intro psi hpsi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpsi
    cases hpsi with
    | inl h => exact h ▸ h_phi
    | inr h => exact h ▸ h_neg
  exact h_cons [phi, phi.neg] h_sub ⟨h_deriv⟩

/--
If phi.neg is in a set-maximal consistent set M, then phi is not in M.

This is the contrapositive of negation completeness: if neg phi in M, then phi not in M.
Used in the completeness proof to show countermodels exist.
-/
theorem SetMaximalConsistent.neg_excludes {fc : FrameClass}
    {Omega : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc Omega)
    (phi : Formula Atom) (h_neg : phi.neg ∈ Omega) : phi ∉ Omega := by
  intro h_phi
  exact set_consistent_not_both h_mcs.1 phi h_phi h_neg

end Cslib.Logic.Bimodal.Metalogic.Core
