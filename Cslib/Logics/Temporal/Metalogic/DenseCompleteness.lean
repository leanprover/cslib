/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.DenseSoundness
public import Cslib.Logics.Temporal.Metalogic.Completeness

/-! # Dense Completeness for Temporal Logic

This module proves completeness of the Dense temporal proof system.

## Strategy

Uses the existing Base chronicle construction with a Dense-MCS starting point.
The key is showing `neg U(top, bot)` belongs to ALL limit points, enabling
DenselyOrdered via C4. For forward points (x > 0), a direct C4 argument at
(0, x) works. For backward points (x < 0), the truth lemma provides the bridge:
`H(neg U(top, bot))` in the starting MCS implies satisfaction at all past points,
which by the truth lemma gives membership.

## Main Results

- `dense_indicator_in_all_limit_points`: neg U(top, bot) in limitF(x) for all x.
- `chronicle_densely_ordered_dense`: DenselyOrdered for chronicle from Dense-MCS.
- `completeness_dense`: ValidDense phi -> ThDerivableFc .Dense phi.
-/

set_option linter.style.setOption false
set_option linter.dupNamespace false
set_option maxHeartbeats 3200000

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic
open Cslib.Logic.Temporal.Metalogic
open Cslib.Logic.Temporal.Metalogic.Chronicle

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Dense Axiom Membership in Dense-MCS -/

/-- neg U(top, bot) belongs to every Dense-MCS. -/
theorem dense_indicator_in_dense_mcs
    {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A) :
    (Formula.untl Formula.top Formula.bot).neg ∈ A :=
  theoremInMcsFc h_mcs (.axiom [] _ .dense_indicator (le_refl _))

/-- G(neg U(top, bot)) belongs to every Dense-MCS (temporal necessitation). -/
theorem g_dense_indicator_in_dense_mcs
    {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A) :
    (Formula.untl Formula.top Formula.bot).neg.allFuture ∈ A :=
  theoremInMcsFc h_mcs
    (.temporal_necessitation _ (.axiom [] _ .dense_indicator (le_refl _)))

/-! ## Propagation of neg U(top, bot) to All Limit Points -/

variable [Denumerable (Formula Atom)]

/-- neg U(top, bot) in limitF(x) for all x in the limit domain.

For x = 0: limitF(0) = A is Dense-MCS containing neg U(top, bot).
For x > 0: G(neg U(top, bot)) in limitF(0). If U(top, bot) in limitF(x),
  derive neg neg U(top, bot) in limitF(x) by DNI. Then C4 at (0, x) with
  neg U(neg neg U(top, bot), top) in limitF(0) and neg neg U(top, bot) in limitF(x)
  gives z with top.neg in limitF(z), contradicting Base-MCS (since top.neg = neg top
  and top in every MCS, giving bot in MCS).
For x < 0: Use the truth lemma. G(neg U(top, bot)) in A = limitF(0)
  implies neg U(top, bot) satisfied at all future times in the chronicle model.
  But for PAST times, we use H(neg U(top, bot)) in A, which is Dense-derivable
  (via temporal duality and necessitation). By the truth lemma:
  H(neg U(top, bot)) satisfied at t0 implies neg U(top, bot) satisfied at all
  t < t0, which by truth lemma gives neg U(top, bot) in limitF(x) for x < 0. -/
theorem dense_indicator_in_all_limit_points
    {A : Set (Formula Atom)}
    (h_dense_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A)
    (h_base_mcs : Temporal.SetMaximalConsistent A)
    (x : Rat) (hx : x ∈ limitDom A h_base_mcs) :
    (Formula.untl Formula.top Formula.bot).neg ∈ limitF A h_base_mcs x := by
  have h_mcs_x := limit_c0 A h_base_mcs x hx
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- Case x < 0: Use truth lemma with H(neg U(top, bot)) in A.
    -- Step 1: H(neg U(top, bot)) is Dense-derivable.
    -- Derivation: dense_indicator -> swap -> G -> swap = H by swap-G-swap = H identity.
    -- But syntactically this gives H(neg U(top,bot)) = neg S(neg neg U(top,bot), top).
    -- By truth lemma at t0: Satisfies model t0 (H(neg U(top, bot))).
    -- Since x < 0 = t0.val, we get Satisfies model (x, hx) (neg U(top, bot)).
    -- By truth lemma: neg U(top, bot) in limitF(x).
    let nub := (Formula.untl (Atom := Atom) Formula.top Formula.bot).neg
    let model := chronicleModel A h_base_mcs
    let t₀ : ChronicleSubtype A h_base_mcs := chronicleZero A h_base_mcs
    -- H(neg U(top, bot)) in A
    -- Build derivation: swap -> G -> swap starting from dense_indicator
    have d_ind : DerivationTree FrameClass.Dense ([] : Context Atom) nub :=
      .axiom [] _ .dense_indicator (le_refl _)
    have d_swap := DerivationTree.temporal_duality _ d_ind  -- swap(nub)
    have d_g := DerivationTree.temporal_necessitation _ d_swap  -- G(swap(nub))
    have d_h := DerivationTree.temporal_duality _ d_g  -- swap(G(swap(nub))) = H(nub)
    -- Put H(nub) in A (as Dense-MCS member)
    have h_h_nub_in_A := theoremInMcsFc h_dense_mcs d_h
    -- The type of d_h is: swap(G(swap(nub))).
    -- By truth lemma at t0: this formula is satisfied at t0 in the chronicle model.
    -- Since limitF(0) = A and h_h_nub_in_A is membership in A = limitF(0):
    have h_zero_mem : nub.swapTemporal.allFuture.swapTemporal ∈ limitF A h_base_mcs 0 := by
      rw [limit_f_zero]; exact h_h_nub_in_A
    have h_sat_h := (chronicle_truth_lemma A h_base_mcs t₀
        nub.swapTemporal.allFuture.swapTemporal).mpr h_zero_mem
    -- Now I need to convert this satisfaction to satisfaction of H(nub).
    -- swap(G(swap(nub))) is satisfied iff H(nub) is satisfied (semantically).
    -- Actually, by swapTemporal_dual, swap(phi) satisfaction = phi in dual model.
    -- Let me instead use the allPast_iff characterization.
    -- H(nub) = neg P(neg nub) = allPast(nub).
    -- Satisfaction of allPast(nub) means: for all s < t0, nub satisfied at s.
    -- But d_h has syntactic type swap(G(swap(nub))), not allPast(nub).
    -- These are propositionally equal formulas. Let me show:
    -- swap(G(swap(nub))) = allPast(nub) = H(nub) as Formula.
    -- allPast(phi) = neg(snce(neg phi, top))
    -- swap(G(swap(phi))):
    --   swap(phi) = swap_phi
    --   G(swap_phi) = neg(untl(neg swap_phi, top))
    --   swap(neg(untl(neg swap_phi, top))) = neg(snce(swap(neg swap_phi), top))
    --     = neg(snce(neg(swap(swap_phi)), top)) = neg(snce(neg phi, top)) [by involution]
    --     = allPast(phi).
    -- So swap(G(swap(phi))) = allPast(phi). But this requires swap involution to fire.
    -- In Lean, swap(swap(phi)) reduces to phi by Formula.swapTemporal_involution.
    have h_eq_form : nub.swapTemporal.allFuture.swapTemporal = nub.allPast := by
      -- Need: swap(G(swap(nub))) = allPast(nub) = neg(snce(neg nub, top))
      -- G(swap(nub)) = neg(untl(neg(swap(nub)), top))
      -- swap(neg(untl(neg(swap(nub)), top))) = neg(snce(swap(neg(swap(nub))), top))
      --   = neg(snce(neg(swap(swap(nub))), top))
      -- Now swap(swap(nub)) = nub by involution.
      -- So = neg(snce(neg nub, top)) = allPast(nub).
      simp only [Formula.allFuture, Formula.allPast, Formula.somePast,
        Formula.neg, Formula.top, Formula.swapTemporal, Formula.swapTemporal_involution]
    -- Rewrite h_sat_h to use allPast
    rw [h_eq_form] at h_zero_mem
    have h_sat_hp := (chronicle_truth_lemma A h_base_mcs t₀ nub.allPast).mpr h_zero_mem
    -- allPast satisfaction: for all s < t0, nub satisfied at s.
    rw [Satisfies.allPast_iff] at h_sat_hp
    -- Apply at the point x: ⟨x, hx⟩ < t₀ = ⟨0, _⟩ since x < 0
    have h_sat_x := h_sat_hp ⟨x, hx⟩ hx_neg
    -- By truth lemma backward: nub in limitF(x).
    exact (chronicle_truth_lemma A h_base_mcs ⟨x, hx⟩ nub).mp h_sat_x
  · -- Case x = 0: limitF(0) = A
    subst hx_zero
    rw [limit_f_zero]
    exact dense_indicator_in_dense_mcs h_dense_mcs
  · -- Case x > 0: C4 argument.
    by_contra h_not_neg
    have h_until := (mcs_mem_iff_neg_not_mem h_mcs_x).mpr h_not_neg
    -- U(top, bot) in limitF(x). Derive neg neg U(top, bot) by DNI.
    let utb := Formula.untl (Atom := Atom) Formula.top Formula.bot
    have h_dblneg_until : utb.neg.neg ∈ limitF A h_base_mcs x := by
      have d_dni := deductionTheorem [] utb utb.neg.neg
        (deductionTheorem [utb] utb.neg Formula.bot
          (.modus_ponens [utb.neg, utb] utb Formula.bot
            (.assumption _ utb.neg (by simp))
            (.assumption _ utb (by simp))))
      exact temporal_implication_property h_mcs_x
        (theoremInMcs h_mcs_x d_dni) h_until
    have h0 := zero_mem_limit_dom A h_base_mcs
    -- G(neg U(top, bot)) = neg U(neg neg U(top, bot), top) in limitF(0)
    have h_g := g_dense_indicator_in_dense_mcs h_dense_mcs
    have h_neg_until_g : utb.neg.allFuture ∈ limitF A h_base_mcs 0 := by
      rw [limit_f_zero]; exact h_g
    -- C4 at (0, x) with eta = neg neg utb, xi = top
    obtain ⟨z, hz_dom, _, _, h_neg_top_z⟩ :=
      limit_satisfies_c4 A h_base_mcs 0 x h0 hx hx_pos
        Formula.top utb.neg.neg h_neg_until_g h_dblneg_until
    have h_mcs_z := limit_c0 A h_base_mcs z hz_dom
    have h_top_z : Formula.top ∈ limitF A h_base_mcs z := by
      apply temporal_closed_under_derivation h_mcs_z (L := []) (fun _ h => nomatch h)
      unfold temporalDerivationSystem Temporal.Deriv
      exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
    exact mcs_bot_not_mem h_mcs_z
      (temporal_implication_property h_mcs_z h_neg_top_z h_top_z)

/-! ## DenselyOrdered Instance for Chronicle from Dense-MCS -/

/-- The chronicle subtype built from a Dense-MCS is DenselyOrdered.

For any x < y, neg U(top, bot) in limitF(x) and top in limitF(y).
By limit_satisfies_c4, there exists z with x < z < y. -/
@[reducible]
def chronicle_densely_ordered_dense
    {A : Set (Formula Atom)}
    (h_dense_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A)
    (h_base_mcs : Temporal.SetMaximalConsistent A) :
    DenselyOrdered (ChronicleSubtype A h_base_mcs) where
  dense := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hxy_val : x < y := hxy
    have h_neg_until := dense_indicator_in_all_limit_points h_dense_mcs h_base_mcs x hx
    have h_mcs_y := limit_c0 A h_base_mcs y hy
    have h_top_y : Formula.top ∈ limitF A h_base_mcs y := by
      apply temporal_closed_under_derivation h_mcs_y (L := []) (fun _ h => nomatch h)
      unfold temporalDerivationSystem Temporal.Deriv
      exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
    obtain ⟨z, hz_dom, hxz, hzy, _⟩ :=
      limit_satisfies_c4 A h_base_mcs x y hx hy hxy_val
        Formula.bot Formula.top h_neg_until h_top_y
    exact ⟨⟨z, hz_dom⟩, hxz, hzy⟩

/-! ## Dense Completeness Theorem -/

/-- If phi is not Dense-derivable, then {neg phi} is Dense-consistent. -/
theorem neg_consistent_of_not_derivable_dense
    {φ : Formula Atom} (h_not : ¬ Temporal.ThDerivableFc FrameClass.Dense φ) :
    Temporal.SetConsistentFc FrameClass.Dense ({Formula.neg φ} : Set (Formula Atom)) := by
  intro L hL
  unfold Metalogic.Consistent
  intro ⟨d⟩
  have d_weak : DerivationTree FrameClass.Dense [Formula.neg φ] Formula.bot :=
    .weakening L [Formula.neg φ] .bot d (fun x hx => by
      have := hL x hx; simp only [Set.mem_singleton_iff] at this
      exact List.mem_cons.mpr (Or.inl this))
  have d_dne := deductionTheoremFc [] (Formula.neg φ) .bot d_weak
  let neg_phi := Formula.neg φ
  have efq : DerivationTree (Atom := Atom) FrameClass.Dense []
      (Formula.bot.imp φ) := .axiom [] _ (.efq φ) (FrameClass.base_le _)
  have ik : DerivationTree (Atom := Atom) FrameClass.Dense []
      ((Formula.bot.imp φ).imp (neg_phi.imp (Formula.bot.imp φ))) :=
    .axiom [] _ (.imp_s (Formula.bot.imp φ) neg_phi) (FrameClass.base_le _)
  have step_k := DerivationTree.modus_ponens [] _ _ ik efq
  have is_ax : DerivationTree (Atom := Atom) FrameClass.Dense []
      ((neg_phi.imp (Formula.bot.imp φ)).imp
       ((neg_phi.imp Formula.bot).imp (neg_phi.imp φ))) :=
    .axiom [] _ (.imp_k neg_phi Formula.bot φ) (FrameClass.base_le _)
  have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
  have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
  have peirce_ax : DerivationTree (Atom := Atom) FrameClass.Dense []
      (((φ.imp Formula.bot).imp φ).imp φ) :=
    .axiom [] _ (.peirce φ Formula.bot) (FrameClass.base_le _)
  exact h_not ⟨DerivationTree.modus_ponens [] _ _ peirce_ax step3⟩

/-- **Dense Completeness Theorem for Temporal Logic**:

If phi is valid over all dense serial linear temporal orders, then phi is
Dense-derivable in the BX+Dense proof system. -/
theorem completeness_dense {φ : Formula Atom}
    (h_valid : ValidDense φ) :
    Temporal.ThDerivableFc FrameClass.Dense φ := by
  by_contra h_not_deriv
  have h_cons := neg_consistent_of_not_derivable_dense h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum_fc h_cons
  have h_neg_in_M : Formula.neg φ ∈ M := hM_sup (Set.mem_singleton _)
  have h_phi_not_M : φ ∉ M := mcs_not_mem_of_neg_fc hM_mcs h_neg_in_M
  have h_base_mcs := dense_mcs_implies_base_mcs hM_mcs
  let D := ChronicleSubtype M h_base_mcs
  let model := chronicleModel M h_base_mcs
  let t₀ : D := chronicleZero M h_base_mcs
  have : DenselyOrdered D := chronicle_densely_ordered_dense hM_mcs h_base_mcs
  have h_sat := h_valid D model t₀
  have h_mem := (chronicle_truth_lemma M h_base_mcs t₀ φ).mp h_sat
  have h_zero : t₀.val = 0 := rfl
  rw [h_zero, limit_f_zero] at h_mem
  exact h_phi_not_M h_mem

end Cslib.Logic.Temporal
