/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.DenseSoundness
public import Cslib.Logics.Temporal.Metalogic.Completeness

/-! # Dense Completeness for Temporal Logic

This module proves completeness of the Dense temporal proof system: every formula
valid on all dense serial linear orders is derivable in the Dense BX system.

## Strategy

The proof proceeds by contrapositive, building on the existing Base chronicle
construction. The key insight is that the Dense-MCS starting point A ensures
`¬U(⊤, ⊥)` propagates to ALL limit points via C4/C4' arguments, giving
`DenselyOrdered` for the chronicle subtype WITHOUT FC-parameterization.

### Propagation of ¬U(⊤, ⊥)

1. `limitF(0) = A` is Dense-MCS, so `¬U(⊤, ⊥) ∈ A`.
2. For `x > 0`: `G(¬U(⊤, ⊥)) ∈ A = limitF(0)`, equivalently
   `¬U(U(⊤, ⊥), ⊤) ∈ limitF(0)`. If `U(⊤, ⊥) ∈ limitF(x)`, C4 at (0, x)
   gives `z` with `0 < z < x` and `⊥ ∈ limitF(z)`, contradicting Base-MCS.
3. For `x < 0`: `H(¬U(⊤, ⊥)) ∈ A`, equivalently `¬S(U(⊤, ⊥), ⊤) ∈ limitF(0)`.
   If `U(⊤, ⊥) ∈ limitF(x)`, C4' at (0, x) gives `z` with `x < z < 0` and
   `⊥ ∈ limitF(z)`, contradicting Base-MCS.

## Main Results

- `dense_indicator_in_all_limit_points`: `¬U(⊤, ⊥) ∈ limitF(x)` for all x.
- `chronicle_densely_ordered_dense`: DenselyOrdered for ChronicleSubtype from Dense-MCS.
- `completeness_dense`: ValidDense φ → ThDerivableFc .Dense φ.

## References

- Burgess (1982): BX axiom system
- Xu (1988): Temporal completeness proofs
-/

set_option linter.style.setOption false
set_option linter.dupNamespace false
set_option maxHeartbeats 3200000

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic
open Cslib.Logic.Temporal.Metalogic.Chronicle

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Dense Axiom Membership in Dense-MCS -/

/-- The dense indicator ¬U(⊤, ⊥) belongs to every Dense-MCS. -/
theorem dense_indicator_in_dense_mcs
    {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A) :
    (Formula.untl Formula.top Formula.bot).neg ∈ A :=
  theoremInMcsFc h_mcs
    (.axiom [] _ .dense_indicator (le_refl _))

/-- G(¬U(⊤, ⊥)) belongs to every Dense-MCS (by temporal necessitation). -/
theorem g_dense_indicator_in_dense_mcs
    {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A) :
    Formula.allFuture (Formula.untl Formula.top Formula.bot).neg ∈ A :=
  theoremInMcsFc h_mcs
    (.temporal_necessitation _
      (.axiom [] _ .dense_indicator (le_refl _)))

/-- ¬U(U(⊤, ⊥), ⊤) belongs to every Dense-MCS.
This is the syntactic form of G(¬U(⊤, ⊥)). -/
theorem neg_until_until_in_dense_mcs
    {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A) :
    (Formula.untl (Formula.untl Formula.top Formula.bot) Formula.top).neg ∈ A := by
  -- G(phi) = neg(F(neg phi)) = neg(U(neg phi, top))
  -- G(neg U(top, bot)) = neg(U(neg(neg U(top, bot)), top)) = neg(U(U(top, bot), top))
  exact g_dense_indicator_in_dense_mcs h_mcs

/-- H(¬U(⊤, ⊥)) belongs to every Dense-MCS.
Derived via temporal duality: swap(¬U(⊤, ⊥)) = ¬S(⊤, ⊥),
then G(¬S(⊤, ⊥)) by necessitation, then swap gives H(¬U(⊤, ⊥)). -/
theorem h_dense_indicator_in_dense_mcs
    {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A) :
    Formula.allPast (Formula.untl Formula.top Formula.bot).neg ∈ A := by
  -- We need H(neg U(top, bot)).
  -- Step 1: ⊢[Dense] neg U(top, bot) (dense_indicator)
  -- Step 2: ⊢[Dense] swap(neg U(top, bot)) = neg S(top, bot) (temporal_duality)
  -- Step 3: ⊢[Dense] G(neg S(top, bot)) (temporal_necessitation)
  -- Step 4: ⊢[Dense] swap(G(neg S(top, bot))) = H(swap(neg S(top, bot)))
  --       = H(neg U(top, bot)) (temporal_duality, swap involution)
  have d1 : DerivationTree FrameClass.Dense ([] : Context Atom)
      (Formula.untl Formula.top Formula.bot).neg :=
    .axiom [] _ .dense_indicator (le_refl _)
  have d2 := DerivationTree.temporal_duality _ d1
  have d3 := DerivationTree.temporal_necessitation _ d2
  have d4 := DerivationTree.temporal_duality _ d3
  -- d4 : swap(G(swap(neg U(top, bot))))
  -- swap(neg U(top, bot)) = neg S(top, bot)
  -- G(neg S(top, bot)) = neg F(S(top, bot)) = neg U(S(top, bot), top)
  -- swap(neg U(S(top, bot), top)) = neg S(U(top, bot), top) = H(neg U(top, bot))
  -- which is allPast(neg U(top, bot)).
  -- Need to show the type matches.
  have h_eq : ((Formula.untl Formula.top Formula.bot).neg.swapTemporal.allFuture).swapTemporal
      = Formula.allPast (Formula.untl Formula.top Formula.bot).neg := by
    simp only [Formula.allFuture, Formula.allPast, Formula.someFuture, Formula.somePast,
      Formula.neg, Formula.top, Formula.swapTemporal, Formula.swapTemporal_involution]
  exact theoremInMcsFc h_mcs (h_eq ▸ d4)

/-- ¬S(U(⊤, ⊥), ⊤) belongs to every Dense-MCS.
This is the syntactic form of H(¬U(⊤, ⊥)). -/
theorem neg_since_until_in_dense_mcs
    {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A) :
    (Formula.snce (Formula.untl Formula.top Formula.bot) Formula.top).neg ∈ A := by
  exact h_dense_indicator_in_dense_mcs h_mcs

/-! ## Propagation of ¬U(⊤, ⊥) to All Limit Points -/

variable [Denumerable (Formula Atom)]

/-- ¬U(⊤, ⊥) belongs to limitF(x) for all x in the limit domain.

For x = 0: limitF(0) = A which is Dense-MCS.
For x > 0: G(¬U(⊤, ⊥)) ∈ limitF(0) gives ¬U(U(⊤,⊥), ⊤) ∈ limitF(0).
  If U(⊤,⊥) ∈ limitF(x), C4 at (0,x) gives z with ⊥ ∈ limitF(z), contradiction.
For x < 0: H(¬U(⊤, ⊥)) ∈ limitF(0) gives ¬S(U(⊤,⊥), ⊤) ∈ limitF(0).
  If U(⊤,⊥) ∈ limitF(x), C4' at (0,x) gives z with ⊥ ∈ limitF(z), contradiction.
-/
theorem dense_indicator_in_all_limit_points
    {A : Set (Formula Atom)}
    (h_dense_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A)
    (h_base_mcs : Temporal.SetMaximalConsistent A)
    (x : Rat) (hx : x ∈ limitDom A h_base_mcs) :
    (Formula.untl Formula.top Formula.bot).neg ∈ limitF A h_base_mcs x := by
  -- Get the Base-MCS at x
  have h_mcs_x := limit_c0 A h_base_mcs x hx
  -- Case split on x
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- Case x < 0: Use C4' from 0 to show U(top, bot) ∉ limitF(x)
    by_contra h_not_neg
    -- If neg U(top, bot) ∉ limitF(x), then U(top, bot) ∈ limitF(x) by negation completeness
    have h_until : Formula.untl Formula.top Formula.bot ∈ limitF A h_base_mcs x :=
      (mcs_mem_iff_neg_not_mem h_mcs_x).mpr h_not_neg
    -- H(neg U(top, bot)) ∈ A = limitF(0), equivalently neg S(U(top, bot), top) ∈ limitF(0)
    have h0 := zero_mem_limit_dom A h_base_mcs
    have h_f_zero : limitF A h_base_mcs 0 = A := limit_f_zero A h_base_mcs
    have h_neg_since : (Formula.snce (Formula.untl Formula.top Formula.bot) Formula.top).neg
        ∈ limitF A h_base_mcs 0 := by
      rw [h_f_zero]; exact neg_since_until_in_dense_mcs h_dense_mcs
    -- Apply C4' at (0, x) with hyx : x < 0
    -- C4' takes (x y : Rat) with hx, hy ∈ limitDom, hyx : y < x
    -- neg S(eta, xi) ∈ limitF(x) and eta ∈ limitF(y) => exists z between
    -- Here: x_c4 = 0, y_c4 = x, so y_c4 < x_c4 = 0 (i.e., x < 0)
    -- neg S(U(top, bot), top) ∈ limitF(0) and U(top, bot) ∈ limitF(x)
    obtain ⟨z, hz_dom, hxz, hz0, h_neg_top_z⟩ :=
      limit_satisfies_c4' A h_base_mcs 0 x h0 hx hx_neg
        Formula.top (Formula.untl Formula.top Formula.bot)
        h_neg_since h_until
    -- h_neg_top_z : (neg top) ∈ limitF(z), i.e., (top → bot) ∈ limitF(z)
    -- With top ∈ limitF(z) (all MCS contain top), modus ponens gives bot ∈ limitF(z)
    have h_mcs_z := limit_c0 A h_base_mcs z hz_dom
    have h_top_z : Formula.top ∈ limitF A h_base_mcs z := by
      apply temporal_closed_under_derivation h_mcs_z (L := []) (fun _ h => nomatch h)
      unfold temporalDerivationSystem Temporal.Deriv
      exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
    exact mcs_bot_not_mem h_mcs_z
      (temporal_implication_property h_mcs_z h_neg_top_z h_top_z)
  · -- Case x = 0: limitF(0) = A is Dense-MCS
    subst hx_zero
    rw [limit_f_zero]
    exact dense_indicator_in_dense_mcs h_dense_mcs
  · -- Case x > 0: Use C4 from 0 to show U(top, bot) ∉ limitF(x)
    by_contra h_not_neg
    have h_until : Formula.untl Formula.top Formula.bot ∈ limitF A h_base_mcs x :=
      (mcs_mem_iff_neg_not_mem h_mcs_x).mpr h_not_neg
    -- G(neg U(top, bot)) ∈ A = limitF(0), equivalently neg U(U(top, bot), top) ∈ limitF(0)
    have h0 := zero_mem_limit_dom A h_base_mcs
    have h_f_zero : limitF A h_base_mcs 0 = A := limit_f_zero A h_base_mcs
    have h_neg_until : (Formula.untl (Formula.untl Formula.top Formula.bot) Formula.top).neg
        ∈ limitF A h_base_mcs 0 := by
      rw [h_f_zero]; exact neg_until_until_in_dense_mcs h_dense_mcs
    obtain ⟨z, hz_dom, h0z, hzx, h_neg_top_z⟩ :=
      limit_satisfies_c4 A h_base_mcs 0 x h0 hx hx_pos
        Formula.top (Formula.untl Formula.top Formula.bot)
        h_neg_until h_until
    -- h_neg_top_z : (neg top) ∈ limitF(z)
    have h_mcs_z := limit_c0 A h_base_mcs z hz_dom
    have h_top_z : Formula.top ∈ limitF A h_base_mcs z := by
      apply temporal_closed_under_derivation h_mcs_z (L := []) (fun _ h => nomatch h)
      unfold temporalDerivationSystem Temporal.Deriv
      exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
    exact mcs_bot_not_mem h_mcs_z
      (temporal_implication_property h_mcs_z h_neg_top_z h_top_z)

/-! ## DenselyOrdered Instance for Chronicle from Dense-MCS -/

/-- The chronicle subtype built from a Dense-MCS is DenselyOrdered.

For any x < y in the chronicle subtype, `¬U(⊤, ⊥) ∈ limitF(x)` and
`⊤ ∈ limitF(y)`. By limit_satisfies_c4, there exists z with x < z < y
and `⊥.neg = ⊤ ∈ limitF(z)`, providing the intermediate point. -/
def chronicle_densely_ordered_dense
    {A : Set (Formula Atom)}
    (h_dense_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A)
    (h_base_mcs : Temporal.SetMaximalConsistent A) :
    DenselyOrdered (ChronicleSubtype A h_base_mcs) where
  dense := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    -- hxy : x < y (as elements of the subtype)
    have hxy_val : x < y := hxy
    -- neg U(top, bot) ∈ limitF(x)
    have h_neg_until := dense_indicator_in_all_limit_points h_dense_mcs h_base_mcs x hx
    -- top ∈ limitF(y)
    have h_mcs_y := limit_c0 A h_base_mcs y hy
    have h_top_y : Formula.top ∈ limitF A h_base_mcs y := by
      apply temporal_closed_under_derivation h_mcs_y (L := []) (fun _ h => nomatch h)
      unfold temporalDerivationSystem Temporal.Deriv
      exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
    -- Apply C4: neg U(top, bot) ∈ limitF(x), top ∈ limitF(y), x < y
    -- => exists z with x < z < y and bot.neg = top ∈ limitF(z)
    obtain ⟨z, hz_dom, hxz, hzy, _⟩ :=
      limit_satisfies_c4 A h_base_mcs x y hx hy hxy_val
        Formula.bot Formula.top h_neg_until h_top_y
    exact ⟨⟨z, hz_dom⟩, hxz, hzy⟩

/-! ## Dense Completeness Theorem -/

omit [Denumerable (Formula Atom)] in
/-- If φ is not Dense-derivable, then {¬φ} is Dense-consistent. -/
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

If `φ` is valid over all dense serial linear temporal orders (linear orders with
`NoMaxOrder`, `NoMinOrder`, and `DenselyOrdered`), then `φ` is Dense-derivable.

The proof proceeds by contrapositive:
1. If φ is not Dense-derivable, then {¬φ} is Dense-consistent.
2. Extend to Dense-MCS M via temporal_lindenbaum_fc.
3. M is also Base-MCS by dense_mcs_implies_base_mcs.
4. Build chronicle from Base-MCS M using existing construction.
5. Chronicle subtype has LinearOrder, Nontrivial, NoMaxOrder, NoMinOrder.
6. Chronicle subtype has DenselyOrdered via ¬U(⊤,⊥) propagation + C4.
7. Apply ValidDense to get φ ∈ limitF(0) = M, contradicting ¬φ ∈ M. -/
omit [Denumerable (Formula Atom)] in
theorem completeness_dense [Denumerable (Formula Atom)] {φ : Formula Atom}
    (h_valid : ValidDense φ) :
    Temporal.ThDerivableFc FrameClass.Dense φ := by
  by_contra h_not_deriv
  have h_cons := neg_consistent_of_not_derivable_dense h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum_fc h_cons
  have h_neg_in_M : Formula.neg φ ∈ M := hM_sup (Set.mem_singleton _)
  have h_phi_not_M : φ ∉ M := mcs_not_mem_of_neg_fc hM_mcs h_neg_in_M
  -- M is Dense-MCS, hence also Base-MCS
  have h_base_mcs := dense_mcs_implies_base_mcs hM_mcs
  -- Build the chronicle countermodel from the Base-MCS M.
  let D := ChronicleSubtype M h_base_mcs
  let model := chronicleModel M h_base_mcs
  let t₀ : D := chronicleZero M h_base_mcs
  -- D has DenselyOrdered from Dense-MCS + C4 propagation
  have : DenselyOrdered D := chronicle_densely_ordered_dense hM_mcs h_base_mcs
  -- Apply validity: φ is true at t₀ in the chronicle model.
  have h_sat := h_valid D model t₀
  -- By the truth lemma: Satisfies model t₀ φ ↔ φ ∈ limitF M h_base_mcs t₀.val
  have h_mem := (chronicle_truth_lemma M h_base_mcs t₀ φ).mp h_sat
  -- t₀.val = 0 and limitF(0) = M, so φ ∈ M.
  have h_zero : t₀.val = 0 := rfl
  rw [h_zero, limit_f_zero] at h_mem
  -- Contradiction: φ ∈ M but φ ∉ M.
  exact h_phi_not_M h_mem

end Cslib.Logic.Temporal
