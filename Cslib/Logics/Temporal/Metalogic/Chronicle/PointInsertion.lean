/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Temporal.Metalogic.Chronicle.Frame
import Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation

/-!
# Point Insertion Lemmas (Burgess 2.4-2.8)

Implements the core point insertion machinery for the Burgess chronicle
construction, adapted for temporal logic (no FrameClass parameter, no liftBase).

## Key Results

- `F_neg_of_G_not` / `P_neg_of_H_not`: If G(φ)/H(φ) not in MCS, then F(¬φ)/P(¬φ) is.
- `lemma_2_4`: Until witness endpoint construction
- `lemma_2_5b` / `lemma_2_5b_past`: g/h-content ordering transitivity
- `lemma_2_6`: Counterexample insertion
- `dc_delta_B_burgessR3`: Extension of B by delta preserves burgessR3
- `BurgessR3Maximal_extension_fails`: Maximality prevents consistent proper extensions
- `g_content_sub`: BurgessR3Maximal implies g_content(A) ⊆ B

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean
* Burgess 1982: "Axioms for tense logic II: Time periods"
-/

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.flexible false
set_option maxHeartbeats 3200000

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

/-! ## Private Helper: theorem_in_mcs -/

private noncomputable def theorem_in_mcs {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (h_deriv : DerivationTree FrameClass.Base [] phi) : phi ∈ M :=
  temporal_closed_under_derivation h_mcs (L := []) (fun _ h => by simp at h) ⟨h_deriv⟩

/-! ## Helper: F(neg phi) from G(phi) not in A -/

/-- If G(φ) ∉ MCS A, then F(¬φ) ∈ A. -/
theorem F_neg_of_G_not {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ : Formula Atom)
    (h_Gφ_not : Formula.all_future φ ∉ A) :
    Formula.some_future φ.neg ∈ A := by
  rcases temporal_negation_complete h_mcs (Formula.some_future φ.neg) with h | h
  · exact h
  · -- ¬F(¬φ) ∈ A: derive G(¬¬φ) ∈ A
    -- ¬F(¬φ) = G(¬¬φ) via duality
    -- F(X) = X U ⊤ = ¬G(¬X) ... we need F(¬φ) = ¬G(¬¬φ)
    -- ¬F(¬φ) ∈ A means G(¬¬φ) ∈ A (by double negation of the duality)
    -- Then G(¬¬φ) → G(φ) via DNE under G, giving G(φ) ∈ A, contradiction.
    -- Step: ¬F(¬φ) → G(¬¬φ) via DNE on the F-side
    -- Actually: some_future (φ.neg) = ¬(all_future (φ.neg.neg))
    -- = ¬(all_future (¬¬φ))
    -- So ¬(some_future (φ.neg)) = all_future(¬¬φ).neg.neg
    -- But we need all_future(¬¬φ) from ¬F(¬φ).
    -- Let's use: some_future X = ¬G(¬X). So some_future φ.neg = ¬G(¬(φ.neg)) = ¬G(φ.neg.neg).
    -- ¬(some_future φ.neg) = ¬¬G(φ.neg.neg)
    -- So (some_future φ.neg).neg ∈ A means ¬¬G(φ.neg.neg) ∈ A.
    -- We can derive from this that G(φ.neg.neg) ∈ A.
    -- Actually, let's just use the MCS properties directly.
    -- h says ¬(F(¬φ)) ∈ A.
    -- some_future X = neg (all_future (neg X)) doesn't hold definitionally.
    -- Instead: some_future X = untl X top. G(Y) = neg(untl (neg Y) top).
    -- We proved neg_some_future_to_all_future_neg in WitnessSeed.lean.
    -- But that gives: ¬(some_future X) → all_future (neg X). With X = φ.neg:
    -- ¬F(¬φ) → G(¬¬φ).
    -- Let's check if this helper exists.
    -- Use neg_some_future_to_all_future_neg pattern: it converts ¬F(X) to G(¬X)
    -- We don't have exactly that function but we can replicate the logic.
    -- Actually let's just use the available pattern.

    -- We have ¬F(φ.neg) ∈ A (i.e., h : (some_future φ.neg).neg ∈ A)
    -- We want G(φ) ∈ A.
    -- Step 1: From ¬F(¬φ), derive G(¬¬φ). This requires:
    --   ⊢ ¬F(¬φ) → G(¬¬φ). But this isn't direct due to definitional mismatch.
    -- Alternative: use BX3 contrapositive path.
    -- G(¬¬φ → φ) → F(¬¬φ) → F(φ). Contrapositive: G(¬¬φ → φ) → ¬F(φ) → ¬F(¬¬φ).
    -- i.e., G(¬¬φ → φ) → G(φ) → G(¬¬φ). Wrong direction again.
    -- Let's try: from ⊢ φ → ¬¬φ (DNI), get G(φ → ¬¬φ) by TN.
    -- BX3: G(φ → ¬¬φ) → F(φ) → F(¬¬φ). Contrapositive: ¬F(¬¬φ) → ¬F(φ).
    -- But we want the opposite direction for G. So G(¬¬φ) → G(φ).
    -- We need ⊢ ¬¬φ → φ (DNE). Then G(¬¬φ → φ) → F(¬¬φ) → F(φ).
    -- Contrapositive with G(...) as hypothesis: G(¬¬φ → φ) → ¬F(φ) → ¬F(¬¬φ) = G(¬¬φ → φ) → G(φ) → G(¬¬φ).
    -- WRONG direction again. BX3 gives F → F, not G → G.
    -- For G → G we need the K-distribution: G(¬¬φ → φ) and G(¬¬φ) give G(φ) via mcs_g_mp.
    -- So: G(DNE) ∈ A (from DNE theorem + TN + MCS closure), G(¬¬φ) ∈ A → G(φ) ∈ A.
    -- Now we just need G(¬¬φ) ∈ A from ¬F(¬φ) ∈ A.
    -- some_future φ.neg = untl φ.neg top. Its negation is all_future (neg (φ.neg)) when we have duality.
    -- But definitionally all_future X = neg(untl (neg X) top) = neg(some_future (neg X)).
    -- So all_future(φ.neg.neg) = neg(some_future(φ.neg.neg.neg)).
    -- That's not the same as neg(some_future φ.neg).
    -- φ.neg.neg.neg and φ.neg are NOT definitionally equal.
    -- OK this is getting complicated. Let me just use the approach from the bimodal version
    -- which uses mcs_g_mp with the K distribution.

    -- Strategy: derive all_future φ ∈ A from h, causing contradiction with h_Gφ_not.
    -- We'll skip the duality bridge and use BX3-based reasoning.
    -- From ¬F(¬φ) ∈ A: suppose G(φ) ∉ A. Then F(¬φ) ∈ A (which we're trying to prove).
    -- But we have ¬F(¬φ) ∈ A, contradiction. So G(φ) ∈ A.
    -- Wait, that's circular. h says ¬F(¬φ) ∈ A, and we're in the branch where this holds.
    -- We need to derive G(φ) ∈ A from ¬F(¬φ) ∈ A to get contradiction with h_Gφ_not.

    -- Actually we need some_future_all_future_neg_absurd pattern.
    -- We know: (some_future φ.neg).neg ∈ A. This is ¬F(¬φ) ∈ A.
    -- By DNE on the outside: ¬¬G(¬¬φ) ∈ A, i.e., G(¬¬φ) ∈ A (since ¬F(X) = ¬¬G(¬X) and DNE).
    -- Hmm, definitionally G(X) = ¬F(¬X). So F(¬φ) = ¬G(¬¬φ). ¬F(¬φ) = ¬¬G(¬¬φ).
    -- So (some_future φ.neg).neg = G(φ.neg.neg).neg.neg. NOT G(φ.neg.neg) directly.
    -- Need DNE: ¬¬G(¬¬φ) → G(¬¬φ).
    -- ¬F(¬φ) ∈ A. If G(φ) ∉ A, then F(¬φ) ∈ A (what we're trying to prove).
    -- But we're in the branch where ¬F(¬φ) ∈ A. If F(¬φ) were in A, contradiction.
    -- So either F(¬φ) ∈ A or ¬F(¬φ) ∈ A. We have ¬F(¬φ) ∈ A.
    -- We need to derive G(φ) ∈ A from ¬F(¬φ) ∈ A.
    -- Strategy: show ⊢ ¬F(¬φ) → G(φ) via the chain:
    --   ¬F(¬φ) → ¬F(¬¬¬φ) (from ⊢ ¬¬¬φ → ¬φ via BX3 contrapositive)
    --   ¬F(¬¬¬φ) = G(¬¬φ)
    --   G(¬¬φ) → G(φ) via mcs_g_mp + DNE
    -- Actually, let's use the fact that G(φ) = ¬F(¬φ) up to DNE.
    -- G(φ) = neg(some_future(neg φ)) = neg(untl (neg φ) top).
    -- ¬F(¬φ) = neg(some_future(neg φ)) = neg(untl (neg φ) top) = G(φ). Wait...
    -- Actually, G(φ) IS ¬F(¬φ) by definition!
    -- all_future φ = neg(some_future(neg φ)) = neg(untl (neg φ) top).
    -- So h : (some_future φ.neg).neg ∈ A is exactly all_future φ ∈ A!
    -- Let me check: all_future φ = neg(untl (neg φ) top).
    -- some_future(neg φ) = untl (neg φ) top.
    -- So (some_future φ.neg).neg = neg(untl (neg(neg φ)) top) WAIT NO.
    -- some_future X = untl X top. So some_future (φ.neg) = untl (φ.neg) top.
    -- (some_future φ.neg).neg = neg(untl φ.neg top) = all_future(φ.neg.neg)?
    -- NO. all_future Y = neg(some_future(neg Y)) = neg(untl (neg Y) top).
    -- So all_future(φ.neg.neg) = neg(untl (neg(φ.neg.neg)) top) = neg(untl φ.neg.neg.neg top).
    -- That's not the same as neg(untl φ.neg top) = (some_future φ.neg).neg.
    -- So (some_future φ.neg).neg ≠ all_future(φ.neg.neg) definitionally.
    -- BUT: all_future φ = neg(some_future(neg φ)) = neg(untl φ.neg top)
    --     = (untl φ.neg top).neg = (some_future φ.neg).neg
    -- WAIT: neg φ = φ.imp bot. φ.neg = φ.imp bot.
    -- some_future X = untl X top. some_future (neg φ) = untl (neg φ) top = untl (φ.imp bot) top.
    -- But some_future (φ.neg) = untl (φ.neg) top = untl (φ.imp bot) top.
    -- So some_future (neg φ) = some_future (φ.neg). And Formula.neg φ = φ.neg = φ.imp bot.
    -- all_future φ = neg(some_future(neg φ)) = (some_future(φ.neg)).neg.
    -- So all_future φ = (some_future φ.neg).neg.
    -- h says (some_future φ.neg).neg ∈ A.
    -- This IS all_future φ ∈ A by definition!
    -- So h : all_future φ ∈ A. But h_Gφ_not says all_future φ ∉ A. Contradiction!
    exact absurd h h_Gφ_not

/-- If H(φ) ∉ MCS A, then P(¬φ) ∈ A. Dual of `F_neg_of_G_not`. -/
theorem P_neg_of_H_not {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ : Formula Atom)
    (h_Hφ_not : Formula.all_past φ ∉ A) :
    Formula.some_past φ.neg ∈ A := by
  rcases temporal_negation_complete h_mcs (Formula.some_past φ.neg) with h | h
  · exact h
  · -- ¬P(¬φ) ∈ A is the same as H(φ) ∈ A (by definition), contradicting h_Hφ_not.
    exact absurd h h_Hφ_not

/-! ## Lemma 2.4: Until Witness Endpoint Construction -/

/-- The Until witness seed: {β} ∪ g_content(A) is consistent when U(γ,β) ∈ MCS A. -/
theorem until_witness_seed_consistent {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : Formula.untl β γ ∈ A) :
    Temporal.SetConsistent ({β} ∪ g_content A) := by
  have h_F_β : Formula.some_future β ∈ A := by
    have h_ax : DerivationTree FrameClass.Base [] ((Formula.untl β γ).imp (Formula.some_future β)) :=
      DerivationTree.axiom [] _ (Axiom.until_F γ β) trivial
    exact temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_ax) h_until
  exact forward_temporal_witness_seed_consistent A h_mcs β h_F_β

/-- F(γ) ∈ A for all γ ∈ C when g_content(A) ⊆ C. -/
private theorem F_mem_of_g_content_sub {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_gc : g_content A ⊆ C) (γ : Formula Atom) (h_γ : γ ∈ C) :
    Formula.some_future γ ∈ A := by
  by_contra h_not_F
  have h_neg_F : (Formula.some_future γ).neg ∈ A :=
    mcs_neg_of_not_mem h_mcs_A h_not_F
  -- ¬F(γ) ∈ A → G(¬γ) ∈ A (by duality bridge)
  -- F(γ) = ¬G(¬γ). ¬F(γ) = G(¬γ).neg.neg. Need DNE to get G(¬γ).
  -- Actually, all_future X = neg(some_future(neg X)).
  -- So G(¬γ) = neg(F(¬¬γ)). ¬F(γ) = neg(some_future γ).
  -- G(¬γ) and ¬F(γ) are NOT the same definitionally.
  -- We need: if ¬F(γ) ∈ A then G(¬γ) ∈ A.
  -- Since G(¬γ) = ¬F(¬¬γ): we need ¬F(¬¬γ) ∈ A from ¬F(γ) ∈ A.
  -- BX3 contrapositive: G(γ → ¬¬γ) → ¬F(¬¬γ) → ¬F(γ). So ¬F(γ) → ¬F(¬¬γ) needs the reverse.
  -- From ⊢ ¬¬γ → γ (DNE): G(¬¬γ → γ) → F(¬¬γ) → F(γ). Contrapositive: ¬F(γ) → ¬F(¬¬γ).
  -- So ¬F(γ) ∈ A → ¬F(¬¬γ) ∈ A = G(¬γ) ∈ A. YES.
  have h_G_neg : Formula.all_future γ.neg ∈ A := by
    -- ¬F(γ) ∈ A, and all_future(γ.neg) = neg(some_future(γ.neg.neg)) by definition.
    -- But ¬F(γ) = neg(some_future γ), and all_future(γ.neg) = neg(some_future(neg(γ.neg)))
    -- = neg(some_future(γ.neg.neg)). These are NOT the same unless γ.neg.neg = γ.
    -- We need: ¬F(γ) → G(¬γ), i.e., neg(some_future γ) → neg(some_future(neg(γ.neg)))
    -- = neg(some_future γ) → neg(some_future(γ.neg.neg)).
    -- From ⊢ γ → ¬¬γ (DNI): G(γ → ¬¬γ) by TN. BX3: G(γ→¬¬γ) → F(γ)→F(¬¬γ).
    -- So F(γ) → F(¬¬γ). Contrapositive: ¬F(¬¬γ) → ¬F(γ). But we want ¬F(γ) → ¬F(¬¬γ).
    -- That's the wrong direction for BX3.
    -- From ⊢ ¬¬γ → γ (DNE): G(¬¬γ→γ) by TN. BX3: G(¬¬γ→γ) → F(¬¬γ)→F(γ).
    -- Contrapositive: ¬F(γ) → ¬F(¬¬γ). YES.
    -- ¬F(¬¬γ) = G(¬γ) = all_future(γ.neg). But definitionally:
    -- all_future(γ.neg) = neg(some_future(neg(γ.neg))) = neg(some_future(γ.neg.neg)).
    -- ¬F(¬¬γ) = neg(some_future(γ.neg.neg)). OK these are the same!
    -- So: ⊢ ¬F(γ) → ¬F(¬¬γ) = ⊢ neg(some_future γ) → neg(some_future(γ.neg.neg))
    --   = ⊢ neg(some_future γ) → all_future(γ.neg).
    -- Build: G(DNE(γ)) = G(¬¬γ → γ) by TN.
    -- BX3: G(¬¬γ→γ) → untl(¬¬γ, ⊤) → untl(γ, ⊤) = G(¬¬γ→γ) → F(¬¬γ) → F(γ).
    -- This is a derivation tree: ⊢ G(¬¬γ→γ) → F(¬¬γ) → F(γ).
    -- Contrapositive of F(¬¬γ)→F(γ) given G(¬¬γ→γ): ¬F(γ) → ¬F(¬¬γ).
    -- Build the derivation tree for this:
    have h_dne := double_negation γ
    have h_G_dne : DerivationTree FrameClass.Base [] ((γ.neg.neg.imp γ).all_future) :=
      DerivationTree.temporal_necessitation _ h_dne
    have h_bx3 : DerivationTree FrameClass.Base [] ((γ.neg.neg.imp γ).all_future.imp
        ((Formula.untl γ.neg.neg Formula.top).imp (Formula.untl γ Formula.top))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_until γ.neg.neg γ Formula.top) trivial
    -- ⊢ F(¬¬γ) → F(γ)
    have h_F_mono : DerivationTree FrameClass.Base [] ((Formula.some_future γ.neg.neg).imp (Formula.some_future γ)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dne
    -- Contrapositive: ⊢ ¬F(γ) → ¬F(¬¬γ)
    have h_contra : DerivationTree FrameClass.Base [] ((Formula.some_future γ).neg.imp (Formula.some_future γ.neg.neg).neg) :=
      contraposition h_F_mono
    -- ¬F(γ) ∈ A → ¬F(¬¬γ) ∈ A = all_future(γ.neg) ∈ A
    exact temporal_implication_property h_mcs_A (theorem_in_mcs h_mcs_A h_contra) h_neg_F
  have h_neg_C : γ.neg ∈ C := h_gc h_G_neg
  exact mcs_not_mem_of_neg h_mcs_C h_neg_C h_γ

/-- P(α) ∈ C for all α ∈ A when g_content(A) ⊆ C. -/
private theorem P_mem_of_g_content_sub {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_gc : g_content A ⊆ C) (α : Formula Atom) (h_α : α ∈ A) :
    Formula.some_past α ∈ C := by
  have h_GP : Formula.all_future (Formula.some_past α) ∈ A := by
    have h_ax : DerivationTree FrameClass.Base [] (α.imp (Formula.all_future (Formula.some_past α))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future α) trivial
    exact temporal_implication_property h_mcs_A (theorem_in_mcs h_mcs_A h_ax) h_α
  exact h_gc h_GP

/-- BurgessR3Maximal existence from g_content inclusion. -/
private theorem burgessR3Maximal_from_g_content_sub' {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_gc : g_content A ⊆ C) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal A B C := by
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with top_def
  have h_top_A : top ∈ A :=
    theorem_in_mcs h_mcs_A (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_bR : burgessR A top C := by
    intro γ hγ
    have h_F := F_mem_of_g_content_sub h_mcs_A h_mcs_C h_gc γ hγ
    have h_bx12 : DerivationTree FrameClass.Base [] ((Formula.some_future γ).imp (Formula.untl γ top)) :=
      DerivationTree.axiom [] _ (Axiom.F_until_equiv γ) trivial
    exact temporal_implication_property h_mcs_A (theorem_in_mcs h_mcs_A h_bx12) h_F
  have h_bRS : burgessRSince C top A := by
    intro α hα
    have h_P := P_mem_of_g_content_sub h_mcs_A h_gc α hα
    have h_bx12' : DerivationTree FrameClass.Base [] ((Formula.some_past α).imp (Formula.snce α top)) :=
      DerivationTree.axiom [] _ (Axiom.P_since_equiv α) trivial
    exact temporal_implication_property h_mcs_C (theorem_in_mcs h_mcs_C h_bx12') h_P
  exact burgessR3Maximal_exists_from_seed A C top h_mcs_A h_mcs_C h_bR h_bRS h_top_A

/-- **Lemma 2.4**: Given MCS A with U(γ, β) ∈ A, there exists MCS C with
β ∈ C, g_content(A) ⊆ C, P(U(γ,β)) ∈ C, and a DCS interval set B with
BurgessR3Maximal(A, B, C). -/
noncomputable def lemma_2_4 {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : Formula.untl β γ ∈ A) :
    ∃ B C : Set (Formula Atom), Temporal.SetMaximalConsistent C ∧
      β ∈ C ∧ g_content A ⊆ C ∧
      Formula.some_past (Formula.untl β γ) ∈ C ∧
      BurgessR3Maximal A B C := by
  have h_seed_cons := until_witness_seed_consistent h_mcs γ β h_until
  obtain ⟨C, h_sup, h_C_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_β_C : β ∈ C := h_sup (Set.mem_union_left _ (Set.mem_singleton β))
  have h_g_sub : g_content A ⊆ C := fun χ hχ => h_sup (Set.mem_union_right _ hχ)
  have h_GP : Formula.all_future (Formula.some_past (Formula.untl β γ)) ∈ A := by
    have h_ax : DerivationTree FrameClass.Base [] ((Formula.untl β γ).imp
        (Formula.all_future (Formula.some_past (Formula.untl β γ)))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future (Formula.untl β γ)) trivial
    exact temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_ax) h_until
  have h_P_until_C : Formula.some_past (Formula.untl β γ) ∈ C := h_g_sub h_GP
  obtain ⟨B, h_B⟩ := burgessR3Maximal_from_g_content_sub' h_mcs h_C_mcs h_g_sub
  exact ⟨B, C, h_C_mcs, h_β_C, h_g_sub, h_P_until_C, h_B⟩

/-! ## MCS-Level Axiom Helpers -/

/-- BX10 at MCS level: U(γ,β) ∈ A implies F(β) ∈ A. -/
theorem until_F_mcs' {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : Formula.untl β γ ∈ A) :
    Formula.some_future β ∈ A :=
  until_implies_F_in_mcs h_mcs h_until

/-- BX5 at MCS level: U(γ,β) ∈ A implies U(γ∧U(γ,β), β) ∈ A. -/
theorem self_accum_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_until : Formula.untl β γ ∈ A) :
    Formula.untl β (Formula.and γ (Formula.untl β γ)) ∈ A :=
  until_self_accum_in_mcs h_mcs h_until

/-- BX5' at MCS level: snce(γ, β) ∈ A implies snce(γ ∧ snce(γ, β), β) ∈ A. -/
theorem self_accum_since_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (γ β : Formula Atom)
    (h_since : Formula.snce β γ ∈ A) :
    Formula.snce β (Formula.and γ (Formula.snce β γ)) ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.snce β γ).imp
      (Formula.snce β (Formula.and γ (Formula.snce β γ)))) :=
    DerivationTree.axiom [] _ (Axiom.self_accum_since γ β) trivial
  exact temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_ax) h_since

/-- BX4 at MCS level: φ ∈ A implies G(P(φ)) ∈ A. -/
theorem connect_future_mcs' {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ : Formula Atom)
    (h_φ : φ ∈ A) :
    Formula.all_future (Formula.some_past φ) ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] (φ.imp (Formula.all_future (Formula.some_past φ))) :=
    DerivationTree.axiom [] _ (Axiom.connect_future φ) trivial
  exact temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_ax) h_φ

/-- Conjunction introduction at MCS level. -/
theorem conj_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_φ : φ ∈ A) (h_ψ : ψ ∈ A) :
    Formula.and φ ψ ∈ A :=
  dcs_conj_closed (mcs_is_dcs h_mcs) h_φ h_ψ

/-- MCS disjunction elimination: If (φ ∨ ψ) ∈ A then φ ∈ A ∨ ψ ∈ A.
Recall φ.or ψ = φ.neg.imp ψ. -/
private theorem or_elim_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {φ ψ : Formula Atom}
    (h : (φ.or ψ) ∈ A) : φ ∈ A ∨ ψ ∈ A := by
  rcases temporal_negation_complete h_mcs φ with h_φ | h_neg_φ
  · exact Or.inl h_φ
  · exact Or.inr (temporal_implication_property h_mcs h h_neg_φ)

/-- BX7 (linear_until) at MCS level. -/
theorem linear_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ χ θ : Formula Atom)
    (h_u1 : Formula.untl ψ φ ∈ A)
    (h_u2 : Formula.untl θ χ ∈ A) :
    Formula.untl (Formula.and ψ θ) (Formula.and φ χ) ∈ A ∨
    Formula.untl (Formula.and ψ χ) (Formula.and φ χ) ∈ A ∨
    Formula.untl (Formula.and φ θ) (Formula.and φ χ) ∈ A := by
  have h_conj := conj_mcs h_mcs _ _ h_u1 h_u2
  have h_bx7 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.linear_until φ ψ χ θ) trivial
  have h_disj := temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_bx7) h_conj
  rcases or_elim_mcs h_mcs h_disj with h12 | h3
  · rcases or_elim_mcs h_mcs h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-- BX7' (linear_since) at MCS level. -/
theorem linear_since_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ χ θ : Formula Atom)
    (h_s1 : Formula.snce ψ φ ∈ A)
    (h_s2 : Formula.snce θ χ ∈ A) :
    Formula.snce (Formula.and ψ θ) (Formula.and φ χ) ∈ A ∨
    Formula.snce (Formula.and ψ χ) (Formula.and φ χ) ∈ A ∨
    Formula.snce (Formula.and φ θ) (Formula.and φ χ) ∈ A := by
  have h_conj := conj_mcs h_mcs _ _ h_s1 h_s2
  have h_bx7 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.linear_since φ ψ χ θ) trivial
  have h_disj := temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_bx7) h_conj
  rcases or_elim_mcs h_mcs h_disj with h12 | h3
  · rcases or_elim_mcs h_mcs h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-! ## Lemma 2.5: g_content Ordering Composition -/

/-- **Lemma 2.5** (composition): g_content ordering is transitive. -/
theorem lemma_2_5b {A D C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_AD : g_content A ⊆ D) (h_DC : g_content D ⊆ C) :
    g_content A ⊆ C := by
  intro φ hφ
  have h_GGφ := mcs_g_trans h_mcs_A hφ
  exact h_DC (h_AD h_GGφ)

/-- Dual: h_content ordering is transitive. -/
theorem lemma_2_5b_past {A D C : Set (Formula Atom)}
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_CD : h_content C ⊆ D) (h_DA : h_content D ⊆ A) :
    h_content C ⊆ A := by
  intro φ hφ
  have h_HHφ : Formula.all_past (Formula.all_past φ) ∈ C := mcs_h_trans h_mcs_C hφ
  exact h_DA (h_CD h_HHφ)

/-! ## Lemma 2.6: Counterexample Insertion -/

/-- **Lemma 2.6**: Given MCS A and C with g_content(A) ⊆ C,
if δ ∉ C, then there exists MCS D with ¬δ ∈ D and g_content(A) ⊆ D. -/
noncomputable def lemma_2_6 {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (_h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_g_AC : g_content A ⊆ C)
    (δ : Formula Atom)
    (h_δ_not_C : δ ∉ C) :
    ∃ D : Set (Formula Atom), Temporal.SetMaximalConsistent D ∧
      δ.neg ∈ D ∧ g_content A ⊆ D := by
  have h_Gδ_not_A : Formula.all_future δ ∉ A := by
    intro h_Gδ; exact h_δ_not_C (h_g_AC h_Gδ)
  have h_F_neg_δ := F_neg_of_G_not h_mcs_A δ h_Gδ_not_A
  have h_seed_cons := forward_temporal_witness_seed_consistent A h_mcs_A δ.neg h_F_neg_δ
  obtain ⟨D, h_sup, h_D_mcs⟩ := temporal_lindenbaum h_seed_cons
  exact ⟨D, h_D_mcs,
    h_sup (Set.mem_union_left _ (Set.mem_singleton _)),
    fun χ hχ => h_sup (Set.mem_union_right _ hχ)⟩

/-! ## Conjunction Elimination at MCS Level -/

/-- Conjunction left elimination at MCS level. -/
theorem conj_left_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_conj : Formula.and φ ψ ∈ A) :
    φ ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.and φ ψ).imp φ) := lce_imp φ ψ
  exact temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_ax) h_conj

/-- Conjunction right elimination at MCS level. -/
theorem conj_right_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_conj : Formula.and φ ψ ∈ A) :
    ψ ∈ A := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.and φ ψ).imp ψ) := rce_imp φ ψ
  exact temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_ax) h_conj

/-! ## G/H Implies F/P (Seriality) -/

/-- In an MCS, G(α) implies F(α). -/
theorem G_implies_F_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (α : Formula Atom)
    (h_G : Formula.all_future α ∈ A) :
    Formula.some_future α ∈ A := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_weak : DerivationTree FrameClass.Base [] (Formula.imp α (Formula.imp top α)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s α top) trivial
  have h_G_top_α : Formula.all_future (Formula.imp top α) ∈ A := by
    have h1 := theorem_in_mcs h_mcs (DerivationTree.temporal_necessitation _ h_weak)
    have h2 := theorem_in_mcs h_mcs (temp_k_dist_derived α (Formula.imp top α))
    exact temporal_implication_property h_mcs
      (temporal_implication_property h_mcs h2 h1) h_G
  have h_top_in : top ∈ A :=
    theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_F_top : Formula.some_future top ∈ A :=
    temporal_implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ Axiom.serial_future trivial)) h_top_in
  have h_TUT : Formula.untl top top ∈ A :=
    temporal_implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.F_until_equiv top) trivial)) h_F_top
  have h_TUα : Formula.untl α top ∈ A := by
    have h1 := temporal_implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.right_mono_until top α top) trivial))
      h_G_top_α
    exact temporal_implication_property h_mcs h1 h_TUT
  exact temporal_implication_property h_mcs
    (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.until_F top α) trivial)) h_TUα

/-- In an MCS, H(α) implies P(α). Mirror of G_implies_F_mcs. -/
theorem H_implies_P_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) (α : Formula Atom)
    (h_H : Formula.all_past α ∈ A) :
    Formula.some_past α ∈ A := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_weak : DerivationTree FrameClass.Base [] (Formula.imp α (Formula.imp top α)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s α top) trivial
  have h_H_top_α : Formula.all_past (Formula.imp top α) ∈ A := by
    have h1 := theorem_in_mcs h_mcs (past_necessitation _ h_weak)
    have h2 := theorem_in_mcs h_mcs (past_k_dist α (Formula.imp top α))
    exact temporal_implication_property h_mcs
      (temporal_implication_property h_mcs h2 h1) h_H
  have h_top_in : top ∈ A :=
    theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_P_top : Formula.some_past top ∈ A :=
    temporal_implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ Axiom.serial_past trivial)) h_top_in
  have h_TST : Formula.snce top top ∈ A :=
    temporal_implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.P_since_equiv top) trivial)) h_P_top
  have h_TSα : Formula.snce α top ∈ A := by
    have h1 := temporal_implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.right_mono_since top α top) trivial))
      h_H_top_α
    exact temporal_implication_property h_mcs h1 h_TST
  exact temporal_implication_property h_mcs
    (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.since_P top α) trivial)) h_TSα

/-! ## DCS Neg Insert Consistent -/

/-- If B is CUD and φ ∉ B, then {¬φ} ∪ B is consistent. -/
theorem dcs_neg_union_consistent' {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed Sig)
    {φ : Formula Atom} (h_not : φ ∉ Sig) :
    Temporal.SetConsistent ({φ.neg} ∪ Sig) :=
  dcs_neg_insert_consistent h_dcs.2 h_not

/-! ## R3Maximal / BurgessR3Maximal Properties -/

/-- R3Maximal negation completeness: δ ∉ B implies δ.neg ∈ B. -/
theorem r3Maximal_neg_of_not_mem {A B C : Set (Formula Atom)}
    (h_R3 : R3Maximal A B C) (δ : Formula Atom) (h_not : δ ∉ B) :
    δ.neg ∈ B := by
  by_contra h_neg_not
  have h_cons := dcs_neg_insert_consistent h_R3.1.2 h_not
  have h_dc_dcs := deductiveClosure_is_dcs h_cons
  have h_B_sub : B ⊆ deductiveClosure ({δ.neg} ∪ B) :=
    fun φ hφ => subset_deductiveClosure ({δ.neg} ∪ B) (Set.mem_union_right _ hφ)
  have h_neg_in : δ.neg ∈ deductiveClosure ({δ.neg} ∪ B) :=
    subset_deductiveClosure ({δ.neg} ∪ B) (Set.mem_union_left _ (Set.mem_singleton δ.neg))
  have h_proper : B ⊂ deductiveClosure ({δ.neg} ∪ B) :=
    ⟨h_B_sub, fun h_eq => h_neg_not (h_eq h_neg_in)⟩
  have h_r3 : r3Relation A (deductiveClosure ({δ.neg} ∪ B)) C :=
    r3Relation_subset h_R3.2.1 h_B_sub
  exact h_R3.2.2 _ (deductiveClosure_is_dcs h_cons) h_proper h_r3

/-- R3Maximal forces MCS. -/
theorem R3Maximal_is_mcs {A B C : Set (Formula Atom)}
    (h_R3 : R3Maximal A B C) : Temporal.SetMaximalConsistent B := by
  refine ⟨h_R3.1.1, ?_⟩
  intro φ h_not_φ h_cons_insert
  have h_cons : Temporal.SetConsistent ({φ} ∪ B) := by rwa [Set.insert_eq] at h_cons_insert
  have h_dc_dcs := deductiveClosure_is_dcs h_cons
  have h_B_sub : B ⊆ deductiveClosure ({φ} ∪ B) :=
    fun ψ hψ => subset_deductiveClosure ({φ} ∪ B) (Set.mem_union_right _ hψ)
  have h_φ_in : φ ∈ deductiveClosure ({φ} ∪ B) :=
    subset_deductiveClosure ({φ} ∪ B) (Set.mem_union_left _ (Set.mem_singleton φ))
  exact h_R3.2.2 _ h_dc_dcs ⟨h_B_sub, fun h_eq => h_not_φ (h_eq h_φ_in)⟩
    (r3Relation_subset h_R3.2.1 h_B_sub)

/-- An MCS has no proper DCS extension. -/
theorem mcs_no_proper_dcs_extension {B D : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent B) (h_dcs : SetDeductivelyClosed D)
    (hBD : B ⊂ D) : False := by
  obtain ⟨φ, h_φ_D, h_φ_not_B⟩ := Set.not_subset.mp hBD.2
  have h_incons := h_mcs.2 φ h_φ_not_B
  apply h_incons
  intro L hL ⟨d⟩
  exact h_dcs.1 L (fun ψ hψ => (Set.insert_subset h_φ_D hBD.1) (hL ψ hψ)) ⟨d⟩

/-! ## BurgessR3Maximal Extension Properties -/

/-- If L is a subset of {delta} union B with B a CUD, and L derives phi, then either
phi is in B, or there exists beta in B with ⊢ (beta ∧ delta) → phi. -/
theorem dc_delta_B_controlled {B : Set (Formula Atom)} (h_dcs : ClosedUnderDerivation B)
    {delta phi : Formula Atom} {L : List (Formula Atom)}
    (hL_sub : ∀ psi ∈ L, psi ∈ ({delta} : Set (Formula Atom)) ∪ B)
    (hL_deriv : DerivationTree FrameClass.Base L phi) :
    (phi ∈ B) ∨ (∃ beta ∈ B, Nonempty (DerivationTree FrameClass.Base [] ((Formula.and beta delta).imp phi))) := by
  haveI : ∀ x : Formula Atom, Decidable (x ∈ B) := fun x => Classical.propDecidable _
  by_cases h_delta_L : delta ∈ L
  · let L_B := L.filter (· ∈ B)
    have hL_sub_dB : L ⊆ delta :: L_B := by
      intro psi hpsi
      by_cases h_B : psi ∈ B
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hpsi, decide_eq_true_eq.mpr h_B⟩)
      · rcases hL_sub psi hpsi with h | h
        · rw [Set.mem_singleton_iff.mp h]; exact .head _
        · exact absurd h h_B
    have d_w : DerivationTree FrameClass.Base (delta :: L_B) phi :=
      DerivationTree.weakening L (delta :: L_B) phi hL_deriv hL_sub_dB
    have d_imp := deduction_theorem L_B delta phi d_w
    have hLB_sub : ∀ psi ∈ L_B, psi ∈ B := by
      intro psi hpsi; exact decide_eq_true_eq.mp (List.mem_filter.mp hpsi).2
    by_cases hLB_empty : L_B = []
    · rw [hLB_empty] at d_imp
      -- When L_B is empty, ⊢ delta → phi. Need ⊢ (top ∧ delta) → phi.
      have h_top_B : ((Formula.bot : Formula Atom).imp Formula.bot) ∈ B :=
        cud_contains_theorems h_dcs
          (DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.efq (Formula.bot : Formula Atom)) trivial)
      exact Or.inr ⟨Formula.bot.imp Formula.bot, h_top_B, ⟨imp_trans (rce_imp (Formula.bot.imp Formula.bot) delta) d_imp⟩⟩
    · have h_imp_B : delta.imp phi ∈ B := h_dcs L_B _ hLB_sub d_imp
      right
      refine ⟨delta.imp phi, h_imp_B, ⟨?_⟩⟩
      have h_l : DerivationTree FrameClass.Base [(Formula.and (delta.imp phi) delta)] (delta.imp phi) :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)]
          (Formula.and (delta.imp phi) delta) (delta.imp phi)
          (DerivationTree.weakening [] [(Formula.and (delta.imp phi) delta)] _
            (lce_imp (delta.imp phi) delta) (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp))
      have h_r : DerivationTree FrameClass.Base [(Formula.and (delta.imp phi) delta)] delta :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)]
          (Formula.and (delta.imp phi) delta) delta
          (DerivationTree.weakening [] [(Formula.and (delta.imp phi) delta)] _
            (rce_imp (delta.imp phi) delta) (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp))
      have h_mp : DerivationTree FrameClass.Base [(Formula.and (delta.imp phi) delta)] phi :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)] delta phi h_l h_r
      exact deduction_theorem [] (Formula.and (delta.imp phi) delta) phi h_mp
  · left
    have hL_B : ∀ psi ∈ L, psi ∈ B := by
      intro psi hpsi
      rcases hL_sub psi hpsi with h | h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hpsi) h_delta_L
      · exact h
    exact h_dcs L phi hL_B hL_deriv

/-- BurgessR3Maximal extension fails: if δ ∉ B, then DC({δ} ∪ B) does NOT satisfy burgessR3. -/
theorem BurgessR3Maximal_extension_fails {A B C : Set (Formula Atom)}
    (h_R3M : BurgessR3Maximal A B C)
    {delta : Formula Atom} (h_delta_not : delta ∉ B) :
    ¬burgessR3 A (deductiveClosure ({delta} ∪ B)) C := by
  intro h_r3
  have h_cud : ClosedUnderDerivation (deductiveClosure ({delta} ∪ B)) :=
    deductiveClosure_closed_under_derivation _
  have h_sub : B ⊆ deductiveClosure ({delta} ∪ B) :=
    fun phi hphi => subset_deductiveClosure ({delta} ∪ B) (Set.mem_union_right _ hphi)
  have h_delta_in : delta ∈ deductiveClosure ({delta} ∪ B) :=
    subset_deductiveClosure ({delta} ∪ B) (Set.mem_union_left _ (Set.mem_singleton delta))
  have h_proper : B ⊂ deductiveClosure ({delta} ∪ B) :=
    ⟨h_sub, fun h_eq => h_delta_not (h_eq h_delta_in)⟩
  exact h_R3M.2.2 _ h_cud h_proper h_r3

/-- dc_delta_B_burgessR3: Extension of B by delta preserves burgessR3. -/
theorem dc_delta_B_burgessR3 {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_dcs : ClosedUnderDerivation B)
    (h_r3 : burgessR3 A B C)
    {delta : Formula Atom}
    (h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C, Formula.untl gamma (Formula.and beta delta) ∈ A)
    (h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A, Formula.snce alpha (Formula.and beta delta) ∈ C) :
    burgessR3 A (deductiveClosure ({delta} ∪ B)) C := by
  constructor
  · intro phi hphi gamma hgamma
    obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
    rcases dc_delta_B_controlled h_dcs hL_sub d with h_B | ⟨beta, hbeta, ⟨h_impl⟩⟩
    · exact h_r3.1 phi h_B gamma hgamma
    · exact untl_left_mono_thm h_mcs_A h_impl (h_until_all beta hbeta gamma hgamma)
  · intro phi hphi alpha halpha
    obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
    rcases dc_delta_B_controlled h_dcs hL_sub d with h_B | ⟨beta, hbeta, ⟨h_impl⟩⟩
    · exact h_r3.2 phi h_B alpha halpha
    · exact snce_left_mono_thm h_mcs_C h_impl (h_since_all beta hbeta alpha halpha)

/-! ## g_content(A) ⊆ B from BurgessR3Maximal -/

/-- Helper: ⊢ φ → (β → (β ∧ φ)). Conjunction introduction curried. -/
private noncomputable def conj_intro_curried (β φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (β.imp (Formula.and β φ))) := by
  have h1 : DerivationTree FrameClass.Base [β, φ] (Formula.and β φ) :=
    DerivationTree.modus_ponens [β, φ] _ _
      (DerivationTree.modus_ponens [β, φ] β _
        (DerivationTree.weakening [] [β, φ] _
          (pairing β φ) (List.nil_subset _))
        (DerivationTree.assumption _ β (by simp)))
      (DerivationTree.assumption _ φ (by simp))
  exact deduction_theorem [] φ _ (deduction_theorem [φ] β _ h1)

/-- Helper: ⊢ φ → (φ.neg → ψ) for any ψ. -/
private noncomputable def ex_falso_from_assumption (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.neg.imp ψ)) := by
  have h1 : DerivationTree FrameClass.Base [φ.neg, φ] Formula.bot :=
    DerivationTree.modus_ponens [φ.neg, φ] φ Formula.bot
      (DerivationTree.assumption _ φ.neg (by simp))
      (DerivationTree.assumption _ φ (by simp))
  have h2 : DerivationTree FrameClass.Base [φ.neg, φ] ψ :=
    DerivationTree.modus_ponens [φ.neg, φ] Formula.bot ψ
      (DerivationTree.weakening [] [φ.neg, φ] (Formula.bot.imp ψ)
        (efq_axiom ψ) (List.nil_subset _))
      h1
  exact deduction_theorem [] φ _ (deduction_theorem [φ] φ.neg ψ h2)

/-- When {φ} ∪ B is inconsistent with CUD B, then φ.neg ∈ B. -/
private theorem neg_mem_of_inconsistent_union {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B)
    {φ : Formula Atom} (h_not_cons : ¬Temporal.SetConsistent ({φ} ∪ B)) :
    φ.neg ∈ B := by
  by_contra h_neg_not_B
  apply h_not_cons
  intro L hL ⟨d⟩
  set M := L.filter (fun x => !decide (x = φ)) with hM_def
  have hM_sub_B : ∀ ψ ∈ M, ψ ∈ B := by
    intro ψ hψ; rw [hM_def] at hψ
    have h_mem := List.mem_filter.mp hψ
    have h1 : ψ ∈ L := h_mem.1
    have h2 : ψ ≠ φ := by simp at h_mem; exact h_mem.2
    rcases hL ψ h1 with h | h
    · exact absurd (Set.mem_singleton_iff.mp h) h2
    · exact h
  have hL_sub_φM : L ⊆ φ :: M := by
    intro x hx
    by_cases heq : x = φ
    · subst heq; exact .head M
    · exact .tail _ (List.mem_filter.mpr ⟨hx, by simp; exact heq⟩)
  have d_w : DerivationTree FrameClass.Base (φ :: M) Formula.bot :=
    DerivationTree.weakening L (φ :: M) Formula.bot d hL_sub_φM
  have d_neg : DerivationTree FrameClass.Base M φ.neg := deduction_theorem M φ Formula.bot d_w
  exact h_neg_not_B (h_cud M φ.neg hM_sub_B d_neg)

/-- G(φ.neg → ψ) ∈ A from G(φ) ∈ A, using ex_falso_from_assumption + temporal necessitation + K. -/
private theorem G_ex_falso_strengthen {A : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (φ ψ : Formula Atom)
    (h_Gφ : Formula.all_future φ ∈ A) :
    (φ.neg.imp ψ).all_future ∈ A := by
  have d_ef := ex_falso_from_assumption φ ψ
  exact temporal_implication_property h_mcs_A
    (temporal_implication_property h_mcs_A
      (theorem_in_mcs h_mcs_A (temp_k_dist_derived φ (φ.neg.imp ψ)))
      (theorem_in_mcs h_mcs_A (DerivationTree.temporal_necessitation _ d_ef)))
    h_Gφ

/-- When {φ} ∪ B is inconsistent, burgessR3(A, Set.univ, C). -/
private theorem burgessR3_univ_of_inconsistent_ext {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3 : burgessR3 A B C)
    {φ : Formula Atom} (h_Gφ : Formula.all_future φ ∈ A)
    (h_neg_in_B : φ.neg ∈ B) :
    burgessR3 A Set.univ C := by
  constructor
  · intro ψ _ γ hγ
    have h_untl_neg := h_r3.1 φ.neg h_neg_in_B γ hγ
    have h_G_impl := G_ex_falso_strengthen h_mcs_A φ ψ h_Gφ
    exact untl_left_mono_G h_mcs_A h_G_impl h_untl_neg
  · intro ψ _ α hα
    have h_burgessR : burgessR A ψ C := fun γ hγ => by
      have h_untl_neg := h_r3.1 φ.neg h_neg_in_B γ hγ
      have h_G_impl := G_ex_falso_strengthen h_mcs_A φ ψ h_Gφ
      exact untl_left_mono_G h_mcs_A h_G_impl h_untl_neg
    exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR α hα

/-- Set.univ is ClosedUnderDerivation. -/
theorem set_univ_closed_under_derivation : ClosedUnderDerivation (Set.univ : Set (Formula Atom)) :=
  fun _ _ _ _ => Set.mem_univ _

/-- Inconsistent CUD set equals Set.univ. -/
private theorem closed_under_derivation_inconsistent_eq_univ
    {D : Set (Formula Atom)} (h_cud : ClosedUnderDerivation D) (h_not_cons : ¬Temporal.SetConsistent D) :
    D = Set.univ := by
  have h_exists : ∃ L : List (Formula Atom), (∀ φ ∈ L, φ ∈ D) ∧ Nonempty (DerivationTree FrameClass.Base L (Formula.bot : Formula Atom)) := by
    by_contra h_all
    apply h_not_cons
    intro L hL hd
    exact h_all ⟨L, hL, hd⟩
  obtain ⟨L, hL, ⟨d⟩⟩ := h_exists
  have h_bot : (Formula.bot : Formula Atom) ∈ D := h_cud L Formula.bot hL d
  ext φ; simp only [Set.mem_univ, iff_true]
  have d_efq : DerivationTree FrameClass.Base [(Formula.bot : Formula Atom)] φ :=
    DerivationTree.modus_ponens [(Formula.bot : Formula Atom)] Formula.bot φ
      (DerivationTree.weakening [] [(Formula.bot : Formula Atom)] ((Formula.bot : Formula Atom).imp φ)
        (efq_axiom φ) (List.nil_subset _))
      (DerivationTree.assumption [(Formula.bot : Formula Atom)] Formula.bot (by simp))
  exact h_cud [(Formula.bot : Formula Atom)] φ (fun ψ hψ => by simp at hψ; rw [hψ]; exact h_bot) d_efq

/-- g_content(A) ⊆ B from BurgessR3Maximal: every G(φ) ∈ A has φ ∈ B. -/
theorem g_content_sub {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A)
    (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_R3M : BurgessR3Maximal A B C) :
    g_content A ⊆ B := by
  intro φ hφ
  by_contra h_not
  have h_dcs : ClosedUnderDerivation B := h_R3M.1
  have h_r3 : burgessR3 A B C := h_R3M.2.1
  -- Case split: is {φ} ∪ B consistent?
  by_cases h_cons : Temporal.SetConsistent ({φ} ∪ B)
  · -- Consistent case: show DC({φ}∪B) satisfies burgessR3, contradicting maximality
    have h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C,
        Formula.untl gamma (Formula.and beta φ) ∈ A := by
      intro beta h_beta gamma h_gamma
      have h_untl := h_r3.1 beta h_beta gamma h_gamma
      -- G(φ) ∈ A, so G(β → β ∧ φ) ∈ A
      have h_flip := conj_intro_curried beta φ
      have h_G_flip := theorem_in_mcs h_mcs_A (DerivationTree.temporal_necessitation _ h_flip)
      have h_kd := temp_k_dist_derived φ (beta.imp (Formula.and beta φ))
      have h_G_guard_str : (beta.imp (Formula.and beta φ)).all_future ∈ A :=
        temporal_implication_property h_mcs_A
          (temporal_implication_property h_mcs_A (theorem_in_mcs h_mcs_A h_kd) h_G_flip) hφ
      exact untl_left_mono_G h_mcs_A h_G_guard_str h_untl
    have h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A,
        Formula.snce alpha (Formula.and beta φ) ∈ C := by
      intro beta h_beta alpha h_alpha
      have h_burgessR : burgessR A (Formula.and beta φ) C :=
        fun gamma h_gamma => h_until_all beta h_beta gamma h_gamma
      exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR alpha h_alpha
    have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
    exact absurd h_r3_ext (BurgessR3Maximal_extension_fails h_R3M h_not)
  · -- Inconsistent case: φ.neg ∈ B, derive burgessR3(A, Set.univ, C)
    have h_neg_in := neg_mem_of_inconsistent_union h_dcs h_cons
    have h_r3_univ := burgessR3_univ_of_inconsistent_ext h_mcs_A h_mcs_C h_r3 hφ h_neg_in
    -- Set.univ is CUD, B ⊂ Set.univ (B is consistent since BurgessR3Maximal has a DCS part)
    -- Actually B is CUD. B ≠ Set.univ since ⊥ ∉ B (B is consistent? Not necessarily for BurgessR3Maximal).
    -- BurgessR3Maximal only requires CUD, not SDC. But if B were inconsistent, B = Set.univ.
    -- In that case, φ ∈ B = Set.univ, contradicting h_not. So B must be consistent.
    have h_B_ne_univ : B ≠ Set.univ := by
      intro h_eq
      exact h_not (h_eq ▸ Set.mem_univ φ)
    have h_B_cons : Temporal.SetConsistent B := by
      by_contra h_not_cons
      exact h_B_ne_univ (closed_under_derivation_inconsistent_eq_univ h_dcs h_not_cons)
    -- B ⊂ Set.univ (B is a consistent proper subset)
    have h_proper : B ⊂ Set.univ := by
      constructor
      · exact fun _ _ => Set.mem_univ _
      · intro h_eq; exact h_B_ne_univ (Set.eq_univ_iff_forall.mpr (fun x => h_eq (Set.mem_univ x)))
    exact h_R3M.2.2 Set.univ set_univ_closed_under_derivation h_proper h_r3_univ

/-! ## Xu Lemma 2.3: Guard Strengthening via left_mono_until_G -/

/-- Xu Lemma 2.3 (i): If R(A, B, C) then snce(alpha, top) ∈ B for all alpha ∈ A. -/
theorem xu_lemma_2_3_since_top {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {alpha : Formula Atom} (h_alpha : alpha ∈ A) :
    Formula.snce alpha (Formula.bot.imp Formula.bot) ∈ B := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  -- G(snce(alpha, top)) ∈ A: from alpha ∈ A via BX4 + BX12'
  have h_bx4 : DerivationTree FrameClass.Base [] (alpha.imp (alpha.some_past.all_future)) :=
    DerivationTree.axiom [] _ (Axiom.connect_future alpha) trivial
  have h_G_P_alpha : alpha.some_past.all_future ∈ A :=
    temporal_implication_property h_mcs_A (theorem_in_mcs h_mcs_A h_bx4) h_alpha
  have h_bx12' : DerivationTree FrameClass.Base [] (alpha.some_past.imp (Formula.snce alpha top)) :=
    DerivationTree.axiom [] _ (Axiom.P_since_equiv alpha) trivial
  have h_G_impl : (alpha.some_past.imp (Formula.snce alpha top)).all_future ∈ A :=
    theorem_in_mcs h_mcs_A (DerivationTree.temporal_necessitation _ h_bx12')
  have h_temp_k := temp_k_dist_derived alpha.some_past (Formula.snce alpha top)
  have h_G_snce : (Formula.snce alpha top).all_future ∈ A :=
    temporal_implication_property h_mcs_A
      (temporal_implication_property h_mcs_A (theorem_in_mcs h_mcs_A h_temp_k) h_G_impl)
      h_G_P_alpha
  -- Until condition: ∀ beta ∈ B, ∀ gamma ∈ C, untl(gamma, beta ∧ snce(alpha, top)) ∈ A
  have h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C,
      Formula.untl gamma (Formula.and beta (Formula.snce alpha top)) ∈ A := by
    intro beta h_beta gamma h_gamma
    have h_untl := h_r3.1 beta h_beta gamma h_gamma
    have h_flip := conj_intro_curried beta (Formula.snce alpha top)
    have h_G_flip := theorem_in_mcs h_mcs_A (DerivationTree.temporal_necessitation _ h_flip)
    have h_temp_k2 := temp_k_dist_derived (Formula.snce alpha top) (beta.imp (Formula.and beta (Formula.snce alpha top)))
    have h_G_guard_str : (beta.imp (Formula.and beta (Formula.snce alpha top))).all_future ∈ A :=
      temporal_implication_property h_mcs_A
        (temporal_implication_property h_mcs_A (theorem_in_mcs h_mcs_A h_temp_k2) h_G_flip)
        h_G_snce
    exact untl_left_mono_G h_mcs_A h_G_guard_str h_untl
  -- Since condition: from burgessR_implies_burgessRSince
  have h_since_all : ∀ beta ∈ B, ∀ alpha' ∈ A,
      Formula.snce alpha' (Formula.and beta (Formula.snce alpha top)) ∈ C := by
    intro beta h_beta alpha' h_alpha'
    have h_burgessR : burgessR A (Formula.and beta (Formula.snce alpha top)) C :=
      fun gamma h_gamma => h_until_all beta h_beta gamma h_gamma
    exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR alpha' h_alpha'
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-- Xu Lemma 2.3 (ii): If R(A, B, C) then untl(gamma, top) ∈ B for all gamma ∈ C. -/
theorem xu_lemma_2_3_until_top {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {gamma : Formula Atom} (h_gamma : gamma ∈ C) :
    Formula.untl gamma (Formula.bot.imp Formula.bot) ∈ B := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  -- H(untl(gamma, top)) ∈ C: from gamma ∈ C via BX4' + BX12
  have h_bx4' : DerivationTree FrameClass.Base [] (gamma.imp (gamma.some_future.all_past)) :=
    DerivationTree.axiom [] _ (Axiom.connect_past gamma) trivial
  have h_H_F_gamma : gamma.some_future.all_past ∈ C :=
    temporal_implication_property h_mcs_C (theorem_in_mcs h_mcs_C h_bx4') h_gamma
  have h_bx12 : DerivationTree FrameClass.Base [] (gamma.some_future.imp (Formula.untl gamma top)) :=
    DerivationTree.axiom [] _ (Axiom.F_until_equiv gamma) trivial
  have h_H_impl : (gamma.some_future.imp (Formula.untl gamma top)).all_past ∈ C :=
    theorem_in_mcs h_mcs_C (past_necessitation _ h_bx12)
  have h_past_k := past_k_dist gamma.some_future (Formula.untl gamma top)
  have h_H_untl : (Formula.untl gamma top).all_past ∈ C :=
    temporal_implication_property h_mcs_C
      (temporal_implication_property h_mcs_C (theorem_in_mcs h_mcs_C h_past_k) h_H_impl)
      h_H_F_gamma
  -- Since condition
  have h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A,
      Formula.snce alpha (Formula.and beta (Formula.untl gamma top)) ∈ C := by
    intro beta h_beta alpha' h_alpha'
    have h_snce := h_r3.2 beta h_beta alpha' h_alpha'
    have h_flip := conj_intro_curried beta (Formula.untl gamma top)
    have h_H_flip := theorem_in_mcs h_mcs_C (past_necessitation _ h_flip)
    have h_past_k2 := past_k_dist (Formula.untl gamma top) (beta.imp (Formula.and beta (Formula.untl gamma top)))
    have h_H_guard_str : (beta.imp (Formula.and beta (Formula.untl gamma top))).all_past ∈ C :=
      temporal_implication_property h_mcs_C
        (temporal_implication_property h_mcs_C (theorem_in_mcs h_mcs_C h_past_k2) h_H_flip)
        h_H_untl
    exact snce_left_mono_H h_mcs_C h_H_guard_str h_snce
  -- Until condition from burgessRSince_implies_burgessR
  have h_until_all : ∀ beta ∈ B, ∀ gamma' ∈ C,
      Formula.untl gamma' (Formula.and beta (Formula.untl gamma top)) ∈ A := by
    intro beta h_beta gamma' h_gamma'
    have h_burgessRSince : burgessRSince C (Formula.and beta (Formula.untl gamma top)) A :=
      fun alpha h_alpha => h_since_all beta h_beta alpha h_alpha
    exact burgessRSince_implies_burgessR h_mcs_A h_mcs_C h_burgessRSince gamma' h_gamma'
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-! ## Derivation-Level Monotonicity -/

/-- Derivation-level left_mono for Until. -/
private noncomputable def untl_left_mono_deriv (φ ψ χ : Formula Atom)
    (h_impl : DerivationTree FrameClass.Base [] (φ.imp χ)) :
    DerivationTree FrameClass.Base [] ((Formula.untl ψ φ).imp (Formula.untl ψ χ)) := by
  have h_G := DerivationTree.temporal_necessitation _ h_impl
  have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.left_mono_until_G φ χ ψ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_G

/-- Derivation-level left_mono for Since. -/
private noncomputable def snce_left_mono_deriv (φ ψ χ : Formula Atom)
    (h_impl : DerivationTree FrameClass.Base [] (φ.imp χ)) :
    DerivationTree FrameClass.Base [] ((Formula.snce ψ φ).imp (Formula.snce ψ χ)) := by
  have h_H := past_necessitation _ h_impl
  have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.left_mono_since_H φ χ ψ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_H

/-- Right monotonicity for Until at MCS level. -/
private theorem right_mono_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {φ ψ χ : Formula Atom}
    (h_impl : DerivationTree FrameClass.Base [] (ψ.imp χ))
    (h_untl : Formula.untl ψ φ ∈ A) :
    Formula.untl χ φ ∈ A := by
  have h_G_impl : Formula.all_future (ψ.imp χ) ∈ A :=
    theorem_in_mcs h_mcs (DerivationTree.temporal_necessitation _ h_impl)
  have h_bx3 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_until ψ χ φ) trivial
  exact temporal_implication_property h_mcs
    (temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_bx3) h_G_impl) h_untl

/-- Right monotonicity for Since at MCS level. -/
private theorem right_mono_since_mcs {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) {φ ψ χ : Formula Atom}
    (h_impl : DerivationTree FrameClass.Base [] (ψ.imp χ))
    (h_snce : Formula.snce ψ φ ∈ C) :
    Formula.snce χ φ ∈ C := by
  have h_H_impl : Formula.all_past (ψ.imp χ) ∈ C :=
    theorem_in_mcs h_mcs (past_necessitation _ h_impl)
  have h_bx3' := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_since ψ χ φ) trivial
  exact temporal_implication_property h_mcs
    (temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_bx3') h_H_impl) h_snce

/-! ## BX13/BX13' at MCS Level -/

/-- BX13 (enrichment_until) at MCS level. -/
theorem enrichment_until_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {phi psi p : Formula Atom}
    (h_p : p ∈ A)
    (h_untl : Formula.untl psi phi ∈ A) :
    Formula.untl (Formula.and psi (Formula.snce p phi)) phi ∈ A := by
  have h_conj := conj_mcs h_mcs p (Formula.untl psi phi) h_p h_untl
  have h_bx13 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.enrichment_until phi psi p) trivial
  exact temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_bx13) h_conj

/-- BX13' (enrichment_since) at MCS level. -/
theorem enrichment_since_mcs {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) {phi psi p : Formula Atom}
    (h_p : p ∈ C)
    (h_snce : Formula.snce psi phi ∈ C) :
    Formula.snce (Formula.and psi (Formula.untl p phi)) phi ∈ C := by
  have h_conj := conj_mcs h_mcs p (Formula.snce psi phi) h_p h_snce
  have h_bx13 := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.enrichment_since phi psi p) trivial
  exact temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_bx13) h_conj

/-! ## F/P Monotonicity -/

/-- F-monotonicity at MCS level. -/
private theorem F_mono_mcs {A : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent A) {phi psi : Formula Atom}
    (h_impl : DerivationTree FrameClass.Base [] (phi.imp psi))
    (h_F : Formula.some_future phi ∈ A) :
    Formula.some_future psi ∈ A := by
  -- F(phi) = untl phi top. G(phi → psi) → F(phi) → F(psi) via right_mono_until.
  exact right_mono_until_mcs h_mcs h_impl h_F

/-- P-monotonicity at MCS level. -/
private theorem P_mono_mcs {C : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent C) {phi psi : Formula Atom}
    (h_impl : DerivationTree FrameClass.Base [] (phi.imp psi))
    (h_P : Formula.some_past phi ∈ C) :
    Formula.some_past psi ∈ C := by
  exact right_mono_since_mcs h_mcs h_impl h_P

/-! ## Xu Lemma 3.2.1: Full Guard Strengthening -/

/-- Xu Lemma 3.2.1 (i): If R(A, B, C) then untl(gamma, beta) ∈ B for all beta ∈ B, gamma ∈ C. -/
theorem xu_lemma_3_2_1_until {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {beta : Formula Atom} (h_beta : beta ∈ B)
    {gamma : Formula Atom} (h_gamma : gamma ∈ C) :
    Formula.untl gamma beta ∈ B := by
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  -- Show both conditions of dc_delta_B_burgessR3 hold
  -- If they held universally, we'd get burgessR3 for the extension, contradiction.
  -- So some condition must fail, giving us a neg-until witness.
  -- But by the standard maximality argument, the conditions DO hold when we
  -- strengthen the guard with BX5 + monotonicity.
  -- Strategy: show burgessR3(A, DC({untl(gamma,beta)} ∪ B), C) via dc_delta_B_burgessR3.
  -- Until condition: ∀ beta' ∈ B, ∀ gamma' ∈ C, untl(gamma', beta' ∧ untl(gamma, beta)) ∈ A
  have h_until_all : ∀ beta' ∈ B, ∀ gamma' ∈ C,
      Formula.untl gamma' (Formula.and beta' (Formula.untl gamma beta)) ∈ A := by
    intro beta' h_beta' gamma' h_gamma'
    -- From burgessR3: untl(gamma'', beta'') ∈ A where gamma'' = gamma ∧ gamma', beta'' = beta ∧ beta'
    have h_beta'' : Formula.and beta beta' ∈ B := cud_conj_closed h_dcs h_beta h_beta'
    have h_gamma'' : Formula.and gamma gamma' ∈ C := conj_mcs h_mcs_C gamma gamma' h_gamma h_gamma'
    have h_untl := h_r3.1 (Formula.and beta beta') h_beta'' (Formula.and gamma gamma') h_gamma''
    -- h_untl : untl(γ∧γ', β∧β') ∈ A, i.e., (β∧β') guards until (γ∧γ') happens
    -- BX5: self_accum takes (guard, event): untl(event, guard) → untl(event, guard ∧ untl(event, guard))
    have h_sa := self_accum_until_mcs h_mcs_A (Formula.and beta beta') (Formula.and gamma gamma') h_untl
    -- Monotonicity: (β∧β') ∧ untl(γ∧γ', β∧β') → β' ∧ untl(γ, β)
    -- Component 1: (β∧β') → β' via right projection
    -- Component 2: untl(γ∧γ', β∧β') → untl(γ, β) via right_mono + left_mono
    --   ⊢ γ∧γ' → γ (left proj), ⊢ β∧β' → β (left proj)
    --   BX3: G(γ∧γ' → γ) → untl(γ∧γ', β∧β') → untl(γ, β∧β')
    --   BX2G: G(β∧β' → β) → untl(γ, β∧β') → untl(γ, β)
    have h_guard_r : DerivationTree FrameClass.Base [] (((Formula.and beta beta').and (Formula.untl (Formula.and gamma gamma') (Formula.and beta beta'))).imp
        (Formula.and beta' (Formula.untl gamma beta))) := by
      -- Build the pairing
      -- Left: ⊢ (x ∧ y) → β'  where x = β∧β', y = untl(γ∧γ', β∧β')
      -- Right: ⊢ (x ∧ y) → untl(γ, β)
      -- For right: ⊢ y → untl(γ, β)
      --   = ⊢ untl(γ∧γ', β∧β') → untl(γ, β)
      --   From ⊢ γ∧γ' → γ and ⊢ β∧β' → β via right_mono + left_mono
      have h_event_proj := lce_imp gamma gamma'  -- ⊢ γ∧γ' → γ
      have h_guard_proj := lce_imp beta beta'    -- ⊢ β∧β' → β
      -- ⊢ untl(γ∧γ', β∧β') → untl(γ, β∧β') via right_mono (event)
      have h1 : DerivationTree FrameClass.Base [] ((Formula.untl (Formula.and gamma gamma') (Formula.and beta beta')).imp
          (Formula.untl gamma (Formula.and beta beta'))) := by
        have h_G := DerivationTree.temporal_necessitation _ h_event_proj
        have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_until (Formula.and gamma gamma') gamma (Formula.and beta beta')) trivial
        exact DerivationTree.modus_ponens [] _ _ h_ax h_G
      -- ⊢ untl(γ, β∧β') → untl(γ, β) via left_mono (guard)
      have h2 : DerivationTree FrameClass.Base [] ((Formula.untl gamma (Formula.and beta beta')).imp
          (Formula.untl gamma beta)) :=
        untl_left_mono_deriv (Formula.and beta beta') gamma beta h_guard_proj
      -- ⊢ untl(γ∧γ', β∧β') → untl(γ, β)
      have h_untl_proj := imp_trans h1 h2
      -- Now build the pairing: ⊢ x∧y → β' ∧ untl(γ, β)
      -- ⊢ x∧y → β' from ⊢ x → β' via x = β∧β' → β' and ⊢ x∧y → x
      have h_left := imp_trans (lce_imp (Formula.and beta beta') (Formula.untl (Formula.and gamma gamma') (Formula.and beta beta')))
        (rce_imp beta beta')
      -- ⊢ x∧y → untl(γ,β) from ⊢ y → untl(γ,β) and ⊢ x∧y → y
      have h_right := imp_trans (rce_imp (Formula.and beta beta') (Formula.untl (Formula.and gamma gamma') (Formula.and beta beta')))
        h_untl_proj
      -- Combine: ⊢ x∧y → β' ∧ untl(γ, β) using pairing
      -- Need: from ⊢ A → B and ⊢ A → C, derive ⊢ A → B ∧ C
      -- Build in context [A]: B and C, then apply pairing
      have := DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.untl (Formula.and gamma gamma') (Formula.and beta beta')))] _ _
        (DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.untl (Formula.and gamma gamma') (Formula.and beta beta')))] _ _
          (DerivationTree.weakening [] [_] _ (pairing beta' (Formula.untl gamma beta)) (List.nil_subset _))
          (DerivationTree.modus_ponens [_] _ _
            (DerivationTree.weakening [] [_] _ h_left (List.nil_subset _))
            (DerivationTree.assumption _ _ (by simp))))
        (DerivationTree.modus_ponens [_] _ _
          (DerivationTree.weakening [] [_] _ h_right (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp)))
      exact deduction_theorem [] _ _ this
    -- Apply left_mono: G(guard_str) → untl(γ∧γ', (β∧β') ∧ untl(γ∧γ', β∧β')) → untl(γ∧γ', β' ∧ untl(γ, β))
    have h_step1 := untl_left_mono_thm h_mcs_A h_guard_r h_sa
    -- Now ⊢ γ∧γ' → γ' to go from untl(γ∧γ', ...) to untl(γ', ...)
    have h_event_proj_r := rce_imp gamma gamma'
    exact right_mono_until_mcs h_mcs_A h_event_proj_r h_step1
  -- Since condition from burgessR_implies_burgessRSince
  have h_since_all : ∀ beta' ∈ B, ∀ alpha ∈ A,
      Formula.snce alpha (Formula.and beta' (Formula.untl gamma beta)) ∈ C := by
    intro beta' h_beta' alpha h_alpha
    have h_burgessR : burgessR A (Formula.and beta' (Formula.untl gamma beta)) C :=
      fun gamma' h_gamma' => h_until_all beta' h_beta' gamma' h_gamma'
    exact burgessR_implies_burgessRSince h_mcs_A h_mcs_C h_burgessR alpha h_alpha
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-- Xu Lemma 3.2.1 (ii): If R(A, B, C) then snce(alpha, beta) ∈ B for all beta ∈ B, alpha ∈ A. -/
theorem xu_lemma_3_2_1_since {A B C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_r3m : BurgessR3Maximal A B C)
    {beta : Formula Atom} (h_beta : beta ∈ B)
    {alpha : Formula Atom} (h_alpha : alpha ∈ A) :
    Formula.snce alpha beta ∈ B := by
  have h_dcs : ClosedUnderDerivation B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails h_r3m h_not_in_B
  -- Since condition (dual of xu_lemma_3_2_1_until)
  have h_since_all : ∀ beta' ∈ B, ∀ alpha' ∈ A,
      Formula.snce alpha' (Formula.and beta' (Formula.snce alpha beta)) ∈ C := by
    intro beta' h_beta' alpha' h_alpha'
    have h_beta'' : Formula.and beta beta' ∈ B := cud_conj_closed h_dcs h_beta h_beta'
    have h_alpha'' : Formula.and alpha alpha' ∈ A := conj_mcs h_mcs_A alpha alpha' h_alpha h_alpha'
    have h_snce := h_r3.2 (Formula.and beta beta') h_beta'' (Formula.and alpha alpha') h_alpha''
    -- h_snce : snce(α∧α', β∧β') ∈ C. self_accum_since takes (guard, event)
    have h_sa := self_accum_since_mcs h_mcs_C (Formula.and beta beta') (Formula.and alpha alpha') h_snce
    -- Monotonicity to get snce(α', β' ∧ snce(α, β)) from snce(α∧α', (β∧β') ∧ snce(α∧α', β∧β'))
    have h_guard_r : DerivationTree FrameClass.Base [] (((Formula.and beta beta').and (Formula.snce (Formula.and alpha alpha') (Formula.and beta beta'))).imp
        (Formula.and beta' (Formula.snce alpha beta))) := by
      have h_event_proj := lce_imp alpha alpha'
      have h_guard_proj := lce_imp beta beta'
      have h1 : DerivationTree FrameClass.Base [] ((Formula.snce (Formula.and alpha alpha') (Formula.and beta beta')).imp
          (Formula.snce alpha (Formula.and beta beta'))) := by
        have h_H := past_necessitation _ h_event_proj
        have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.right_mono_since (Formula.and alpha alpha') alpha (Formula.and beta beta')) trivial
        exact DerivationTree.modus_ponens [] _ _ h_ax h_H
      have h2 : DerivationTree FrameClass.Base [] ((Formula.snce alpha (Formula.and beta beta')).imp
          (Formula.snce alpha beta)) :=
        snce_left_mono_deriv (Formula.and beta beta') alpha beta h_guard_proj
      have h_snce_proj := imp_trans h1 h2
      have h_left := imp_trans (lce_imp (Formula.and beta beta') (Formula.snce (Formula.and alpha alpha') (Formula.and beta beta')))
        (rce_imp beta beta')
      have h_right := imp_trans (rce_imp (Formula.and beta beta') (Formula.snce (Formula.and alpha alpha') (Formula.and beta beta')))
        h_snce_proj
      have := DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.snce (Formula.and alpha alpha') (Formula.and beta beta')))] _ _
        (DerivationTree.modus_ponens [((Formula.and beta beta').and (Formula.snce (Formula.and alpha alpha') (Formula.and beta beta')))] _ _
          (DerivationTree.weakening [] [_] _ (pairing beta' (Formula.snce alpha beta)) (List.nil_subset _))
          (DerivationTree.modus_ponens [_] _ _
            (DerivationTree.weakening [] [_] _ h_left (List.nil_subset _))
            (DerivationTree.assumption _ _ (by simp))))
        (DerivationTree.modus_ponens [_] _ _
          (DerivationTree.weakening [] [_] _ h_right (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp)))
      exact deduction_theorem [] _ _ this
    have h_step1 := snce_left_mono_thm h_mcs_C h_guard_r h_sa
    have h_event_proj_r := rce_imp alpha alpha'
    exact right_mono_since_mcs h_mcs_C h_event_proj_r h_step1
  -- Until condition from burgessRSince_implies_burgessR
  have h_until_all : ∀ beta' ∈ B, ∀ gamma ∈ C,
      Formula.untl gamma (Formula.and beta' (Formula.snce alpha beta)) ∈ A := by
    intro beta' h_beta' gamma h_gamma
    have h_burgessRSince : burgessRSince C (Formula.and beta' (Formula.snce alpha beta)) A :=
      fun alpha' h_alpha' => h_since_all beta' h_beta' alpha' h_alpha'
    exact burgessRSince_implies_burgessR h_mcs_A h_mcs_C h_burgessRSince gamma h_gamma
  have h_r3_ext := dc_delta_B_burgessR3 h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-! ## Duality: h_content ↔ g_content -/

/-- h_content(B) ⊆ A implies g_content(A) ⊆ B for MCS A, B. -/
theorem h_content_sub_imp_g_content_sub' {A B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_B : Temporal.SetMaximalConsistent B)
    (h_hBA : h_content B ⊆ A) :
    g_content A ⊆ B := by
  intro ψ hψ
  by_contra h_not
  have h_neg_ψ : ψ.neg ∈ B := mcs_neg_of_not_mem h_mcs_B h_not
  have h_ax : DerivationTree FrameClass.Base [] (ψ.neg.imp (ψ.neg.some_future.all_past)) :=
    DerivationTree.axiom [] _ (Axiom.connect_past ψ.neg) trivial
  have h_HF : Formula.all_past (Formula.some_future ψ.neg) ∈ B :=
    temporal_implication_property h_mcs_B (theorem_in_mcs h_mcs_B h_ax) h_neg_ψ
  have h_F_neg_ψ_A : Formula.some_future ψ.neg ∈ A := h_hBA h_HF
  have h_G_nn : Formula.all_future ψ.neg.neg ∈ A := by
    have h_dni_ax := dni ψ
    have h_G_dni := theorem_in_mcs h_mcs_A (DerivationTree.temporal_necessitation _ h_dni_ax)
    have h_kd := temp_k_dist_derived ψ ψ.neg.neg
    have h1 := temporal_implication_property h_mcs_A (theorem_in_mcs h_mcs_A h_kd) h_G_dni
    exact temporal_implication_property h_mcs_A h1 hψ
  exact some_future_all_future_neg_absurd h_mcs_A ψ.neg h_F_neg_ψ_A h_G_nn

/-- g_content(A) ⊆ B implies h_content(B) ⊆ A for MCS A, B. -/
theorem g_content_sub_imp_h_content_sub' {A B : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_B : Temporal.SetMaximalConsistent B)
    (h_gAB : g_content A ⊆ B) :
    h_content B ⊆ A := by
  intro ψ hψ
  by_contra h_not
  have h_neg_ψ : ψ.neg ∈ A := mcs_neg_of_not_mem h_mcs_A h_not
  have h_GP : Formula.all_future (Formula.some_past ψ.neg) ∈ A :=
    connect_future_mcs' h_mcs_A ψ.neg h_neg_ψ
  have h_P_neg_ψ_B : Formula.some_past ψ.neg ∈ B := h_gAB h_GP
  have h_H_nn : Formula.all_past ψ.neg.neg ∈ B := by
    have h_dni_ax := dni ψ
    have h_H_dni := theorem_in_mcs h_mcs_B (past_necessitation _ h_dni_ax)
    have h_kd := past_k_dist ψ ψ.neg.neg
    have h1 := temporal_implication_property h_mcs_B (theorem_in_mcs h_mcs_B h_kd) h_H_dni
    exact temporal_implication_property h_mcs_B h1 hψ
  exact some_past_all_past_neg_absurd h_mcs_B ψ.neg h_P_neg_ψ_B h_H_nn

end Cslib.Logic.Temporal.Metalogic.Chronicle
