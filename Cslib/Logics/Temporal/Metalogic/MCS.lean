/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.DeductionTheorem

/-! # Maximal Consistent Sets for Temporal Logic BX

This module instantiates the generic MCS framework for temporal logic BX and
proves temporal-specific MCS properties needed for the completeness theorem.

## Main Results

- `temporal_lindenbaum`: Every consistent set extends to an MCS.
- `temporal_closed_under_derivation`, `temporal_implication_property`,
  `temporal_negation_complete`: Generic MCS properties.
- `mcs_bot_not_mem`, `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`: Negation lemmas.
- `mcs_g_mp`: G-distribution: `G(φ→ψ) ∈ S` and `G(φ) ∈ S` imply `G(ψ) ∈ S`.
- `mcs_g_witness`: If `G(φ) ∉ S`, exists MCS T with `futureSet Ω ⊆ T` and `φ ∉ T`.
- `mcs_h_witness`: Symmetric for the past (H).

## References

* Cslib/Logics/Modal/Metalogic/MCS.lean — structural template
* Cslib/Foundations/Logic/Metalogic/Consistency.lean — generic MCS framework
-/

set_option linter.style.setOption false
set_option linter.dupNamespace false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Abbreviations -/

/-- Set consistency for the temporal derivation system. -/
abbrev Temporal.SetConsistent (Ω : Set (Formula Atom)) : Prop :=
  Metalogic.SetConsistent temporalDerivationSystem Ω

/-- Set maximal consistency for the temporal derivation system. -/
abbrev Temporal.SetMaximalConsistent (Ω : Set (Formula Atom)) : Prop :=
  Metalogic.SetMaximalConsistent temporalDerivationSystem Ω

/-! ## Generic MCS Properties -/

theorem temporal_lindenbaum {Ω : Set (Formula Atom)}
    (hS : Temporal.SetConsistent Ω) :
    ∃ M : Set (Formula Atom), Ω ⊆ M ∧ Temporal.SetMaximalConsistent M :=
  Metalogic.set_lindenbaum temporalDerivationSystem hS

theorem temporal_closed_under_derivation
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {L : List (Formula Atom)} (h_sub : ∀ ψ ∈ L, ψ ∈ Ω)
    {φ : Formula Atom} (h_deriv : temporalDerivationSystem.Deriv L φ) : φ ∈ Ω :=
  Metalogic.SetMaximalConsistent.closed_under_derivation
    temporalDerivationSystem temporal_has_deduction_theorem h_mcs h_sub h_deriv

theorem temporal_implication_property
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ ψ : Formula Atom} (h_imp : Formula.imp φ ψ ∈ Ω) (h_phi : φ ∈ Ω) : ψ ∈ Ω :=
  Metalogic.SetMaximalConsistent.implication_property
    temporalDerivationSystem temporal_has_deduction_theorem h_mcs h_imp h_phi

theorem temporal_negation_complete
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    (φ : Formula Atom) : φ ∈ Ω ∨ (¬φ) ∈ Ω :=
  Metalogic.SetMaximalConsistent.negation_complete
    temporalDerivationSystem temporal_has_deduction_theorem h_mcs φ

/--
Theorems (formulas derivable from empty context) belong to every Temporal MCS.

This is the key convenience wrapper around `temporal_closed_under_derivation` with an empty
context list, used throughout the Temporal metalogic modules.
-/
noncomputable def theoremInMcs {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (h_deriv : DerivationTree FrameClass.Base [] phi) : phi ∈ M :=
  temporal_closed_under_derivation h_mcs (L := []) (fun _ h => by simp at h) ⟨h_deriv⟩

/-! ## Basic MCS Properties -/

theorem mcs_mp_axiom
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ ψ : Formula Atom} (h_mem : φ ∈ Ω) (h_ax : Axiom (φ.imp ψ))
    (h_fc : h_ax.minFrameClass ≤ .Base := by trivial) : ψ ∈ Ω := by
  apply temporal_closed_under_derivation h_mcs (L := [φ]) (fun x hx => by
    simp [List.mem_cons] at hx; exact hx ▸ h_mem)
  unfold temporalDerivationSystem Temporal.Deriv
  exact ⟨.modus_ponens [φ] φ ψ
    (.weakening [] [φ] (φ.imp ψ) (.axiom [] _ h_ax h_fc) (fun _ h => nomatch h))
    (.assumption [φ] φ (List.mem_cons.mpr (Or.inl rfl)))⟩

theorem mcs_bot_not_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.bot ∉ Ω := by
  intro h_bot
  exact h_mcs.1 [Formula.bot]
    (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h_bot)
    (by simp [temporalDerivationSystem, Temporal.Deriv]
        exact ⟨.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))⟩)

theorem mcs_neg_of_not_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ : Formula Atom} (h_not : φ ∉ Ω) : (¬φ) ∈ Ω := by
  rcases temporal_negation_complete h_mcs φ with h | h
  · exact absurd h h_not
  · exact h

theorem mcs_not_mem_of_neg
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ : Formula Atom} (h_neg : (¬φ) ∈ Ω) : φ ∉ Ω := by
  intro h_phi
  exact mcs_bot_not_mem h_mcs (temporal_implication_property h_mcs h_neg h_phi)

theorem mcs_mem_iff_neg_not_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ : Formula Atom} : φ ∈ Ω ↔ (¬φ) ∉ Ω := by
  constructor
  · intro h hn; exact mcs_bot_not_mem h_mcs (temporal_implication_property h_mcs hn h)
  · intro h; rcases temporal_negation_complete h_mcs φ with h' | h'
    · exact h'
    · exact absurd h' h

/-! ## G-distribution (key lemma) -/

/-- Build a DerivationTree for the contrapositive: `⊢ (A→B)→(¬B→¬A)`. -/
noncomputable def deriveContrapositive (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) := by
  -- Context: [A→B, ¬B, A] ⊢ ⊥
  -- Then DT three times to get ⊢ (A→B)→¬B→¬A = (A→B)→(B→⊥)→(A→⊥).
  let ctx := [A, Formula.neg B, A.imp B]
  have d_B : DerivationTree FrameClass.Base ctx B :=
    .modus_ponens ctx A B
      (.assumption ctx (A.imp B) (by simp [List.mem_cons, ctx]))
      (.assumption ctx A (by simp [List.mem_cons, ctx]))
  have d_bot : DerivationTree FrameClass.Base ctx Formula.bot :=
    .modus_ponens ctx B Formula.bot
      (.assumption ctx (Formula.neg B) (by simp [List.mem_cons, ctx]))
      d_B
  -- DT on A: [¬B, A→B] ⊢ A→⊥ = ¬A
  have d1 := deductionTheorem [Formula.neg B, A.imp B] A Formula.bot d_bot
  -- DT on ¬B: [A→B] ⊢ ¬B→¬A
  have d2 := deductionTheorem [A.imp B] (Formula.neg B) (Formula.neg A) d1
  -- DT on A→B: [] ⊢ (A→B)→(¬B→¬A)
  exact deductionTheorem [] (A.imp B) (B.neg.imp A.neg) d2

/-- `G(φ→ψ) ∈ S` and `G(φ) ∈ S` imply `G(ψ) ∈ S`.

By contradiction: assume `F(¬ψ) ∈ S`. From `⊢ ¬(¬ψ→¬φ) → ¬(φ→ψ)` (derivable) and
necessitation, BX3 gives `G(φ→ψ) → G(¬ψ→¬φ)` at MCS level.
Then BX3 on `G(¬ψ→¬φ) → F(¬ψ) → F(¬φ)` yields `F(¬φ) ∈ S`, contradicting `G(φ) ∈ S`. -/
theorem mcs_g_mp
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ ψ : Formula Atom}
    (h_g_imp : Formula.allFuture (φ.imp ψ) ∈ Ω)
    (h_g_phi : (𝐆φ) ∈ Ω) : (𝐆ψ) ∈ Ω := by
  -- Assume G(ψ) ∉ Ω, giving F(¬ψ) ∈ Ω
  by_contra h_not_g_psi
  have h_f_neg_psi : Formula.someFuture (Formula.neg ψ) ∈ Ω :=
    (mcs_mem_iff_neg_not_mem h_mcs).mpr h_not_g_psi
  -- Derive ⊢ (φ→ψ) → (¬ψ → ¬φ) (contrapositive)
  have d_contra := deriveContrapositive φ ψ
  -- Necessitation: ⊢ G((φ→ψ) → (¬ψ → ¬φ))
  have h_g_contra : Formula.allFuture ((φ.imp ψ).imp (ψ.neg.imp φ.neg)) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.temporal_necessitation _ d_contra⟩
  -- Key: derive ⊢ ¬(¬ψ→¬φ) → ¬(φ→ψ) to get G(φ→ψ) → G(¬ψ→¬φ) at MCS level
  have d_neg_equiv : DerivationTree FrameClass.Base []
      ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) := by
    let ctx := [φ.imp ψ, (ψ.neg.imp φ.neg).neg]
    have d_contra_w : DerivationTree FrameClass.Base ctx (ψ.neg.imp φ.neg) :=
      .modus_ponens ctx (φ.imp ψ) (ψ.neg.imp φ.neg)
        (.weakening [] ctx _ (deriveContrapositive φ ψ) (fun _ h => nomatch h))
        (.assumption ctx (φ.imp ψ) (by simp [List.mem_cons, ctx]))
    have d_bot : DerivationTree FrameClass.Base ctx Formula.bot :=
      .modus_ponens ctx (ψ.neg.imp φ.neg) Formula.bot
        (.assumption ctx (ψ.neg.imp φ.neg).neg (by simp [List.mem_cons, ctx]))
        d_contra_w
    have d1 := deductionTheorem [(ψ.neg.imp φ.neg).neg] (φ.imp ψ) Formula.bot d_bot
    exact deductionTheorem [] (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg d1
  -- Necessitation: ⊢ G(¬(¬ψ→¬φ) → ¬(φ→ψ))
  have h_g_neg_equiv_S :
      Formula.allFuture ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.temporal_necessitation _ d_neg_equiv⟩
  -- BX3 (right_mono_until) with α = ¬(¬ψ→¬φ), β = ¬(φ→ψ), χ = ⊤:
  -- G(¬(¬ψ→¬φ)→¬(φ→ψ)) → (¬(¬ψ→¬φ) U ⊤ → ¬(φ→ψ) U ⊤)
  -- = G(...) → F(¬(¬ψ→¬φ)) → F(¬(φ→ψ))
  -- So G(...) ∈ Ω → (F(¬(¬ψ→¬φ)) → F(¬(φ→ψ))) ∈ S.
  -- BX3 axiom instance:
  -- right_mono_until (¬(¬ψ→¬φ)) (¬(φ→ψ)) ⊤
  -- gives: G(¬(¬ψ→¬φ)→¬(φ→ψ)) → (¬(¬ψ→¬φ) U ⊤ → ¬(φ→ψ) U ⊤)
  have h_bx3_imp : Formula.imp (Formula.someFuture (ψ.neg.imp φ.neg).neg)
      (Formula.someFuture (φ.imp ψ).neg) ∈ Ω :=
    mcs_mp_axiom h_mcs h_g_neg_equiv_S
      (.right_mono_until (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top)
  -- G(φ→ψ) → G(¬ψ→¬φ): if G(¬ψ→¬φ) ∉ S, then F(¬(¬ψ→¬φ)) ∈ S, then F(¬(φ→ψ)) ∈ S
  -- via h_bx3_imp; but G(φ→ψ) ∈ S. Contradiction.
  have h_g_contra_psi_phi : Formula.allFuture (ψ.neg.imp φ.neg) ∈ Ω := by
    by_contra h_not
    exact mcs_not_mem_of_neg h_mcs h_g_imp
      (temporal_implication_property h_mcs h_bx3_imp ((mcs_mem_iff_neg_not_mem h_mcs).mpr h_not))
  -- BX3: G(¬ψ→¬φ) → F(¬ψ) → F(¬φ). We have both antecedents; F(¬φ) contradicts G(φ) ∈ S.
  exact mcs_not_mem_of_neg h_mcs h_g_phi
    (temporal_implication_property h_mcs
      (mcs_mp_axiom h_mcs h_g_contra_psi_phi (.right_mono_until ψ.neg φ.neg Formula.top))
      h_f_neg_psi)

/-- Symmetric version for H (allPast). -/
theorem mcs_h_mp
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ ψ : Formula Atom}
    (h_h_imp : Formula.allPast (φ.imp ψ) ∈ Ω)
    (h_h_phi : (𝐇φ) ∈ Ω) : (𝐇ψ) ∈ Ω := by
  -- Same structure as mcs_g_mp but using BX3' (right_mono_since) and temporal_duality.
  by_contra h_not_h_psi
  have h_p_neg_psi : Formula.somePast (Formula.neg ψ) ∈ Ω :=
    (mcs_mem_iff_neg_not_mem h_mcs).mpr h_not_h_psi
  -- Derive ¬(¬ψ→¬φ) → ¬(φ→ψ) same as before
  have d_neg_equiv : DerivationTree FrameClass.Base []
      ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) := by
    let ctx := [φ.imp ψ, (ψ.neg.imp φ.neg).neg]
    have d_contra_w : DerivationTree FrameClass.Base ctx (ψ.neg.imp φ.neg) :=
      .modus_ponens ctx (φ.imp ψ) (ψ.neg.imp φ.neg)
        (.weakening [] ctx _ (deriveContrapositive φ ψ) (fun _ h => nomatch h))
        (.assumption ctx (φ.imp ψ) (by simp [List.mem_cons, ctx]))
    have d_bot : DerivationTree FrameClass.Base ctx Formula.bot :=
      .modus_ponens ctx (ψ.neg.imp φ.neg) Formula.bot
        (.assumption ctx (ψ.neg.imp φ.neg).neg (by simp [List.mem_cons, ctx]))
        d_contra_w
    have d1 := deductionTheorem [(ψ.neg.imp φ.neg).neg] (φ.imp ψ) Formula.bot d_bot
    exact deductionTheorem [] (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg d1
  -- Use double-swap: duality(d_neg_equiv) gives ⊢ swap(X); necessitation gives ⊢ G(swap(X));
  -- duality again gives ⊢ swap(G(swap(X))) = H(swap(swap(X))) = H(X) by involution.
  have h_h_neg_equiv_S :
      Formula.allPast ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    let X := (ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg
    have d_swap_X := DerivationTree.temporal_duality X d_neg_equiv
    have d_g_swap := DerivationTree.temporal_necessitation _ d_swap_X
    have d_h_swap2 := DerivationTree.temporal_duality _ d_g_swap
    have h_eq : (Formula.allFuture X.swapTemporal).swapTemporal =
        Formula.allPast (X.swapTemporal.swapTemporal) := by
      simp only [Formula.allFuture, Formula.allPast, Formula.someFuture, Formula.somePast,
        Formula.neg, Formula.top, Formula.swapTemporal]
    rw [Formula.swapTemporal_involution] at h_eq
    exact ⟨h_eq ▸ d_h_swap2⟩
  -- BX3' (right_mono_since): H(α→β) → P(α) → P(β)
  have h_bx3_imp : Formula.imp (Formula.somePast (ψ.neg.imp φ.neg).neg)
      (Formula.somePast (φ.imp ψ).neg) ∈ Ω :=
    mcs_mp_axiom h_mcs h_h_neg_equiv_S
      (.right_mono_since (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top)
  have h_h_contra : Formula.allPast (ψ.neg.imp φ.neg) ∈ Ω := by
    by_contra h_not
    have h_p := (mcs_mem_iff_neg_not_mem h_mcs).mpr h_not
    have h_p2 := temporal_implication_property h_mcs h_bx3_imp h_p
    exact mcs_not_mem_of_neg h_mcs h_h_imp h_p2
  have h_bx3_2 : Formula.imp (Formula.somePast ψ.neg) (Formula.somePast φ.neg) ∈ Ω :=
    mcs_mp_axiom h_mcs h_h_contra
      (.right_mono_since ψ.neg φ.neg Formula.top)
  have h_p_neg_phi := temporal_implication_property h_mcs h_bx3_2 h_p_neg_psi
  exact mcs_not_mem_of_neg h_mcs h_h_phi h_p_neg_phi

/-! ## G-witness and H-witness -/

/-- The "future set" of an MCS: all formulas whose G-closure is in Ω. -/
def futureSet (Ω : Set (Formula Atom)) : Set (Formula Atom) :=
  {φ | (𝐆φ) ∈ Ω}

/-- The "past set" of an MCS: all formulas whose H-closure is in Ω. -/
def pastSet (Ω : Set (Formula Atom)) : Set (Formula Atom) :=
  {φ | (𝐇φ) ∈ Ω}

/-- Derive ⊥ from G-context: if all G(lᵢ) ∈ S and L ⊢ ⊥, then S is inconsistent
via iterated G-distribution.

The proof repeatedly applies mcs_g_mp: from G(l₁→l₂→...→⊥) (via necessitation of
the iterated deduction theorem result) and G(l₁) ∈ S, derive G(l₂→...→⊥) ∈ S, etc.
The final step gives G(⊥) ∈ S, i.e., ¬F(⊤) ∈ S. But serial_future gives F(⊤) ∈ S.
Contradiction. -/
theorem derive_g_contradiction
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {L : List (Formula Atom)} {φ : Formula Atom}
    (hL : ∀ x ∈ L, (𝐆x) ∈ Ω)
    (d : DerivationTree FrameClass.Base L φ) : (𝐆φ) ∈ Ω := by
  induction L generalizing φ with
  | nil =>
    -- L = [], d : [] ⊢ φ. Necessitation: ⊢ G(φ). So G(φ) ∈ S.
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.temporal_necessitation _ d⟩
  | cons a L' ih =>
    have dt := deductionTheorem L' a φ d
    have h_g_imp := ih (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) dt
    exact mcs_g_mp h_mcs h_g_imp (hL a (List.mem_cons.mpr (Or.inl rfl)))

/-- If `G(φ) ∉ S`, then there exists an MCS `T` with `futureSet Ω ⊆ T` and `φ ∉ T`. -/
theorem mcs_g_witness
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ : Formula Atom} (h_not_g : (𝐆φ) ∉ Ω) :
    ∃ T : Set (Formula Atom), Temporal.SetMaximalConsistent T ∧
      (∀ ψ, (𝐆ψ) ∈ Ω → ψ ∈ T) ∧ φ ∉ T := by
  let W := futureSet Ω ∪ {Formula.neg φ}
  have hW : Temporal.SetConsistent W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    -- Separate L into elements with G-versions in Ω and possibly ¬φ.
    let L' := L.filter (· ≠ Formula.neg φ)
    have h_L'_g : ∀ x ∈ L', (𝐆x) ∈ Ω := by
      intro x hx
      simp only [L', List.mem_filter, decide_eq_true_eq] at hx
      rcases hL x hx.1 with h | h
      · exact h
      · exact absurd h hx.2
    by_cases h_neg_in : (¬φ) ∈ L
    · -- ¬φ ∈ L. Weaken, DT, then Peirce+EFQ derive φ; derive_g_contradiction gives G(φ) ∈ S.
      have h_perm : ∀ x, x ∈ L → x ∈ Formula.neg φ :: L' := by
        intro x hx
        by_cases hxn : x = Formula.neg φ
        · exact List.mem_cons.mpr (Or.inl hxn)
        · exact List.mem_cons.mpr (Or.inr (by
            simp only [L', List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
      have d_reord := DerivationTree.weakening L (Formula.neg φ :: L') Formula.bot
        d_bot h_perm
      have d_dne := deductionTheorem L' (Formula.neg φ) Formula.bot d_reord
      let neg_phi := Formula.neg φ
      have efq : DerivationTree FrameClass.Base L' (Formula.bot.imp φ) :=
        .weakening [] L' _ (.axiom [] _ (.efq φ) trivial) (fun _ h => nomatch h)
      have ik : DerivationTree FrameClass.Base L'
          ((Formula.bot.imp φ).imp (neg_phi.imp (Formula.bot.imp φ))) :=
        .weakening [] L' _ (.axiom [] _ (.imp_s (Formula.bot.imp φ) neg_phi) trivial)
          (fun _ h => nomatch h)
      have step_k := DerivationTree.modus_ponens L' _ _ ik efq
      have is_ax : DerivationTree FrameClass.Base L'
          ((neg_phi.imp (Formula.bot.imp φ)).imp
           ((neg_phi.imp Formula.bot).imp (neg_phi.imp φ))) :=
        .weakening [] L' _ (.axiom [] _ (.imp_k neg_phi Formula.bot φ) trivial)
          (fun _ h => nomatch h)
      have step_s := DerivationTree.modus_ponens L' _ _ is_ax step_k
      have step3 := DerivationTree.modus_ponens L' _ _ step_s d_dne
      have peirce_ax : DerivationTree FrameClass.Base L'
          (((φ.imp Formula.bot).imp φ).imp φ) :=
        .weakening [] L' _ (.axiom [] _ (.peirce φ Formula.bot) trivial)
          (fun _ h => nomatch h)
      exact h_not_g (derive_g_contradiction h_mcs h_L'_g
        (DerivationTree.modus_ponens L' _ _ peirce_ax step3))
    · -- ¬φ ∉ L. All elements have G-versions in Ω; derive_g_contradiction gives G(⊥) ∈ S.
      have h_all_g : ∀ x ∈ L, (𝐆x) ∈ Ω := by
        intro x hx
        rcases hL x hx with h | h
        · exact h
        · exact absurd (h ▸ hx) h_neg_in
      have h_g_bot := derive_g_contradiction h_mcs h_all_g d_bot
      -- G(⊥) = ¬F(⊤). serial_future gives F(⊤) ∈ S. Contradiction.
      have h_top : Formula.top ∈ Ω := by
        apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
        unfold temporalDerivationSystem Temporal.Deriv
        exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
      exact mcs_not_mem_of_neg h_mcs h_g_bot (mcs_mp_axiom h_mcs h_top .serial_future)
  obtain ⟨T, hWT, hT_mcs⟩ := temporal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · intro ψ h_g; exact hWT (Set.mem_union_left _ h_g)
  · have h_neg : (¬φ) ∈ T := hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg hT_mcs h_neg

/-- Symmetric version for past: if `H(φ) ∉ S`, exists MCS T with pastSet Ω ⊆ T and φ ∉ T. -/
theorem derive_h_contradiction
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {L : List (Formula Atom)} {φ : Formula Atom}
    (hL : ∀ x ∈ L, (𝐇x) ∈ Ω)
    (d : DerivationTree FrameClass.Base L φ) : (𝐇φ) ∈ Ω := by
  induction L generalizing φ with
  | nil =>
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    have d_g := DerivationTree.temporal_necessitation _ d
    have d_swap := DerivationTree.temporal_duality _ d_g
    have h_eq : (Formula.allFuture φ).swapTemporal = Formula.allPast φ.swapTemporal := by
      simp only [Formula.allFuture, Formula.allPast, Formula.someFuture, Formula.somePast,
        Formula.neg, Formula.top, Formula.swapTemporal]
    -- Double-swap: duality(d) gives ⊢ swap(φ); necessitation; duality gives H(φ) by involution.
    have d_swap_phi := DerivationTree.temporal_duality φ d
    have d_g_swap := DerivationTree.temporal_necessitation _ d_swap_phi
    have d_h := DerivationTree.temporal_duality _ d_g_swap
    have h_eq2 : (Formula.allFuture φ.swapTemporal).swapTemporal =
        Formula.allPast (φ.swapTemporal.swapTemporal) := by
      simp only [Formula.allFuture, Formula.allPast, Formula.someFuture, Formula.somePast,
        Formula.neg, Formula.top, Formula.swapTemporal]
    rw [Formula.swapTemporal_involution] at h_eq2
    exact ⟨h_eq2 ▸ d_h⟩
  | cons a L' ih =>
    have dt := deductionTheorem L' a φ d
    have h_h_imp := ih (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) dt
    have h_h_a := hL a (List.mem_cons.mpr (Or.inl rfl))
    exact mcs_h_mp h_mcs h_h_imp h_h_a

theorem mcs_h_witness
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ : Formula Atom} (h_not_h : (𝐇φ) ∉ Ω) :
    ∃ T : Set (Formula Atom), Temporal.SetMaximalConsistent T ∧
      (∀ ψ, (𝐇ψ) ∈ Ω → ψ ∈ T) ∧ φ ∉ T := by
  let W := pastSet Ω ∪ {Formula.neg φ}
  have hW : Temporal.SetConsistent W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    let L' := L.filter (· ≠ Formula.neg φ)
    have h_L'_h : ∀ x ∈ L', (𝐇x) ∈ Ω := by
      intro x hx
      simp only [L', List.mem_filter, decide_eq_true_eq] at hx
      rcases hL x hx.1 with h | h
      · exact h
      · exact absurd h hx.2
    by_cases h_neg_in : (¬φ) ∈ L
    · have h_perm : ∀ x, x ∈ L → x ∈ Formula.neg φ :: L' := by
        intro x hx
        by_cases hxn : x = Formula.neg φ
        · exact List.mem_cons.mpr (Or.inl hxn)
        · exact List.mem_cons.mpr (Or.inr (by
            simp only [L', List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
      have d_reord := DerivationTree.weakening L (Formula.neg φ :: L') Formula.bot
        d_bot h_perm
      have d_dne := deductionTheorem L' (Formula.neg φ) Formula.bot d_reord
      let neg_phi := Formula.neg φ
      have efq : DerivationTree FrameClass.Base L' (Formula.bot.imp φ) :=
        .weakening [] L' _ (.axiom [] _ (.efq φ) trivial) (fun _ h => nomatch h)
      have ik : DerivationTree FrameClass.Base L'
          ((Formula.bot.imp φ).imp (neg_phi.imp (Formula.bot.imp φ))) :=
        .weakening [] L' _ (.axiom [] _ (.imp_s (Formula.bot.imp φ) neg_phi) trivial)
          (fun _ h => nomatch h)
      have step_k := DerivationTree.modus_ponens L' _ _ ik efq
      have is_ax : DerivationTree FrameClass.Base L'
          ((neg_phi.imp (Formula.bot.imp φ)).imp
           ((neg_phi.imp Formula.bot).imp (neg_phi.imp φ))) :=
        .weakening [] L' _ (.axiom [] _ (.imp_k neg_phi Formula.bot φ) trivial)
          (fun _ h => nomatch h)
      have step_s := DerivationTree.modus_ponens L' _ _ is_ax step_k
      have step3 := DerivationTree.modus_ponens L' _ _ step_s d_dne
      have peirce_ax : DerivationTree FrameClass.Base L'
          (((φ.imp Formula.bot).imp φ).imp φ) :=
        .weakening [] L' _ (.axiom [] _ (.peirce φ Formula.bot) trivial)
          (fun _ h => nomatch h)
      have d_phi := DerivationTree.modus_ponens L' _ _ peirce_ax step3
      exact h_not_h (derive_h_contradiction h_mcs h_L'_h d_phi)
    · have h_all_h : ∀ x ∈ L, (𝐇x) ∈ Ω := by
        intro x hx
        rcases hL x hx with h | h
        · exact h
        · exact absurd (h ▸ hx) h_neg_in
      have h_h_bot := derive_h_contradiction h_mcs h_all_h d_bot
      have h_top : Formula.top ∈ Ω := by
        apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
        unfold temporalDerivationSystem Temporal.Deriv
        exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
      have h_p_top : Formula.somePast Formula.top ∈ Ω :=
        mcs_mp_axiom h_mcs h_top .serial_past
      exact mcs_not_mem_of_neg h_mcs h_h_bot h_p_top
  obtain ⟨T, hWT, hT_mcs⟩ := temporal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · intro ψ h_h; exact hWT (Set.mem_union_left _ h_h)
  · have h_neg : (¬φ) ∈ T := hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg hT_mcs h_neg

end Cslib.Logic.Temporal
