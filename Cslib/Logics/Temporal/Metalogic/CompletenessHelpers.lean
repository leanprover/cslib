/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.MCS
public import Cslib.Logics.Temporal.Metalogic.Soundness

/-! # Completeness Helpers for Temporal Logic BX

MCS helper lemmas needed by both the completeness theorem and the chronicle
canonical frame construction. Extracted from Completeness.lean to break the
circular import: Frame.lean -> Completeness.lean -> TruthLemma.lean -> ... -> Frame.lean.

## Main Results

- `mcs_g_trans`: G-transitivity in MCS
- `mcs_h_trans`: H-transitivity in MCS
- `past_of_future_subset`, `future_of_past_subset`: BX4/BX4' consequences
- `exists_future_successor`, `exists_past_predecessor`: Seriality witnesses
- `CanonicalWorld`, `canonicalAcc`: Canonical model types
- G/H truth lemma forward/reverse for canonical model
-/

set_option linter.style.setOption false
set_option maxHeartbeats 3200000

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## MCS Helper Lemmas -/

/-- ⊤ ∈ every MCS. -/
theorem mcs_top_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.top ∈ Ω := by
  apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
  unfold temporalDerivationSystem Temporal.Deriv
  exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩

/-- F(⊤) ∈ every MCS (from serial_future). -/
theorem mcs_f_top_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.someFuture Formula.top ∈ Ω :=
  mcs_mp_axiom h_mcs (mcs_top_mem h_mcs) .serial_future

/-- P(⊤) ∈ every MCS (from serial_past). -/
theorem mcs_p_top_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.somePast Formula.top ∈ Ω :=
  mcs_mp_axiom h_mcs (mcs_top_mem h_mcs) .serial_past

/-- G(⊥) ∉ any MCS. G(⊥) = ¬F(⊤) and F(⊤) ∈ Ω. -/
theorem mcs_g_bot_not_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.allFuture Formula.bot ∉ Ω := by
  intro h_g_bot
  exact mcs_bot_not_mem h_mcs (temporal_implication_property h_mcs h_g_bot (mcs_f_top_mem h_mcs))

/-- H(⊥) ∉ any MCS. H(⊥) = ¬P(⊤) and P(⊤) ∈ Ω. -/
theorem mcs_h_bot_not_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.allPast Formula.bot ∉ Ω := by
  intro h_h_bot
  exact mcs_bot_not_mem h_mcs (temporal_implication_property h_mcs h_h_bot (mcs_p_top_mem h_mcs))

/-- Derive double negation elimination: ⊢ ¬¬X → X. -/
noncomputable def deriveDne (X : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Formula.neg (Formula.neg X)).imp X) := by
  let ctx := [Formula.neg (Formula.neg X)]
  have d_peirce : DerivationTree FrameClass.Base ctx (((X.imp Formula.bot).imp X).imp X) :=
    .weakening [] ctx _ (.axiom [] _ (.peirce X Formula.bot) trivial) (fun _ h => nomatch h)
  let ctx2 := [X.imp Formula.bot, Formula.neg (Formula.neg X)]
  have d_bot : DerivationTree FrameClass.Base ctx2 Formula.bot :=
    .modus_ponens ctx2 (X.imp Formula.bot) Formula.bot
      (.assumption ctx2 (Formula.neg (Formula.neg X)) (by simp [List.mem_cons, ctx2]))
      (.assumption ctx2 (X.imp Formula.bot) (by simp [List.mem_cons, ctx2]))
  have d_efq : DerivationTree FrameClass.Base ctx2 X :=
    .modus_ponens ctx2 Formula.bot X
      (.weakening [] ctx2 _ (.axiom [] _ (.efq X) trivial) (fun _ h => nomatch h))
      d_bot
  have d_imp := deductionTheorem [Formula.neg (Formula.neg X)] (X.imp Formula.bot) X d_efq
  exact deductionTheorem [] (Formula.neg (Formula.neg X)) X
    (DerivationTree.modus_ponens ctx _ _ d_peirce d_imp)

/-- H-necessitation: from ⊢ φ derive ⊢ H(φ). -/
noncomputable def deriveHNec (φ : Formula Atom)
    (d : DerivationTree FrameClass.Base [] φ) :
    DerivationTree FrameClass.Base [] (Formula.allPast φ) := by
  have d_swap := DerivationTree.temporal_duality _ d
  have d_g_swap := DerivationTree.temporal_necessitation _ d_swap
  have d_h := DerivationTree.temporal_duality _ d_g_swap
  have h_eq : (Formula.allFuture φ.swapTemporal).swapTemporal =
      Formula.allPast (φ.swapTemporal.swapTemporal) := by
    simp only [Formula.allFuture, Formula.allPast, Formula.someFuture, Formula.somePast,
      Formula.neg, Formula.top, Formula.swapTemporal]
  rw [Formula.swapTemporal_involution] at h_eq
  exact h_eq ▸ d_h

/-- Derive ⊢ φ → ⊤ ∧ φ. -/
noncomputable def deriveAndTopIntro (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (Formula.and Formula.top φ)) := by
  let ctx := [Formula.imp Formula.top (Formula.neg φ), φ]
  have d_top : DerivationTree FrameClass.Base ctx Formula.top :=
    .weakening [] ctx _ (.axiom [] _ (.efq Formula.bot) trivial) (fun _ h => nomatch h)
  have d_neg_phi : DerivationTree FrameClass.Base ctx (Formula.neg φ) :=
    .modus_ponens ctx Formula.top (Formula.neg φ)
      (.assumption ctx _ (by simp [List.mem_cons, ctx]))
      d_top
  have d_bot : DerivationTree FrameClass.Base ctx Formula.bot :=
    .modus_ponens ctx φ Formula.bot d_neg_phi
      (.assumption ctx φ (by simp [List.mem_cons, ctx]))
  have d1 := deductionTheorem [φ] (Formula.imp Formula.top (Formula.neg φ)) Formula.bot d_bot
  exact deductionTheorem [] φ (Formula.and Formula.top φ) d1

/-- ¬¬X ∈ Ω ↔ X ∈ Ω in MCS. -/
theorem mcs_dne
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {X : Formula Atom} : Formula.neg (Formula.neg X) ∈ Ω ↔ X ∈ Ω := by
  constructor
  · intro h
    apply temporal_closed_under_derivation h_mcs (L := [Formula.neg (Formula.neg X)])
      (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.modus_ponens [Formula.neg (Formula.neg X)] _ X
      (.weakening [] [Formula.neg (Formula.neg X)] _
        (deriveDne X) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
  · intro h
    have h_neg_not : (¬X) ∉ Ω :=
      fun hn => mcs_bot_not_mem h_mcs (temporal_implication_property h_mcs hn h)
    exact mcs_neg_of_not_mem h_mcs h_neg_not

/-- F(F(ψ)) → F(ψ) in MCS (via BX6 + BX3). -/
theorem mcs_ff_imp_f
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {ψ : Formula Atom}
    (h_ff : Formula.someFuture (Formula.someFuture ψ) ∈ Ω) :
    (𝐅ψ) ∈ Ω := by
  let fψ := Formula.someFuture ψ
  have h_g_intro : Formula.allFuture (fψ.imp (Formula.and Formula.top fψ)) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.temporal_necessitation _ (deriveAndTopIntro fψ)⟩
  have h_bx3 : (Formula.someFuture fψ).imp
      (Formula.someFuture (Formula.and Formula.top fψ)) ∈ Ω :=
    mcs_mp_axiom h_mcs h_g_intro
      (.right_mono_until fψ (Formula.and Formula.top fψ) Formula.top)
  have h_f_and := temporal_implication_property h_mcs h_bx3 h_ff
  have h_absorb : (Formula.someFuture (Formula.and Formula.top fψ)).imp fψ ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.axiom [] _ (.absorb_until Formula.top ψ) trivial⟩
  exact temporal_implication_property h_mcs h_absorb h_f_and

/-- P(P(ψ)) → P(ψ) in MCS (via BX6' + BX3'). -/
theorem mcs_pp_imp_p
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {ψ : Formula Atom}
    (h_pp : Formula.somePast (Formula.somePast ψ) ∈ Ω) :
    (𝐏ψ) ∈ Ω := by
  let pψ := Formula.somePast ψ
  have h_h_intro : Formula.allPast (pψ.imp (Formula.and Formula.top pψ)) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨deriveHNec _ (deriveAndTopIntro pψ)⟩
  have h_bx3 : (Formula.somePast pψ).imp
      (Formula.somePast (Formula.and Formula.top pψ)) ∈ Ω :=
    mcs_mp_axiom h_mcs h_h_intro
      (.right_mono_since pψ (Formula.and Formula.top pψ) Formula.top)
  have h_p_and := temporal_implication_property h_mcs h_bx3 h_pp
  have h_absorb : (Formula.somePast (Formula.and Formula.top pψ)).imp pψ ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.axiom [] _ (.absorb_since Formula.top ψ) trivial⟩
  exact temporal_implication_property h_mcs h_absorb h_p_and

/-- G(ψ) → G(G(ψ)) in MCS (G-transitivity via F-idempotency). -/
theorem mcs_g_trans
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {ψ : Formula Atom}
    (h_g : (𝐆ψ) ∈ Ω) : Formula.allFuture (Formula.allFuture ψ) ∈ Ω := by
  by_contra h_not_gg
  let X := Formula.someFuture (Formula.neg ψ)
  have h_neg_gg : Formula.neg (Formula.allFuture (Formula.allFuture ψ)) ∈ Ω :=
    mcs_neg_of_not_mem h_mcs h_not_gg
  have h_f_neg_g : Formula.someFuture (Formula.neg (Formula.allFuture ψ)) ∈ Ω :=
    (mcs_dne h_mcs).mp h_neg_gg
  have h_g_dne : Formula.allFuture ((Formula.neg (Formula.neg X)).imp X) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.temporal_necessitation _ (deriveDne X)⟩
  have h_bx3 : (Formula.someFuture (Formula.neg (Formula.neg X))).imp
      (Formula.someFuture X) ∈ Ω :=
    mcs_mp_axiom h_mcs h_g_dne
      (.right_mono_until (Formula.neg (Formula.neg X)) X Formula.top)
  have h_ff := temporal_implication_property h_mcs h_bx3 h_f_neg_g
  exact mcs_not_mem_of_neg h_mcs h_g (mcs_ff_imp_f h_mcs h_ff)

/-- H(ψ) → H(H(ψ)) in MCS (H-transitivity via P-idempotency). -/
theorem mcs_h_trans
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {ψ : Formula Atom}
    (h_h : (𝐇ψ) ∈ Ω) : Formula.allPast (Formula.allPast ψ) ∈ Ω := by
  by_contra h_not_hh
  let X := Formula.somePast (Formula.neg ψ)
  have h_neg_hh : Formula.neg (Formula.allPast (Formula.allPast ψ)) ∈ Ω :=
    mcs_neg_of_not_mem h_mcs h_not_hh
  have h_p_neg_h : Formula.somePast (Formula.neg (Formula.allPast ψ)) ∈ Ω :=
    (mcs_dne h_mcs).mp h_neg_hh
  have h_h_dne : Formula.allPast ((Formula.neg (Formula.neg X)).imp X) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨deriveHNec _ (deriveDne X)⟩
  have h_bx3 : (Formula.somePast (Formula.neg (Formula.neg X))).imp
      (Formula.somePast X) ∈ Ω :=
    mcs_mp_axiom h_mcs h_h_dne
      (.right_mono_since (Formula.neg (Formula.neg X)) X Formula.top)
  have h_pp := temporal_implication_property h_mcs h_bx3 h_p_neg_h
  exact mcs_not_mem_of_neg h_mcs h_h (mcs_pp_imp_p h_mcs h_pp)

/-- If futureSet(Ω₁) ⊆ Ω₂, then pastSet(Ω₂) ⊆ Ω₁. Uses BX4. -/
theorem past_of_future_subset
    {Ω₁ Ω₂ : Set (Formula Atom)}
    (h_mcs₁ : Temporal.SetMaximalConsistent Ω₁)
    (h_mcs₂ : Temporal.SetMaximalConsistent Ω₂)
    (h_future : ∀ ψ, (𝐆ψ) ∈ Ω₁ → ψ ∈ Ω₂) :
    ∀ ψ, (𝐇ψ) ∈ Ω₂ → ψ ∈ Ω₁ := by
  intro ψ h_h
  by_contra h_not
  exact mcs_not_mem_of_neg h_mcs₂ h_h
    (h_future _ (mcs_mp_axiom h_mcs₁ (mcs_neg_of_not_mem h_mcs₁ h_not)
      (.connect_future (Formula.neg ψ))))

/-- If pastSet(Ω₁) ⊆ Ω₂, then futureSet(Ω₂) ⊆ Ω₁. Uses BX4'. -/
theorem future_of_past_subset
    {Ω₁ Ω₂ : Set (Formula Atom)}
    (h_mcs₁ : Temporal.SetMaximalConsistent Ω₁)
    (h_mcs₂ : Temporal.SetMaximalConsistent Ω₂)
    (h_past : ∀ ψ, (𝐇ψ) ∈ Ω₁ → ψ ∈ Ω₂) :
    ∀ ψ, (𝐆ψ) ∈ Ω₂ → ψ ∈ Ω₁ := by
  intro ψ h_g
  by_contra h_not
  exact mcs_not_mem_of_neg h_mcs₂ h_g
    (h_past _ (mcs_mp_axiom h_mcs₁ (mcs_neg_of_not_mem h_mcs₁ h_not)
      (.connect_past (Formula.neg ψ))))

/-! ## Canonical Model Infrastructure -/

/-- A canonical world is an MCS. -/
def CanonicalWorld (Atom : Type*) :=
  { Ω : Set (Formula Atom) // Temporal.SetMaximalConsistent Ω }

/-- Canonical accessibility: futureSet inclusion. -/
def canonicalAcc (W₁ W₂ : CanonicalWorld Atom) : Prop :=
  ∀ ψ, (𝐆ψ) ∈ W₁.val → ψ ∈ W₂.val

/-- Forward G-direction for truth lemma. -/
theorem truth_lemma_g_forward (W : CanonicalWorld Atom)
    {ψ : Formula Atom} (h_g : (𝐆ψ) ∈ W.val) :
    ∀ T : CanonicalWorld Atom, canonicalAcc W T → ψ ∈ T.val :=
  fun T hWT => hWT ψ h_g

/-- Reverse G-direction for truth lemma. -/
theorem truth_lemma_g_reverse (W : CanonicalWorld Atom)
    {ψ : Formula Atom}
    (h_all : ∀ T : CanonicalWorld Atom, canonicalAcc W T → ψ ∈ T.val) :
    (𝐆ψ) ∈ W.val := by
  by_contra h_not_g
  obtain ⟨T, hT_mcs, hT_future, hT_not⟩ := mcs_g_witness W.property h_not_g
  exact hT_not (h_all ⟨T, hT_mcs⟩ hT_future)

/-- Future successor exists for any MCS. -/
theorem exists_future_successor
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    ∃ Ω' : Set (Formula Atom), Temporal.SetMaximalConsistent Ω' ∧
      (∀ ψ, (𝐆ψ) ∈ Ω → ψ ∈ Ω') ∧
      (∀ ψ, (𝐇ψ) ∈ Ω' → ψ ∈ Ω) := by
  obtain ⟨T, hT_mcs, hT_future, _⟩ := mcs_g_witness h_mcs (mcs_g_bot_not_mem h_mcs)
  exact ⟨T, hT_mcs, hT_future, past_of_future_subset h_mcs hT_mcs hT_future⟩

/-- Past predecessor exists for any MCS. -/
theorem exists_past_predecessor
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    ∃ Ω' : Set (Formula Atom), Temporal.SetMaximalConsistent Ω' ∧
      (∀ ψ, (𝐇ψ) ∈ Ω → ψ ∈ Ω') ∧
      (∀ ψ, (𝐆ψ) ∈ Ω' → ψ ∈ Ω) := by
  obtain ⟨T, hT_mcs, hT_past, _⟩ := mcs_h_witness h_mcs (mcs_h_bot_not_mem h_mcs)
  exact ⟨T, hT_mcs, hT_past, future_of_past_subset h_mcs hT_mcs hT_past⟩

/-- Reverse H-direction for truth lemma. -/
theorem truth_lemma_h_reverse (W : CanonicalWorld Atom)
    {ψ : Formula Atom}
    (h_all : ∀ T : CanonicalWorld Atom, canonicalAcc T W → ψ ∈ T.val) :
    (𝐇ψ) ∈ W.val := by
  by_contra h_not_h
  obtain ⟨T, hT_mcs, hT_past, hT_not⟩ := mcs_h_witness W.property h_not_h
  exact hT_not (h_all ⟨T, hT_mcs⟩ (future_of_past_subset W.property hT_mcs hT_past))

end Cslib.Logic.Temporal
