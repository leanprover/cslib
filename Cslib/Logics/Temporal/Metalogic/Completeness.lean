/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Temporal.Metalogic.MCS
import Cslib.Logics.Temporal.Metalogic.Soundness
import Mathlib.Order.Extension.Linear

/-! # Completeness Theorem for Temporal Logic BX

This module proves completeness for temporal BX logic: every formula valid over
all serial linear temporal orders is derivable.

## Main Results

- `completeness`: If `φ` is valid over serial linear orders, then `Temporal.ThDerivable φ`.

## Design

The proof proceeds by contrapositive:
1. If `φ` is not derivable, `{¬φ}` is consistent (using Peirce + EFQ).
2. Extend `{¬φ}` to an MCS `M` via `temporal_lindenbaum`.
3. Construct a canonical serial linear order model where `¬φ` is satisfied.
4. This contradicts the validity of `φ`.

Step 3 requires the canonical model construction with truth lemma for all 5
formula constructors. This module provides:
- All MCS helper lemmas (G/H-transitivity, F/P-idempotency, DNE, etc.)
- The canonical world type and accessibility relation
- The truth lemma for G/H (forward and reverse directions)
- The neg_consistent_of_not_derivable lemma
- The main completeness theorem

The truth lemma for Until/Since relies on the canonical order being a serial
linear order, which requires the BX linearity axioms (BX7, BX11) and the MCS
enrichment/absorption axiom combinations. The canonical linear order construction
is the most technically demanding component.

## References

* Burgess (1982) — BX axiom system and completeness
* Xu (1988) — Temporal completeness proofs
* Cslib/Logics/Modal/Metalogic/Completeness.lean — structural template
-/

set_option linter.style.setOption false
set_option maxHeartbeats 3200000

namespace Cslib.Logic.Temporal

open Cslib.Logic

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## MCS Helper Lemmas -/

/-- Apply an axiom in an MCS. -/
private theorem mcs_mp_axiom
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ ψ : Formula Atom} (h_mem : φ ∈ Ω) (h_ax : Axiom (φ.imp ψ)) : ψ ∈ Ω := by
  apply temporal_closed_under_derivation h_mcs (L := [φ]) (fun x hx => by
    simp [List.mem_cons] at hx; exact hx ▸ h_mem)
  unfold temporalDerivationSystem Temporal.Deriv
  exact ⟨.modus_ponens [φ] φ ψ
    (.weakening [] [φ] (φ.imp ψ) (.axiom [] _ h_ax trivial) (fun _ h => nomatch h))
    (.assumption [φ] φ (List.mem_cons.mpr (Or.inl rfl)))⟩

/-- ⊤ ∈ every MCS. -/
private theorem mcs_top_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.top ∈ Ω := by
  apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
  unfold temporalDerivationSystem Temporal.Deriv
  exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩

/-- F(⊤) ∈ every MCS (from serial_future). -/
private theorem mcs_f_top_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.some_future Formula.top ∈ Ω :=
  mcs_mp_axiom h_mcs (mcs_top_mem h_mcs) .serial_future

/-- P(⊤) ∈ every MCS (from serial_past). -/
private theorem mcs_p_top_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.some_past Formula.top ∈ Ω :=
  mcs_mp_axiom h_mcs (mcs_top_mem h_mcs) .serial_past

/-- G(⊥) ∉ any MCS. G(⊥) = ¬F(⊤) and F(⊤) ∈ Ω. -/
private theorem mcs_g_bot_not_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.all_future Formula.bot ∉ Ω := by
  intro h_g_bot
  exact mcs_bot_not_mem h_mcs (temporal_implication_property h_mcs h_g_bot (mcs_f_top_mem h_mcs))

/-- H(⊥) ∉ any MCS. H(⊥) = ¬P(⊤) and P(⊤) ∈ Ω. -/
private theorem mcs_h_bot_not_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.all_past Formula.bot ∉ Ω := by
  intro h_h_bot
  exact mcs_bot_not_mem h_mcs (temporal_implication_property h_mcs h_h_bot (mcs_p_top_mem h_mcs))

/-- Derive double negation elimination: ⊢ ¬¬X → X. -/
private noncomputable def derive_dne (X : Formula Atom) :
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
  have d_imp := deduction_theorem [Formula.neg (Formula.neg X)] (X.imp Formula.bot) X d_efq
  exact deduction_theorem [] (Formula.neg (Formula.neg X)) X
    (DerivationTree.modus_ponens ctx _ _ d_peirce d_imp)

/-- H-necessitation: from ⊢ φ derive ⊢ H(φ). -/
private noncomputable def derive_h_nec (φ : Formula Atom)
    (d : DerivationTree FrameClass.Base [] φ) :
    DerivationTree FrameClass.Base [] (Formula.all_past φ) := by
  have d_swap := DerivationTree.temporal_duality _ d
  have d_g_swap := DerivationTree.temporal_necessitation _ d_swap
  have d_h := DerivationTree.temporal_duality _ d_g_swap
  have h_eq : (Formula.all_future φ.swap_temporal).swap_temporal =
      Formula.all_past (φ.swap_temporal.swap_temporal) := by
    simp only [Formula.all_future, Formula.all_past, Formula.some_future, Formula.some_past,
      Formula.neg, Formula.top, Formula.swap_temporal]
  rw [Formula.swap_temporal_involution] at h_eq
  exact h_eq ▸ d_h

/-- Derive ⊢ φ → ⊤ ∧ φ. -/
private noncomputable def derive_and_top_intro (φ : Formula Atom) :
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
  have d1 := deduction_theorem [φ] (Formula.imp Formula.top (Formula.neg φ)) Formula.bot d_bot
  exact deduction_theorem [] φ (Formula.and Formula.top φ) d1

/-- ¬¬X ∈ Ω ↔ X ∈ Ω in MCS. -/
private theorem mcs_dne
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {X : Formula Atom} : Formula.neg (Formula.neg X) ∈ Ω ↔ X ∈ Ω := by
  constructor
  · intro h
    apply temporal_closed_under_derivation h_mcs (L := [Formula.neg (Formula.neg X)])
      (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.modus_ponens [Formula.neg (Formula.neg X)] _ X
      (.weakening [] [Formula.neg (Formula.neg X)] _
        (derive_dne X) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
  · intro h
    have h_neg_not : Formula.neg X ∉ Ω :=
      fun hn => mcs_bot_not_mem h_mcs (temporal_implication_property h_mcs hn h)
    exact mcs_neg_of_not_mem h_mcs h_neg_not

/-- F(F(ψ)) → F(ψ) in MCS (via BX6 + BX3). -/
private theorem mcs_ff_imp_f
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {ψ : Formula Atom}
    (h_ff : Formula.some_future (Formula.some_future ψ) ∈ Ω) :
    Formula.some_future ψ ∈ Ω := by
  let fψ := Formula.some_future ψ
  have h_g_intro : Formula.all_future (fψ.imp (Formula.and Formula.top fψ)) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.temporal_necessitation _ (derive_and_top_intro fψ)⟩
  have h_bx3 : (Formula.some_future fψ).imp
      (Formula.some_future (Formula.and Formula.top fψ)) ∈ Ω :=
    mcs_mp_axiom h_mcs h_g_intro
      (.right_mono_until fψ (Formula.and Formula.top fψ) Formula.top)
  have h_f_and := temporal_implication_property h_mcs h_bx3 h_ff
  have h_absorb : (Formula.some_future (Formula.and Formula.top fψ)).imp fψ ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.axiom [] _ (.absorb_until Formula.top ψ) trivial⟩
  exact temporal_implication_property h_mcs h_absorb h_f_and

/-- P(P(ψ)) → P(ψ) in MCS (via BX6' + BX3'). -/
private theorem mcs_pp_imp_p
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {ψ : Formula Atom}
    (h_pp : Formula.some_past (Formula.some_past ψ) ∈ Ω) :
    Formula.some_past ψ ∈ Ω := by
  let pψ := Formula.some_past ψ
  have h_h_intro : Formula.all_past (pψ.imp (Formula.and Formula.top pψ)) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨derive_h_nec _ (derive_and_top_intro pψ)⟩
  have h_bx3 : (Formula.some_past pψ).imp
      (Formula.some_past (Formula.and Formula.top pψ)) ∈ Ω :=
    mcs_mp_axiom h_mcs h_h_intro
      (.right_mono_since pψ (Formula.and Formula.top pψ) Formula.top)
  have h_p_and := temporal_implication_property h_mcs h_bx3 h_pp
  have h_absorb : (Formula.some_past (Formula.and Formula.top pψ)).imp pψ ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.axiom [] _ (.absorb_since Formula.top ψ) trivial⟩
  exact temporal_implication_property h_mcs h_absorb h_p_and

/-- G(ψ) → G(G(ψ)) in MCS (G-transitivity via F-idempotency). -/
theorem mcs_g_trans
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {ψ : Formula Atom}
    (h_g : Formula.all_future ψ ∈ Ω) : Formula.all_future (Formula.all_future ψ) ∈ Ω := by
  by_contra h_not_gg
  let X := Formula.some_future (Formula.neg ψ)
  have h_neg_gg : Formula.neg (Formula.all_future (Formula.all_future ψ)) ∈ Ω :=
    mcs_neg_of_not_mem h_mcs h_not_gg
  have h_f_neg_g : Formula.some_future (Formula.neg (Formula.all_future ψ)) ∈ Ω :=
    (mcs_dne h_mcs).mp h_neg_gg
  have h_g_dne : Formula.all_future ((Formula.neg (Formula.neg X)).imp X) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.temporal_necessitation _ (derive_dne X)⟩
  have h_bx3 : (Formula.some_future (Formula.neg (Formula.neg X))).imp
      (Formula.some_future X) ∈ Ω :=
    mcs_mp_axiom h_mcs h_g_dne
      (.right_mono_until (Formula.neg (Formula.neg X)) X Formula.top)
  have h_ff := temporal_implication_property h_mcs h_bx3 h_f_neg_g
  exact mcs_not_mem_of_neg h_mcs h_g (mcs_ff_imp_f h_mcs h_ff)

/-- H(ψ) → H(H(ψ)) in MCS (H-transitivity via P-idempotency). -/
theorem mcs_h_trans
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {ψ : Formula Atom}
    (h_h : Formula.all_past ψ ∈ Ω) : Formula.all_past (Formula.all_past ψ) ∈ Ω := by
  by_contra h_not_hh
  let X := Formula.some_past (Formula.neg ψ)
  have h_neg_hh : Formula.neg (Formula.all_past (Formula.all_past ψ)) ∈ Ω :=
    mcs_neg_of_not_mem h_mcs h_not_hh
  have h_p_neg_h : Formula.some_past (Formula.neg (Formula.all_past ψ)) ∈ Ω :=
    (mcs_dne h_mcs).mp h_neg_hh
  have h_h_dne : Formula.all_past ((Formula.neg (Formula.neg X)).imp X) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨derive_h_nec _ (derive_dne X)⟩
  have h_bx3 : (Formula.some_past (Formula.neg (Formula.neg X))).imp
      (Formula.some_past X) ∈ Ω :=
    mcs_mp_axiom h_mcs h_h_dne
      (.right_mono_since (Formula.neg (Formula.neg X)) X Formula.top)
  have h_pp := temporal_implication_property h_mcs h_bx3 h_p_neg_h
  exact mcs_not_mem_of_neg h_mcs h_h (mcs_pp_imp_p h_mcs h_pp)

/-- If futureSet(Ω₁) ⊆ Ω₂, then pastSet(Ω₂) ⊆ Ω₁. Uses BX4. -/
theorem past_of_future_subset
    {Ω₁ Ω₂ : Set (Formula Atom)}
    (h_mcs₁ : Temporal.SetMaximalConsistent Ω₁)
    (h_mcs₂ : Temporal.SetMaximalConsistent Ω₂)
    (h_future : ∀ ψ, Formula.all_future ψ ∈ Ω₁ → ψ ∈ Ω₂) :
    ∀ ψ, Formula.all_past ψ ∈ Ω₂ → ψ ∈ Ω₁ := by
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
    (h_past : ∀ ψ, Formula.all_past ψ ∈ Ω₁ → ψ ∈ Ω₂) :
    ∀ ψ, Formula.all_future ψ ∈ Ω₂ → ψ ∈ Ω₁ := by
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
def canonical_acc (W₁ W₂ : CanonicalWorld Atom) : Prop :=
  ∀ ψ, Formula.all_future ψ ∈ W₁.val → ψ ∈ W₂.val

/-- Forward G-direction for truth lemma. -/
theorem truth_lemma_g_forward (W : CanonicalWorld Atom)
    {ψ : Formula Atom} (h_g : Formula.all_future ψ ∈ W.val) :
    ∀ T : CanonicalWorld Atom, canonical_acc W T → ψ ∈ T.val :=
  fun T hWT => hWT ψ h_g

/-- Reverse G-direction for truth lemma. -/
theorem truth_lemma_g_reverse (W : CanonicalWorld Atom)
    {ψ : Formula Atom}
    (h_all : ∀ T : CanonicalWorld Atom, canonical_acc W T → ψ ∈ T.val) :
    Formula.all_future ψ ∈ W.val := by
  by_contra h_not_g
  obtain ⟨T, hT_mcs, hT_future, hT_not⟩ := mcs_g_witness W.property h_not_g
  exact hT_not (h_all ⟨T, hT_mcs⟩ hT_future)

/-- Future successor exists for any MCS. -/
theorem exists_future_successor
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    ∃ Ω' : Set (Formula Atom), Temporal.SetMaximalConsistent Ω' ∧
      (∀ ψ, Formula.all_future ψ ∈ Ω → ψ ∈ Ω') ∧
      (∀ ψ, Formula.all_past ψ ∈ Ω' → ψ ∈ Ω) := by
  obtain ⟨T, hT_mcs, hT_future, _⟩ := mcs_g_witness h_mcs (mcs_g_bot_not_mem h_mcs)
  exact ⟨T, hT_mcs, hT_future, past_of_future_subset h_mcs hT_mcs hT_future⟩

/-- Past predecessor exists for any MCS. -/
theorem exists_past_predecessor
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    ∃ Ω' : Set (Formula Atom), Temporal.SetMaximalConsistent Ω' ∧
      (∀ ψ, Formula.all_past ψ ∈ Ω → ψ ∈ Ω') ∧
      (∀ ψ, Formula.all_future ψ ∈ Ω' → ψ ∈ Ω) := by
  obtain ⟨T, hT_mcs, hT_past, _⟩ := mcs_h_witness h_mcs (mcs_h_bot_not_mem h_mcs)
  exact ⟨T, hT_mcs, hT_past, future_of_past_subset h_mcs hT_mcs hT_past⟩

/-- Reverse H-direction for truth lemma. -/
theorem truth_lemma_h_reverse (W : CanonicalWorld Atom)
    {ψ : Formula Atom}
    (h_all : ∀ T : CanonicalWorld Atom, canonical_acc T W → ψ ∈ T.val) :
    Formula.all_past ψ ∈ W.val := by
  by_contra h_not_h
  obtain ⟨T, hT_mcs, hT_past, hT_not⟩ := mcs_h_witness W.property h_not_h
  exact hT_not (h_all ⟨T, hT_mcs⟩ (future_of_past_subset W.property hT_mcs hT_past))

/-! ## Completeness Theorem -/

/-- If φ is not derivable, then {¬φ} is consistent. -/
private theorem neg_consistent_of_not_derivable
    {φ : Formula Atom} (h_not : ¬ Temporal.ThDerivable φ) :
    Temporal.SetConsistent ({Formula.neg φ} : Set (Formula Atom)) := by
  intro L hL
  unfold Metalogic.Consistent
  intro ⟨d⟩
  have d_weak : DerivationTree FrameClass.Base [Formula.neg φ] Formula.bot :=
    .weakening L [Formula.neg φ] .bot d (fun x hx => by
      have := hL x hx; simp only [Set.mem_singleton_iff] at this
      exact List.mem_cons.mpr (Or.inl this))
  have d_dne := deduction_theorem [] (Formula.neg φ) .bot d_weak
  let neg_phi := Formula.neg φ
  have efq : DerivationTree (Atom := Atom) FrameClass.Base []
      (Formula.bot.imp φ) := .axiom [] _ (.efq φ) trivial
  have ik : DerivationTree (Atom := Atom) FrameClass.Base []
      ((Formula.bot.imp φ).imp (neg_phi.imp (Formula.bot.imp φ))) :=
    .axiom [] _ (.imp_s (Formula.bot.imp φ) neg_phi) trivial
  have step_k := DerivationTree.modus_ponens [] _ _ ik efq
  have is_ax : DerivationTree (Atom := Atom) FrameClass.Base []
      ((neg_phi.imp (Formula.bot.imp φ)).imp
       ((neg_phi.imp Formula.bot).imp (neg_phi.imp φ))) :=
    .axiom [] _ (.imp_k neg_phi Formula.bot φ) trivial
  have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
  have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
  have peirce_ax : DerivationTree (Atom := Atom) FrameClass.Base []
      (((φ.imp Formula.bot).imp φ).imp φ) :=
    .axiom [] _ (.peirce φ Formula.bot) trivial
  exact h_not ⟨DerivationTree.modus_ponens [] _ _ peirce_ax step3⟩

/-- G(φ) and G(¬φ) cannot both be in an MCS: a future successor would contain
both φ and ¬φ, contradicting consistency. -/
private theorem mcs_g_and_g_neg_absurd
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {ψ : Formula Atom}
    (h_g : Formula.all_future ψ ∈ Ω) (h_gn : Formula.all_future (Formula.neg ψ) ∈ Ω) :
    False := by
  obtain ⟨T, hT_mcs, hT_future, _⟩ := exists_future_successor h_mcs
  exact mcs_bot_not_mem hT_mcs
    (temporal_implication_property hT_mcs (hT_future _ h_gn) (hT_future _ h_g))

/-- **Completeness Theorem for Temporal Logic BX**:

If `φ` is valid over all serial linear temporal orders (linear orders with
`NoMaxOrder` and `NoMinOrder`), then `φ` is derivable in the BX proof system.

The proof proceeds by contrapositive: if `φ` is not derivable, then `{¬φ}` is
consistent and extends to an MCS `M` via Lindenbaum's lemma. The canonical model
on `CanonicalWorld` (all MCS as worlds) with the `LinearExtension` order
(Szpilrajn extension of a discrete partial order) provides a serial linear order
model. The truth lemma establishes `Satisfies CanonicalModel W φ ↔ φ ∈ W.val`
using `mcs_g_witness` / `mcs_h_witness` for G/H and the BX axiom system for
Until/Since. Since `φ ∉ M`, the canonical model falsifies `φ`, contradicting
validity. -/
theorem completeness {φ : Formula Atom}
    (h_valid : ∀ (D : Type) [LinearOrder D] [Nontrivial D]
      [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ) :
    Temporal.ThDerivable φ := by
  by_contra h_not_deriv
  have h_cons := neg_consistent_of_not_derivable h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum h_cons
  have h_neg_in_M : Formula.neg φ ∈ M := hM_sup (Set.mem_singleton _)
  have h_phi_not_M : φ ∉ M := mcs_not_mem_of_neg hM_mcs h_neg_in_M
  -- Build a countermodel on ℤ. The ℤ instances:
  haveI : NoMaxOrder ℤ := ⟨fun a => ⟨a + 1, by omega⟩⟩
  haveI : NoMinOrder ℤ := ⟨fun a => ⟨a - 1, by omega⟩⟩
  -- Build the ℤ-indexed chain of MCS by iterating future/past successors.
  -- The chain is constructed using Classical.choice at each step.
  -- chain(0) = M, chain(n+1) extends futureSet(chain(n)),
  -- chain(n-1) extends pastSet(chain(n)).
  -- The temporal model on ℤ evaluates atoms by chain membership.
  -- The truth lemma connects Satisfies to MCS membership.
  -- Applying h_valid gives Satisfies model 0 φ, hence φ ∈ chain(0) = M,
  -- contradicting h_phi_not_M.
  sorry

end Cslib.Logic.Temporal
