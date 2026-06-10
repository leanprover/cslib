/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
import Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles

/-! # Perpetuity Bridge Lemmas and P6

This module contains bridge lemmas connecting modal and temporal duality,
monotonicity lemmas, and the proof of perpetuity principle P6.

## Main Theorems

- `perpetuity_6`: `▽□φ → □△φ` (occurrent necessity is perpetual)

## Bridge Lemmas

- `modal_duality_neg`: `◇¬φ → ¬□φ`
- `modal_duality_neg_rev`: `¬□φ → ◇¬φ`
- `temporal_duality_neg`: `▽¬φ → ¬△φ`
- `temporal_duality_neg_rev`: `¬△φ → ▽¬φ`
- `bridge1`: `¬□△φ → ◇▽¬φ`
- `bridge2`: `△◇¬φ → ¬▽□φ`

## References

* Ported from BimodalLogic/Theories/Bimodal/Theorems/Perpetuity/Bridge.lean
-/

set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Theorems.Perpetuity

open Cslib.Logic

variable {Atom : Type u}

-- Local notation for derivability at Base frame class
local notation:50 "⊢ " phi =>
  Bimodal.DerivationTree Bimodal.FrameClass.Base ([] : List (Bimodal.Formula Atom)) phi

noncomputable section

/-! ## Modal Duality Lemmas -/

/-- Modal duality (forward): `◇¬φ → ¬□φ`.

Uses DNI lifted through box, then contraposed. -/
def modal_duality_neg (φ : Bimodal.Formula Atom) : ⊢ φ.neg.diamond.imp φ.box.neg := by
  have dni_phi := dni φ
  have box_dni := Bimodal.DerivationTree.necessitation _ dni_phi
  have mk := Bimodal.DerivationTree.axiom (fc := Bimodal.FrameClass.Base) [] _
    (Bimodal.Axiom.modal_k_dist φ φ.neg.neg) trivial
  have forward := Bimodal.DerivationTree.modus_ponens [] _ _ mk box_dni
  exact contraposition forward

/-- Modal duality (reverse): `¬□φ → ◇¬φ`.

Uses DNE lifted through box, then contraposed. -/
def modal_duality_neg_rev (φ : Bimodal.Formula Atom) : ⊢ φ.box.neg.imp φ.neg.diamond := by
  have dne_phi := double_negation φ
  have box_dne := Bimodal.DerivationTree.necessitation _ dne_phi
  have mk := Bimodal.DerivationTree.axiom (fc := Bimodal.FrameClass.Base) [] _
    (Bimodal.Axiom.modal_k_dist φ.neg.neg φ) trivial
  have forward := Bimodal.DerivationTree.modus_ponens [] _ _ mk box_dne
  exact contraposition forward

/-! ## Monotonicity Lemmas -/

/-- Box monotonicity: from `⊢ A → B`, derive `⊢ □A → □B`. -/
def box_mono {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.imp φ₂) : ⊢ φ₁.box.imp φ₂.box := by
  have box_h := Bimodal.DerivationTree.necessitation _ h
  have mk := Bimodal.DerivationTree.axiom (fc := Bimodal.FrameClass.Base) [] _
    (Bimodal.Axiom.modal_k_dist φ₁ φ₂) trivial
  exact Bimodal.DerivationTree.modus_ponens [] _ _ mk box_h

/-- Diamond monotonicity: from `⊢ A → B`, derive `⊢ ◇A → ◇B`. -/
def diamond_mono {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.imp φ₂) : ⊢ φ₁.diamond.imp φ₂.diamond :=
  contraposition (box_mono (contraposition h))

/-- Future monotonicity: from `⊢ A → B`, derive `⊢ GA → GB`. -/
def future_mono {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.imp φ₂) : ⊢ φ₁.all_future.imp φ₂.all_future := by
  have g_h := Bimodal.DerivationTree.temporal_necessitation _ h
  have fk := future_k_dist φ₁ φ₂
  exact Bimodal.DerivationTree.modus_ponens [] _ _ fk g_h

/-- Past monotonicity: from `⊢ A → B`, derive `⊢ HA → HB`. -/
def past_mono {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.imp φ₂) : ⊢ φ₁.all_past.imp φ₂.all_past := by
  -- Apply temporal duality to get swap(A → B)
  have h_swap := Bimodal.DerivationTree.temporal_duality _ h
  -- Temporal necessitate the swapped implication
  have g_swap := Bimodal.DerivationTree.temporal_necessitation _ h_swap
  -- Apply temporal duality again to get H(A → B)
  have past_raw := Bimodal.DerivationTree.temporal_duality _ g_swap
  have h_past : ⊢ (φ₁.imp φ₂).all_past := by
    simp only [Bimodal.Formula.swap_temporal, Bimodal.Formula.swap_temporal_involution] at past_raw
    exact past_raw
  have pk := past_k_dist φ₁ φ₂
  exact Bimodal.DerivationTree.modus_ponens [] _ _ pk h_past

/-! ## Always Decomposition/Recomposition -/

/-- Decomposition: `⊢ △φ → Hφ`. -/
def always_to_past (φ : Bimodal.Formula Atom) : ⊢ φ.always.imp φ.all_past :=
  lce_imp φ.all_past (φ.and φ.all_future)

/-- Decomposition: `⊢ △φ → φ`. -/
def always_to_present (φ : Bimodal.Formula Atom) : ⊢ φ.always.imp φ :=
  imp_trans (rce_imp φ.all_past (φ.and φ.all_future)) (lce_imp φ φ.all_future)

/-- Decomposition: `⊢ △φ → Gφ`. -/
def always_to_future (φ : Bimodal.Formula Atom) : ⊢ φ.always.imp φ.all_future :=
  imp_trans (rce_imp φ.all_past (φ.and φ.all_future)) (rce_imp φ φ.all_future)

/-- Composition: `⊢ (Hφ ∧ (φ ∧ Gφ)) → △φ`. Definitional equality. -/
def past_present_future_to_always (φ : Bimodal.Formula Atom) :
    ⊢ (φ.all_past.and (φ.and φ.all_future)).imp φ.always :=
  identity (φ.all_past.and (φ.and φ.all_future))

/-! ## DNI/DNE over Always -/

/-- DNI distributes over always: `⊢ △φ → △(¬¬φ)`. -/
def always_dni (φ : Bimodal.Formula Atom) : ⊢ φ.always.imp φ.neg.neg.always := by
  have dni_phi := dni φ
  have past_lift := past_mono dni_phi
  have future_lift := future_mono dni_phi
  have past_comp := imp_trans (always_to_past φ) past_lift
  have present_comp := imp_trans (always_to_present φ) dni_phi
  have future_comp := imp_trans (always_to_future φ) future_lift
  exact combine_imp_conj_3 past_comp present_comp future_comp

/-- DNE distributes over always: `⊢ △(¬¬φ) → △φ`. -/
def always_dne (φ : Bimodal.Formula Atom) : ⊢ φ.neg.neg.always.imp φ.always := by
  have dne_phi := double_negation φ
  have past_lift := past_mono dne_phi
  have future_lift := future_mono dne_phi
  have past_comp := imp_trans (always_to_past φ.neg.neg) past_lift
  have present_comp := imp_trans (always_to_present φ.neg.neg) dne_phi
  have future_comp := imp_trans (always_to_future φ.neg.neg) future_lift
  exact combine_imp_conj_3 past_comp present_comp future_comp

/-! ## Temporal Duality Lemmas -/

/-- Temporal duality (forward): `▽¬φ → ¬△φ`. Contraposition of always_dni. -/
def temporal_duality_neg (φ : Bimodal.Formula Atom) : ⊢ φ.neg.sometimes.imp φ.always.neg :=
  contraposition (always_dni φ)

/-- Temporal duality (reverse): `¬△φ → ▽¬φ`. Contraposition of always_dne. -/
def temporal_duality_neg_rev (φ : Bimodal.Formula Atom) : ⊢ φ.always.neg.imp φ.neg.sometimes :=
  contraposition (always_dne φ)

/-! ## Always Monotonicity -/

/-- Always monotonicity: from `⊢ A → B`, derive `⊢ △A → △B`. -/
def always_mono {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.imp φ₂) : ⊢ φ₁.always.imp φ₂.always := by
  have past_h := past_mono h
  have future_h := future_mono h
  have comp_past := imp_trans (always_to_past φ₁) past_h
  have comp_present := imp_trans (always_to_present φ₁) h
  have comp_future := imp_trans (always_to_future φ₁) future_h
  exact combine_imp_conj_3 comp_past comp_present comp_future

/-! ## Double Contraposition -/

/-- Double contraposition: from `⊢ ¬A → ¬B`, derive `⊢ B → A`. -/
def double_contrapose {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.neg.imp φ₂.neg) : ⊢ φ₂.imp φ₁ := by
  have contra := contraposition h
  have dne_a := double_negation φ₁
  have chain := imp_trans contra dne_a
  have dni_b := dni φ₂
  exact imp_trans dni_b chain

/-! ## Bridge Lemmas for P6 -/

/-- Bridge 1: `¬□△φ → ◇▽¬φ`.

1. `modal_duality_neg_rev` on `△φ`: `¬□△φ → ◇¬△φ`
2. `temporal_duality_neg_rev` on `φ`: `¬△φ → ▽¬φ`
3. `diamond_mono` lifts step 2: `◇¬△φ → ◇▽¬φ`
4. Compose. -/
def bridge1 (φ : Bimodal.Formula Atom) : ⊢ φ.always.box.neg.imp φ.neg.sometimes.diamond := by
  have md_rev := modal_duality_neg_rev φ.always
  have td_rev := temporal_duality_neg_rev φ
  have dm := diamond_mono td_rev
  exact imp_trans md_rev dm

/-- Bridge 2: `△◇¬φ → ¬▽□φ`.

1. `modal_duality_neg` on `φ`: `◇¬φ → ¬□φ`
2. `always_mono` lifts step 1: `△◇¬φ → △¬□φ`
3. DNI on `△¬□φ`: `△¬□φ → ¬¬△¬□φ` (which is `¬▽□φ`)
4. Compose. -/
def bridge2 (φ : Bimodal.Formula Atom) : ⊢ φ.neg.diamond.always.imp φ.box.sometimes.neg := by
  have md := modal_duality_neg φ
  have am := always_mono md
  have dni_step := dni φ.box.neg.always
  exact imp_trans am dni_step

/-! ## P6: Occurrent Necessity is Perpetual -/

/-- P6: `▽□φ → □△φ` (occurrent necessity is perpetual).

Derivation via P5 applied to `¬φ` with bridge lemmas:
1. P5 for `¬φ`: `◇▽¬φ → △◇¬φ`
2. Bridge 1: `¬□△φ → ◇▽¬φ`
3. Bridge 2: `△◇¬φ → ¬▽□φ`
4. Chain: `¬□△φ → ¬▽□φ`
5. Double contrapose: `▽□φ → □△φ` -/
def perpetuity_6 (φ : Bimodal.Formula Atom) : ⊢ φ.box.sometimes.imp φ.always.box := by
  have p5_neg := perpetuity_5 φ.neg
  have b1 := bridge1 φ
  have b2 := bridge2 φ
  have chain := imp_trans (imp_trans b1 p5_neg) b2
  exact double_contrapose chain

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Perpetuity
