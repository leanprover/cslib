/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles

/-! # Perpetuity Bridge Lemmas and P6

This module contains bridge lemmas connecting modal and temporal duality,
monotonicity lemmas, and the proof of perpetuity principle P6.

## Main Theorems

- `perpetuity_6`: `▽□φ → □△φ` (occurrent necessity is perpetual)

## Bridge Lemmas

- `modalDualityNeg`: `◇¬φ → ¬□φ`
- `modalDualityNegRev`: `¬□φ → ◇¬φ`
- `temporalDualityNeg`: `▽¬φ → ¬△φ`
- `temporalDualityNegRev`: `¬△φ → ▽¬φ`
- `bridge1`: `¬□△φ → ◇▽¬φ`
- `bridge2`: `△◇¬φ → ¬▽□φ`

## References

* Ported from BimodalLogic/Theories/Bimodal/Theorems/Perpetuity/Bridge.lean
-/

set_option linter.style.longLine false

@[expose] public section

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
def modalDualityNeg (φ : Bimodal.Formula Atom) : ⊢ φ.neg.diamond.imp φ.box.neg := by
  have dni_phi := dni φ
  have box_dni := Bimodal.DerivationTree.necessitation _ dni_phi
  have mk := Bimodal.DerivationTree.axiom (fc := Bimodal.FrameClass.Base) [] _
    (Bimodal.Axiom.modal_k_dist φ φ.neg.neg) trivial
  have forward := Bimodal.DerivationTree.modus_ponens [] _ _ mk box_dni
  exact contraposition forward

/-- Modal duality (reverse): `¬□φ → ◇¬φ`.

Uses DNE lifted through box, then contraposed. -/
def modalDualityNegRev (φ : Bimodal.Formula Atom) : ⊢ φ.box.neg.imp φ.neg.diamond := by
  have dne_phi := doubleNegation φ
  have box_dne := Bimodal.DerivationTree.necessitation _ dne_phi
  have mk := Bimodal.DerivationTree.axiom (fc := Bimodal.FrameClass.Base) [] _
    (Bimodal.Axiom.modal_k_dist φ.neg.neg φ) trivial
  have forward := Bimodal.DerivationTree.modus_ponens [] _ _ mk box_dne
  exact contraposition forward

/-! ## Monotonicity Lemmas -/

/-- Box monotonicity: from `⊢ A → B`, derive `⊢ □A → □B`. -/
def boxMono {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.imp φ₂) : ⊢ φ₁.box.imp φ₂.box := by
  have box_h := Bimodal.DerivationTree.necessitation _ h
  have mk := Bimodal.DerivationTree.axiom (fc := Bimodal.FrameClass.Base) [] _
    (Bimodal.Axiom.modal_k_dist φ₁ φ₂) trivial
  exact Bimodal.DerivationTree.modus_ponens [] _ _ mk box_h

/-- Diamond monotonicity: from `⊢ A → B`, derive `⊢ ◇A → ◇B`. -/
def diamondMono {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.imp φ₂) : ⊢ φ₁.diamond.imp φ₂.diamond :=
  contraposition (boxMono (contraposition h))

/-- Future monotonicity: from `⊢ A → B`, derive `⊢ GA → GB`. -/
def futureMono {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.imp φ₂) : ⊢ φ₁.allFuture.imp φ₂.allFuture := by
  have g_h := Bimodal.DerivationTree.temporal_necessitation _ h
  have fk := futureKDist φ₁ φ₂
  exact Bimodal.DerivationTree.modus_ponens [] _ _ fk g_h

/-- Past monotonicity: from `⊢ A → B`, derive `⊢ HA → HB`. -/
def pastMono {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.imp φ₂) : ⊢ φ₁.allPast.imp φ₂.allPast := by
  -- Apply temporal duality to get swap(A → B)
  have h_swap := Bimodal.DerivationTree.temporal_duality _ h
  -- Temporal necessitate the swapped implication
  have g_swap := Bimodal.DerivationTree.temporal_necessitation _ h_swap
  -- Apply temporal duality again to get H(A → B)
  have past_raw := Bimodal.DerivationTree.temporal_duality _ g_swap
  have h_past : ⊢ (φ₁.imp φ₂).allPast := by
    simp only [Bimodal.Formula.swapTemporal, Bimodal.Formula.swapTemporal_involution] at past_raw
    exact past_raw
  have pk := pastKDist φ₁ φ₂
  exact Bimodal.DerivationTree.modus_ponens [] _ _ pk h_past

/-! ## Always Decomposition/Recomposition -/

/-- Decomposition: `⊢ △φ → Hφ`. -/
def alwaysToPast (φ : Bimodal.Formula Atom) : ⊢ φ.always.imp φ.allPast :=
  lceImp φ.allPast (φ.and φ.allFuture)

/-- Decomposition: `⊢ △φ → φ`. -/
def alwaysToPresent (φ : Bimodal.Formula Atom) : ⊢ φ.always.imp φ :=
  impTrans (rceImp φ.allPast (φ.and φ.allFuture)) (lceImp φ φ.allFuture)

/-- Decomposition: `⊢ △φ → Gφ`. -/
def alwaysToFuture (φ : Bimodal.Formula Atom) : ⊢ φ.always.imp φ.allFuture :=
  impTrans (rceImp φ.allPast (φ.and φ.allFuture)) (rceImp φ φ.allFuture)

/-- Composition: `⊢ (Hφ ∧ (φ ∧ Gφ)) → △φ`. Definitional equality. -/
def pastPresentFutureToAlways (φ : Bimodal.Formula Atom) :
    ⊢ (φ.allPast.and (φ.and φ.allFuture)).imp φ.always :=
  identity (φ.allPast.and (φ.and φ.allFuture))

/-! ## DNI/DNE over Always -/

/-- DNI distributes over always: `⊢ △φ → △(¬¬φ)`. -/
def alwaysDni (φ : Bimodal.Formula Atom) : ⊢ φ.always.imp φ.neg.neg.always := by
  have dni_phi := dni φ
  have past_lift := pastMono dni_phi
  have future_lift := futureMono dni_phi
  have past_comp := impTrans (alwaysToPast φ) past_lift
  have present_comp := impTrans (alwaysToPresent φ) dni_phi
  have future_comp := impTrans (alwaysToFuture φ) future_lift
  exact combineImpConj_3 past_comp present_comp future_comp

/-- DNE distributes over always: `⊢ △(¬¬φ) → △φ`. -/
def alwaysDne (φ : Bimodal.Formula Atom) : ⊢ φ.neg.neg.always.imp φ.always := by
  have dne_phi := doubleNegation φ
  have past_lift := pastMono dne_phi
  have future_lift := futureMono dne_phi
  have past_comp := impTrans (alwaysToPast φ.neg.neg) past_lift
  have present_comp := impTrans (alwaysToPresent φ.neg.neg) dne_phi
  have future_comp := impTrans (alwaysToFuture φ.neg.neg) future_lift
  exact combineImpConj_3 past_comp present_comp future_comp

/-! ## Temporal Duality Lemmas -/

/-- Temporal duality (forward): `▽¬φ → ¬△φ`. Contraposition of alwaysDni. -/
def temporalDualityNeg (φ : Bimodal.Formula Atom) : ⊢ φ.neg.sometimes.imp φ.always.neg :=
  contraposition (alwaysDni φ)

/-- Temporal duality (reverse): `¬△φ → ▽¬φ`. Contraposition of alwaysDne. -/
def temporalDualityNegRev (φ : Bimodal.Formula Atom) : ⊢ φ.always.neg.imp φ.neg.sometimes :=
  contraposition (alwaysDne φ)

/-! ## Always Monotonicity -/

/-- Always monotonicity: from `⊢ A → B`, derive `⊢ △A → △B`. -/
def alwaysMono {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.imp φ₂) : ⊢ φ₁.always.imp φ₂.always := by
  have past_h := pastMono h
  have future_h := futureMono h
  have comp_past := impTrans (alwaysToPast φ₁) past_h
  have comp_present := impTrans (alwaysToPresent φ₁) h
  have comp_future := impTrans (alwaysToFuture φ₁) future_h
  exact combineImpConj_3 comp_past comp_present comp_future

/-! ## Double Contraposition -/

/-- Double contraposition: from `⊢ ¬A → ¬B`, derive `⊢ B → A`. -/
def doubleContrapose {φ₁ φ₂ : Bimodal.Formula Atom} (h : ⊢ φ₁.neg.imp φ₂.neg) : ⊢ φ₂.imp φ₁ := by
  have contra := contraposition h
  have dne_a := doubleNegation φ₁
  have chain := impTrans contra dne_a
  have dni_b := dni φ₂
  exact impTrans dni_b chain

/-! ## Bridge Lemmas for P6 -/

/-- Bridge 1: `¬□△φ → ◇▽¬φ`.

1. `modalDualityNegRev` on `△φ`: `¬□△φ → ◇¬△φ`
2. `temporalDualityNegRev` on `φ`: `¬△φ → ▽¬φ`
3. `diamondMono` lifts step 2: `◇¬△φ → ◇▽¬φ`
4. Compose. -/
def bridge1 (φ : Bimodal.Formula Atom) : ⊢ φ.always.box.neg.imp φ.neg.sometimes.diamond := by
  have md_rev := modalDualityNegRev φ.always
  have td_rev := temporalDualityNegRev φ
  have dm := diamondMono td_rev
  exact impTrans md_rev dm

/-- Bridge 2: `△◇¬φ → ¬▽□φ`.

1. `modalDualityNeg` on `φ`: `◇¬φ → ¬□φ`
2. `alwaysMono` lifts step 1: `△◇¬φ → △¬□φ`
3. DNI on `△¬□φ`: `△¬□φ → ¬¬△¬□φ` (which is `¬▽□φ`)
4. Compose. -/
def bridge2 (φ : Bimodal.Formula Atom) : ⊢ φ.neg.diamond.always.imp φ.box.sometimes.neg := by
  have md := modalDualityNeg φ
  have am := alwaysMono md
  have dni_step := dni φ.box.neg.always
  exact impTrans am dni_step

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
  have chain := impTrans (impTrans b1 p5_neg) b2
  exact doubleContrapose chain

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Perpetuity
