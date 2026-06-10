/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers
public import Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived
public import Cslib.Foundations.Logic.Theorems.Modal.S5

/-! # Perpetuity Principles (P1-P5)

This module contains the proofs of perpetuity principles P1 through P5, which
establish fundamental connections between modal necessity (□) and temporal operators
(always △, sometimes ▽).

## Main Theorems

- `perpetuity_1`: `□φ → △φ` (necessary implies always)
- `perpetuity_2`: `▽φ → ◇φ` (sometimes implies possible)
- `perpetuity_3`: `□φ → □△φ` (necessity of perpetuity)
- `perpetuity_4`: `◇▽φ → ◇φ` (possibility of occurrence)
- `perpetuity_5`: `◇▽φ → △◇φ` (persistent possibility)

## References

* Ported from BimodalLogic/Theories/Bimodal/Theorems/Perpetuity/Principles.lean
-/

set_option linter.style.longLine false
set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Theorems.Perpetuity

open Cslib.Logic

variable {Atom : Type u}

-- Local notation for derivability at Base frame class
local notation:50 "⊢ " phi =>
  Bimodal.DerivationTree Bimodal.FrameClass.Base ([] : List (Bimodal.Formula Atom)) phi

-- Abbreviation for axiom constructor with base frame class
abbrev ax (Gamma : List (Bimodal.Formula Atom)) (phi : Bimodal.Formula Atom)
    (h : Bimodal.Axiom phi) (h_fc : h.minFrameClass ≤ Bimodal.FrameClass.Base := by trivial) :
    Bimodal.DerivationTree Bimodal.FrameClass.Base Gamma phi :=
  Bimodal.DerivationTree.axiom Gamma phi h h_fc

noncomputable section

/-! ## P1: Necessary Implies Always -/

/-- P1: `□φ → △φ` (necessary implies always).

Derivation combines three components:
1. `□φ → Hφ` (past): via temporal duality on MF
2. `□φ → φ` (present): via MT axiom
3. `□φ → Gφ` (future): via MF then MT
4. Combine: `□φ → Hφ ∧ (φ ∧ Gφ)` -/
def perpetuity_1 (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp φ.always :=
  combineImpConj_3 (boxToPast φ) (boxToPresent φ) (boxToFuture φ)

/-! ## P2: Sometimes Implies Possible -/

/-- P2: `▽φ → ◇φ` (sometimes implies possible).

From P1 for ¬φ: `□(¬φ) → △(¬φ)`.
Contrapose: `¬△(¬φ) → ¬□(¬φ)`.
Which is: `▽φ → ◇φ`. -/
def perpetuity_2 (φ : Bimodal.Formula Atom) : ⊢ φ.sometimes.imp φ.diamond :=
  contraposition (perpetuity_1 φ.neg)

/-! ## P3: Necessity of Perpetuity -/

/-- Box implies boxed past: `⊢ □φ → □Hφ`. Via temporal duality on MF. -/
def boxToBoxPast (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp (φ.allPast.box) := by
  have mf : ⊢ φ.swapTemporal.box.imp (φ.swapTemporal.allFuture.box) :=
    ax [] _ (Bimodal.Axiom.modal_future φ.swapTemporal)
  have mf_swap := Bimodal.DerivationTree.temporal_duality _ mf
  simp only [Bimodal.Formula.swapTemporal, Bimodal.Formula.swapTemporal_involution] at mf_swap
  exact mf_swap

/-- Boxed conjunction intro from implications: from `⊢ Q → □A` and `⊢ Q → □B`,
    derive `⊢ Q → □(A ∧ B)`. -/
def boxConjIntroImp {φ₀ φ₁ φ₂ : Bimodal.Formula Atom}
    (hA : ⊢ φ₀.imp φ₁.box) (hB : ⊢ φ₀.imp φ₂.box) : ⊢ φ₀.imp (φ₁.and φ₂).box := by
  have pair : ⊢ φ₁.imp (φ₂.imp (φ₁.and φ₂)) :=
    unwrap (@Theorems.Combinators.pairing _ _ _ Bimodal.HilbertTM _ _ φ₁ φ₂)
  have box_pair := Bimodal.DerivationTree.necessitation _ pair
  have mk1 := ax [] _ (Bimodal.Axiom.modal_k_dist φ₁ (φ₂.imp (φ₁.and φ₂)))
  have h1 := Bimodal.DerivationTree.modus_ponens [] _ _ mk1 box_pair
  have mk2 := ax [] _ (Bimodal.Axiom.modal_k_dist φ₂ (φ₁.and φ₂))
  have box_to_box := impTrans h1 mk2
  have h2 := impTrans hA box_to_box
  have k_ax := ax [] _ (Bimodal.Axiom.imp_k φ₀ φ₂.box (φ₁.and φ₂).box)
  have h3 := Bimodal.DerivationTree.modus_ponens [] _ _ k_ax h2
  exact Bimodal.DerivationTree.modus_ponens [] _ _ h3 hB

/-- Three-way boxed conjunction intro from implications. -/
def boxConjIntroImp_3 {φ₀ φ₁ φ₂ φ₃ : Bimodal.Formula Atom}
    (hA : ⊢ φ₀.imp φ₁.box) (hB : ⊢ φ₀.imp φ₂.box) (hC : ⊢ φ₀.imp φ₃.box) :
    ⊢ φ₀.imp (φ₁.and (φ₂.and φ₃)).box :=
  boxConjIntroImp hA (boxConjIntroImp hB hC)

/-- P3: `□φ → □△φ` (necessity of perpetuity).

Uses `boxToBoxPast`, identity, MF, and `boxConjIntroImp_3`. -/
def perpetuity_3 (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp (φ.always.box) :=
  boxConjIntroImp_3
    (boxToBoxPast φ)
    (identity φ.box)
    (ax [] _ (Bimodal.Axiom.modal_future φ))

/-! ## P4: Possibility of Occurrence -/

/-- P4: `◇▽φ → ◇φ` (possibility of occurrence).

Contraposition of P3 at ¬φ, with DNI bridge for double negation. -/
def perpetuity_4 (φ : Bimodal.Formula Atom) : ⊢ φ.sometimes.diamond.imp φ.diamond := by
  have p3_neg := perpetuity_3 φ.neg
  have contraposed := contraposition p3_neg
  have dni_always := dni φ.neg.always
  have box_dni_always := Bimodal.DerivationTree.necessitation _ dni_always
  have mk_dni := ax [] _ (Bimodal.Axiom.modal_k_dist φ.neg.always φ.neg.always.neg.neg)
  have box_dni_imp := Bimodal.DerivationTree.modus_ponens [] _ _ mk_dni box_dni_always
  have bridge := contraposition box_dni_imp
  exact impTrans bridge contraposed

/-! ## P5: Persistent Possibility -/

/-- G-distribution: `⊢ G(φ → ψ) → (Gφ → Gψ)`. Wraps generic typeclass theorem. -/
def futureKDist (φ₁ φ₂ : Bimodal.Formula Atom) :
    ⊢ (φ₁.imp φ₂).allFuture.imp (φ₁.allFuture.imp φ₂.allFuture) := by
  exact unwrap (@Theorems.Temporal.TemporalDerived.G_distribution
    (Bimodal.Formula Atom) _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ₁) (ψ := φ₂))

/-- H-distribution: `⊢ H(φ → ψ) → (Hφ → Hψ)`. Wraps generic typeclass theorem. -/
def pastKDist (φ₁ φ₂ : Bimodal.Formula Atom) :
    ⊢ (φ₁.imp φ₂).allPast.imp (φ₁.allPast.imp φ₂.allPast) := by
  exact unwrap (@Theorems.Temporal.TemporalDerived.H_distribution
    (Bimodal.Formula Atom) _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ₁) (ψ := φ₂))

/-- Modal 5: `⊢ ◇φ → □◇φ`. Wraps S5 typeclass theorem. -/
def modal_5 (φ : Bimodal.Formula Atom) : ⊢ φ.diamond.imp φ.diamond.box :=
  unwrap (@Theorems.Modal.S5.axiom5_derived _ _ _ _ _ _ _ _)

/-- Persistence lemma: `◇φ → △◇φ` (possibility is perpetual).

Uses modal_5 (◇φ → □◇φ), tempFutureDerived, temporal duality,
future/past K distribution, and combineImpConj_3. -/
def persistence (φ : Bimodal.Formula Atom) : ⊢ φ.diamond.imp φ.diamond.always := by
  have m5 := modal_5 φ
  have tf := tempFutureDerived φ.diamond

  -- TD for □◇φ: □◇φ → H□◇φ
  have td : ⊢ φ.diamond.box.imp φ.diamond.box.allPast := by
    have tf_swap : ⊢ φ.diamond.swapTemporal.box.imp φ.diamond.swapTemporal.box.allFuture :=
      tempFutureDerived φ.diamond.swapTemporal
    have td_result := Bimodal.DerivationTree.temporal_duality _ tf_swap
    simp only [Bimodal.Formula.swapTemporal, Bimodal.Formula.swapTemporal_involution] at td_result
    exact td_result

  -- Step 1: ◇φ → H◇φ
  have past_comp : ⊢ φ.diamond.imp φ.diamond.allPast := by
    have chain1 := impTrans m5 td
    have mt := boxToPresent φ.diamond
    -- Build H(□◇φ → ◇φ) via temporal duality
    have mt_swap : ⊢ φ.diamond.swapTemporal.box.imp φ.diamond.swapTemporal :=
      boxToPresent φ.diamond.swapTemporal
    have future_mt_swap := Bimodal.DerivationTree.temporal_necessitation _ mt_swap
    have past_mt_raw := Bimodal.DerivationTree.temporal_duality _ future_mt_swap
    have past_mt : ⊢ (φ.diamond.box.imp φ.diamond).allPast := by
      simp only [Bimodal.Formula.swapTemporal, Bimodal.Formula.swapTemporal_involution] at past_mt_raw
      exact past_mt_raw
    have pk := pastKDist φ.diamond.box φ.diamond
    have past_bridge := Bimodal.DerivationTree.modus_ponens [] _ _ pk past_mt
    exact impTrans chain1 past_bridge

  -- Step 2: ◇φ → ◇φ (identity)
  have present_comp := identity φ.diamond

  -- Step 3: ◇φ → G◇φ
  have future_comp : ⊢ φ.diamond.imp φ.diamond.allFuture := by
    have chain2 := impTrans m5 tf
    have mt := boxToPresent φ.diamond
    have future_mt := Bimodal.DerivationTree.temporal_necessitation _ mt
    have fk := futureKDist φ.diamond.box φ.diamond
    have future_bridge := Bimodal.DerivationTree.modus_ponens [] _ _ fk future_mt
    exact impTrans chain2 future_bridge

  exact combineImpConj_3 past_comp present_comp future_comp

/-- P5: `◇▽φ → △◇φ` (persistent possibility).

Composition of P4 and persistence. -/
def perpetuity_5 (φ : Bimodal.Formula Atom) : ⊢ φ.sometimes.diamond.imp φ.diamond.always :=
  impTrans (perpetuity_4 φ) (persistence φ)

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Perpetuity
