/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Theorems.Propositional.Core
public import Cslib.Foundations.Logic.Theorems.Propositional.Connectives

/-! # Temporal Derived Theorems (Generic Typeclass Style)

Temporal theorems derived from the BX axiom system, generic over `[TemporalBXHilbert S]`.

## Convention Note

Convention (Burgess 1982): `untl φ₁ φ₂` = `φ₁ U φ₂` with `φ₁` as EVENT and `φ₂` as GUARD.
`F(φ) = untl(φ, ⊤)` and `G(φ) = ¬F(¬φ)`. This matches BimodalLogic convention.
-/

@[expose] public section

set_option linter.style.longLine false

namespace Cslib.Logic.Theorems.Temporal.TemporalDerived

open Cslib.Logic
open Cslib.Logic.Axioms
open Cslib.Logic.Theorems.Combinators
open Cslib.Logic.Theorems.Propositional.Core
open Cslib.Logic.Theorems.Propositional.Connectives

variable {F : Type*} [HasBot F] [HasImp F] [HasUntil F] [HasSince F]
variable {S : Type*} [InferenceSystem S F]
variable [TemporalBXHilbert S (F := F)]

section

-- Abbreviations neg'/top' imported from Cslib.Logic.Axioms
abbrev someFuture (φ : F) : F := HasUntil.untl φ top'
abbrev allFuture (φ : F) : F := neg' (someFuture (neg' φ))
abbrev somePast (φ : F) : F := HasSince.snce φ top'
abbrev allPast (φ : F) : F := neg' (somePast (neg' φ))

/-! ### Level 0: Direct Axiom Wrappers -/

/-- Guard monotonicity of Until under G (BX2G): `⊢ G(φ→χ) → (ψ U φ → ψ U χ)`. -/
theorem until_mono_guard {φ χ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.LeftMonoUntilG φ χ ψ) :=
  HasAxiomLeftMonoUntilG.leftMonoUntilG

/-- Guard monotonicity of Since under H (BX2H): `⊢ H(φ→χ) → (ψ S φ → ψ S χ)`. -/
theorem since_mono_guard {φ χ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.LeftMonoSinceH φ χ ψ) :=
  HasAxiomLeftMonoSinceH.leftMonoSinceH

/-- Event monotonicity of Until (BX3): `⊢ G(φ→ψ) → (φ U χ → ψ U χ)`. -/
theorem until_mono_event {φ ψ χ : F} :
    InferenceSystem.DerivableIn S (Axioms.RightMonoUntil φ ψ χ) :=
  HasAxiomRightMonoUntil.rightMonoUntil

/-- Event monotonicity of Since (BX3'): `⊢ H(φ→ψ) → (φ S χ → ψ S χ)`. -/
theorem since_mono_event {φ ψ χ : F} :
    InferenceSystem.DerivableIn S (Axioms.RightMonoSince φ ψ χ) :=
  HasAxiomRightMonoSince.rightMonoSince

/-- Temporal connectedness future (BX4): `⊢ φ → G(P(φ))`. -/
theorem connect_future_thm {φ : F} :
    InferenceSystem.DerivableIn S (Axioms.ConnectFuture φ) :=
  HasAxiomConnectFuture.connectFuture

/-- Temporal connectedness past (BX4'): `⊢ φ → H(F(φ))`. -/
theorem connect_past_thm {φ : F} :
    InferenceSystem.DerivableIn S (Axioms.ConnectPast φ) :=
  HasAxiomConnectPast.connectPast

/-- Until implies F (BX10): `⊢ U(ψ,φ) → F(ψ)`. -/
theorem until_implies_someFuture {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.UntilF φ ψ) :=
  HasAxiomUntilF.untilF

/-- Since implies P (BX10'): `⊢ S(ψ,φ) → P(ψ)`. -/
theorem since_implies_somePast {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.SinceP φ ψ) :=
  HasAxiomSinceP.sinceP

/-! ### F_mono, P_mono

With Burgess convention, F(φ) = untl(φ, ⊤) where the EVENT is φ (first arg).
So F(A) → F(B) = untl(A,⊤) → untl(B,⊤) changes the event (first arg),
which is BX3 (RightMonoUntil) with χ := ⊤.
-/

/-- F is monotone under G: `⊢ G(φ→ψ) → (Fφ → Fψ)`.
    BX3 with χ := ⊤ (event position changes). -/
theorem F_mono {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (allFuture (HasImp.imp φ ψ))
        (HasImp.imp (someFuture φ) (someFuture ψ))) :=
  HasAxiomRightMonoUntil.rightMonoUntil (S := S) (φ := φ) (ψ := ψ) (χ := top')

/-- P is monotone under H: `⊢ H(φ→ψ) → (Pφ → Pψ)`.
    BX3' with χ := ⊤ (event position changes). -/
theorem P_mono {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (allPast (HasImp.imp φ ψ))
        (HasImp.imp (somePast φ) (somePast ψ))) :=
  HasAxiomRightMonoSince.rightMonoSince (S := S) (φ := φ) (ψ := ψ) (χ := top')

/-! ### Duality Lemmas (DNI-based) -/

/-- `⊢ F(¬φ) → ¬(Gφ)`: DNI at F(¬φ). -/
theorem F_neg_G {φ : F} :
    InferenceSystem.DerivableIn S (HasImp.imp (someFuture (neg' φ)) (neg' (allFuture φ))) :=
  dni (someFuture (neg' φ))

/-- `⊢ P(¬φ) → ¬(Hφ)`: DNI at P(¬φ). -/
theorem P_neg_H {φ : F} :
    InferenceSystem.DerivableIn S (HasImp.imp (somePast (neg' φ)) (neg' (allPast φ))) :=
  dni (somePast (neg' φ))

/-! ### Level 1: G-distribution -/

/-- Helper: `⊢ ¬(¬ψ→¬φ) → ¬(φ→ψ)`. -/
private theorem neg_contrapositive_imp_neg {φ ψ : F} :
    InferenceSystem.DerivableIn S (HasImp.imp (neg' (HasImp.imp (neg' ψ) (neg' φ))) (neg' (HasImp.imp φ ψ))) :=
  ModusPonens.mp
    (contrapose_imp (S := S) (φ := HasImp.imp φ ψ) (ψ := HasImp.imp (neg' ψ) (neg' φ)))
    (contrapose_imp (S := S) (φ := φ) (ψ := ψ))

/-- **G-distribution**: `⊢ G(φ→ψ) → (Gφ → Gψ)`.
    Derived from BX3 and propositional contraposition. -/
theorem G_distribution {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (allFuture (HasImp.imp φ ψ))
        (HasImp.imp (allFuture φ) (allFuture ψ))) := by
  -- Step 1: G(neg_contra) via temporal necessitation
  have neg_contra := neg_contrapositive_imp_neg (S := S) (φ := φ) (ψ := ψ)
  have g_nc := TemporalNecessitation.tempNec neg_contra
  -- Step 2: BX3: G(¬(¬ψ→¬φ) → ¬(φ→ψ)) → (F(¬(¬ψ→¬φ)) → F(¬(φ→ψ)))
  -- Using F_mono pattern (BX3 with χ := ⊤, event monotonicity)
  have bx3 := HasAxiomRightMonoUntil.rightMonoUntil (S := S)
    (φ := neg' (HasImp.imp (neg' ψ) (neg' φ)))
    (ψ := neg' (HasImp.imp φ ψ))
    (χ := top')
  have F_step := ModusPonens.mp bx3 g_nc
  -- Step 3: Contrapose: G(φ→ψ) → G(¬ψ→¬φ)
  have G_contra := contraposition F_step
  -- Step 4: BX3: G(¬ψ→¬φ) → (F(¬ψ) → F(¬φ))
  have bx3' := HasAxiomRightMonoUntil.rightMonoUntil (S := S)
    (φ := neg' ψ) (ψ := neg' φ) (χ := top')
  -- Step 5: Contrapose to get Gφ → Gψ
  have cp := contrapose_imp (S := S)
    (φ := someFuture (neg' ψ)) (ψ := someFuture (neg' φ))
  have GK := imp_trans bx3' cp
  exact imp_trans G_contra GK

/-- **H-distribution**: `⊢ H(φ→ψ) → (Hφ → Hψ)`.
    Derived from BX3' and propositional contraposition (uses tempNecPast). -/
theorem H_distribution {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (allPast (HasImp.imp φ ψ))
        (HasImp.imp (allPast φ) (allPast ψ))) := by
  have neg_contra := neg_contrapositive_imp_neg (S := S) (φ := φ) (ψ := ψ)
  have h_nc := TemporalNecessitation.tempNecPast neg_contra
  have bx3h := HasAxiomRightMonoSince.rightMonoSince (S := S)
    (φ := neg' (HasImp.imp (neg' ψ) (neg' φ)))
    (ψ := neg' (HasImp.imp φ ψ))
    (χ := top')
  have P_step := ModusPonens.mp bx3h h_nc
  have H_contra := contraposition P_step
  have bx3h' := HasAxiomRightMonoSince.rightMonoSince (S := S)
    (φ := neg' ψ) (ψ := neg' φ) (χ := top')
  have cp := contrapose_imp (S := S)
    (φ := somePast (neg' ψ)) (ψ := somePast (neg' φ))
  have HK := imp_trans bx3h' cp
  exact imp_trans H_contra HK

/-! ### G/H Contraposition -/

/-- `⊢ G(φ→ψ) → G(¬ψ→¬φ)`. -/
theorem G_contrapose {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (allFuture (HasImp.imp φ ψ))
        (allFuture (HasImp.imp (neg' ψ) (neg' φ)))) := by
  have neg_contra := neg_contrapositive_imp_neg (S := S) (φ := φ) (ψ := ψ)
  have g_nc := TemporalNecessitation.tempNec neg_contra
  have bx3 := HasAxiomRightMonoUntil.rightMonoUntil (S := S)
    (φ := neg' (HasImp.imp (neg' ψ) (neg' φ)))
    (ψ := neg' (HasImp.imp φ ψ))
    (χ := top')
  exact contraposition (ModusPonens.mp bx3 g_nc)

/-- `⊢ H(φ→ψ) → H(¬ψ→¬φ)`. -/
theorem H_contrapose {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (allPast (HasImp.imp φ ψ))
        (allPast (HasImp.imp (neg' ψ) (neg' φ)))) := by
  have neg_contra := neg_contrapositive_imp_neg (S := S) (φ := φ) (ψ := ψ)
  have h_nc := TemporalNecessitation.tempNecPast neg_contra
  have bx3h := HasAxiomRightMonoSince.rightMonoSince (S := S)
    (φ := neg' (HasImp.imp (neg' ψ) (neg' φ)))
    (ψ := neg' (HasImp.imp φ ψ))
    (χ := top')
  exact contraposition (ModusPonens.mp bx3h h_nc)

/-! ### G/H Conjunction Introduction -/

/-- `⊢ Gφ → Gψ → G(φ∧ψ)`. -/
theorem G_and_intro {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (allFuture φ) (HasImp.imp (allFuture ψ) (allFuture (HasImp.imp (HasImp.imp φ (neg' ψ)) HasBot.bot)))) := by
  have g_pair := TemporalNecessitation.tempNec (@pairing F _ _ S _ _ φ ψ)
  have step1 := ModusPonens.mp (G_distribution (S := S)) g_pair
  exact imp_trans step1 (G_distribution (S := S))

/-- `⊢ Hφ → Hψ → H(φ∧ψ)`. -/
theorem H_and_intro {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (allPast φ) (HasImp.imp (allPast ψ) (allPast (HasImp.imp (HasImp.imp φ (neg' ψ)) HasBot.bot)))) := by
  have h_pair := TemporalNecessitation.tempNecPast (@pairing F _ _ S _ _ φ ψ)
  have step1 := ModusPonens.mp (H_distribution (S := S)) h_pair
  exact imp_trans step1 (H_distribution (S := S))

/-! ### G/H Implication Transitivity -/

/-- `⊢ G(φ→ψ) → G(ψ→χ) → G(φ→χ)`. -/
theorem G_imp_trans' {φ ψ χ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (allFuture (HasImp.imp φ ψ)) (HasImp.imp (allFuture (HasImp.imp ψ χ)) (allFuture (HasImp.imp φ χ)))) := by
  have g_b := TemporalNecessitation.tempNec (@b_combinator F _ _ S _ _ (φ := φ) (ψ := ψ) (χ := χ))
  have step1 := ModusPonens.mp (G_distribution (S := S)) g_b
  have step2 := imp_trans step1 (G_distribution (S := S))
  -- step2 : G(ψ→χ) → G(φ→ψ) → G(φ→χ). Flip to get the right order.
  exact ModusPonens.mp
    (@theorem_flip F _ _ S _ _
      (φ := allFuture (HasImp.imp ψ χ))
      (ψ := allFuture (HasImp.imp φ ψ))
      (χ := allFuture (HasImp.imp φ χ)))
    step2

/-- `⊢ H(φ→ψ) → H(ψ→χ) → H(φ→χ)`. -/
theorem H_imp_trans' {φ ψ χ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (allPast (HasImp.imp φ ψ)) (HasImp.imp (allPast (HasImp.imp ψ χ)) (allPast (HasImp.imp φ χ)))) := by
  have h_b := TemporalNecessitation.tempNecPast (@b_combinator F _ _ S _ _ (φ := φ) (ψ := ψ) (χ := χ))
  have step1 := ModusPonens.mp (H_distribution (S := S)) h_b
  have step2 := imp_trans step1 (H_distribution (S := S))
  exact ModusPonens.mp
    (@theorem_flip F _ _ S _ _
      (φ := allPast (HasImp.imp ψ χ))
      (ψ := allPast (HasImp.imp φ ψ))
      (χ := allPast (HasImp.imp φ χ)))
    step2

/-! ### Level 4: Future-Past Interaction Chains -/

/-- `⊢ Gφ → G(G(Pφ))`. -/
theorem connect_future_G {φ : F} :
    InferenceSystem.DerivableIn S (HasImp.imp (allFuture φ) (allFuture (allFuture (somePast φ)))) := by
  have g_conn := TemporalNecessitation.tempNec (@connect_future_thm F _ _ _ _ S _ _ (φ := φ))
  exact ModusPonens.mp (G_distribution (S := S)) g_conn

/-- `⊢ Hφ → H(H(Fφ))`. -/
theorem connect_past_H {φ : F} :
    InferenceSystem.DerivableIn S (HasImp.imp (allPast φ) (allPast (allPast (someFuture φ)))) := by
  have h_conn := TemporalNecessitation.tempNecPast (@connect_past_thm F _ _ _ _ S _ _ (φ := φ))
  exact ModusPonens.mp (H_distribution (S := S)) h_conn

end -- section

end Cslib.Logic.Theorems.Temporal.TemporalDerived
