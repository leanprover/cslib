/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.ProofSystem.Derivation
public import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
public import Cslib.Logics.Bimodal.Theorems.Propositional.Connectives
public import Cslib.Logics.Bimodal.Theorems.Combinators
public import Cslib.Logics.Bimodal.Theorems.Perpetuity.Bridge
public import Cslib.Logics.Bimodal.Theorems.TemporalDerived

/-!
# Lindenbaum Quotient Construction

Quotient of formulas by provable equivalence forming the Lindenbaum-Tarski algebra.

Ported from BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean
(2 sorries: temp_k_dist in provEquiv_allFuture_congr -- now resolved using derived theorem)
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Algebraic.LindenbaumQuotient

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-- `φ` derives `ψ` when there exists a derivation tree for `φ → ψ` from no hypotheses. -/
def Derives (φ ψ : Formula Atom) : Prop := Nonempty (DerivationTree FrameClass.Base [] (φ.imp ψ))

/-- Two formulas are provably equivalent when each derives the other. -/
def ProvEquiv (φ ψ : Formula Atom) : Prop := Derives φ ψ ∧ Derives ψ φ

scoped infix:50 " ≈ₚ " => ProvEquiv

/-- Derivability is reflexive: every formula derives itself via the identity combinator. -/
theorem derives_refl (φ : Formula Atom) : Derives φ φ := by
  unfold Derives
  exact ⟨Theorems.Combinators.identity φ⟩

/-- Provable equivalence is reflexive. -/
theorem provEquiv_refl (φ : Formula Atom) : φ ≈ₚ φ :=
  ⟨derives_refl φ, derives_refl φ⟩

/-- Provable equivalence is symmetric. -/
theorem provEquiv_symm {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) : ψ ≈ₚ φ :=
  ⟨h.2, h.1⟩

/-- Derivability is transitive via implication transitivity. -/
theorem derives_trans {φ ψ χ : Formula Atom} (h1 : Derives φ ψ) (h2 : Derives ψ χ) :
    Derives φ χ := by
  unfold Derives at *
  obtain ⟨d1⟩ := h1
  obtain ⟨d2⟩ := h2
  exact ⟨Theorems.Combinators.impTrans d1 d2⟩

/-- Provable equivalence is transitive. -/
theorem provEquiv_trans {φ ψ χ : Formula Atom} (h1 : φ ≈ₚ ψ) (h2 : ψ ≈ₚ χ) : φ ≈ₚ χ :=
  ⟨derives_trans h1.1 h2.1, derives_trans h2.2 h1.2⟩

/-- Provable equivalence forms an equivalence relation. -/
theorem provEquiv_equiv : Equivalence (ProvEquiv (Atom := Atom)) where
  refl := provEquiv_refl
  symm := provEquiv_symm
  trans := provEquiv_trans

/-- Setoid instance for formulas under provable equivalence. -/
instance provEquivSetoid : Setoid (Formula Atom) where
  r := ProvEquiv
  iseqv := provEquiv_equiv

/-- The Lindenbaum-Tarski algebra: formulas quotiented by provable equivalence. -/
def LindenbaumAlg (Atom : Type*) : Type _ := Quotient (provEquivSetoid (Atom := Atom))

/-- Canonical quotient map sending a formula to its equivalence class. -/
def toQuot (φ : Formula Atom) : LindenbaumAlg Atom := Quotient.mk provEquivSetoid φ

scoped notation "⟦" φ "⟧" => toQuot φ

/-- Negation is antitone with respect to derivability: if `ψ` derives `φ`, then `¬φ` derives `¬ψ`. -/
theorem derives_neg_antitone {φ ψ : Formula Atom} (h : Derives ψ φ) : Derives φ.neg ψ.neg := by
  unfold Derives at *
  obtain ⟨d⟩ := h
  exact ⟨Theorems.Propositional.contraposition d⟩

/-- Negation respects provable equivalence. -/
theorem provEquiv_neg_congr {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) : φ.neg ≈ₚ ψ.neg := by
  unfold ProvEquiv at *
  exact ⟨derives_neg_antitone h.2, derives_neg_antitone h.1⟩

/-- Box modality respects provable equivalence, using necessitation and K axiom. -/
theorem provEquiv_box_congr {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) : φ.box ≈ₚ ψ.box := by
  unfold ProvEquiv Derives at *
  obtain ⟨⟨d_fwd⟩, ⟨d_bwd⟩⟩ := h
  constructor
  · have d_box := DerivationTree.necessitation (φ.imp ψ) d_fwd
    have d_k := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.modal_k_dist φ ψ) trivial
    exact ⟨DerivationTree.modus_ponens [] _ _ d_k d_box⟩
  · have d_box := DerivationTree.necessitation (ψ.imp φ) d_bwd
    have d_k := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.modal_k_dist ψ φ) trivial
    exact ⟨DerivationTree.modus_ponens [] _ _ d_k d_box⟩

/-- The G (allFuture) modality respects provable equivalence, using temporal necessitation. -/
theorem provEquiv_allFuture_congr {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) :
    φ.allFuture ≈ₚ ψ.allFuture := by
  unfold ProvEquiv Derives at *
  obtain ⟨⟨d_fwd⟩, ⟨d_bwd⟩⟩ := h
  constructor
  · have d_temp := DerivationTree.temporal_necessitation (φ.imp ψ) d_fwd
    have d_k := Theorems.TemporalDerived.tempKDistDerived φ ψ
    exact ⟨DerivationTree.modus_ponens [] _ _ d_k d_temp⟩
  · have d_temp := DerivationTree.temporal_necessitation (ψ.imp φ) d_bwd
    have d_k := Theorems.TemporalDerived.tempKDistDerived ψ φ
    exact ⟨DerivationTree.modus_ponens [] _ _ d_k d_temp⟩

/-- The H (allPast) modality respects provable equivalence. -/
theorem provEquiv_allPast_congr {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) :
    φ.allPast ≈ₚ ψ.allPast := by
  unfold ProvEquiv Derives at *
  obtain ⟨⟨d_fwd⟩, ⟨d_bwd⟩⟩ := h
  constructor
  · exact ⟨Theorems.Perpetuity.pastMono d_fwd⟩
  · exact ⟨Theorems.Perpetuity.pastMono d_bwd⟩

/-- Implication respects provable equivalence in both arguments. -/
theorem provEquiv_imp_congr {φ₁ φ₂ ψ₁ ψ₂ : Formula Atom}
    (hφ : φ₁ ≈ₚ φ₂) (hψ : ψ₁ ≈ₚ ψ₂) : φ₁.imp ψ₁ ≈ₚ φ₂.imp ψ₂ := by
  unfold ProvEquiv Derives at *
  obtain ⟨⟨d_φ_fwd⟩, ⟨d_φ_bwd⟩⟩ := hφ
  obtain ⟨⟨d_ψ_fwd⟩, ⟨d_ψ_bwd⟩⟩ := hψ
  constructor
  · have b1 : DerivationTree FrameClass.Base [] ((ψ₁.imp ψ₂).imp ((φ₂.imp ψ₁).imp (φ₂.imp ψ₂))) :=
      Theorems.Combinators.bCombinator
    have h1 := DerivationTree.modus_ponens [] _ _ b1 d_ψ_fwd
    have b2_pre : DerivationTree FrameClass.Base [] ((φ₁.imp ψ₁).imp ((φ₂.imp φ₁).imp (φ₂.imp ψ₁))) :=
      Theorems.Combinators.bCombinator
    have flip2 : DerivationTree FrameClass.Base []
        (((φ₁.imp ψ₁).imp ((φ₂.imp φ₁).imp (φ₂.imp ψ₁))).imp
         ((φ₂.imp φ₁).imp ((φ₁.imp ψ₁).imp (φ₂.imp ψ₁)))) :=
      Theorems.Combinators.flip
    have b2 := DerivationTree.modus_ponens [] _ _ flip2 b2_pre
    have h2 := DerivationTree.modus_ponens [] _ _ b2 d_φ_bwd
    exact ⟨Theorems.Combinators.impTrans h2 h1⟩
  · have b1 : DerivationTree FrameClass.Base [] ((ψ₂.imp ψ₁).imp ((φ₁.imp ψ₂).imp (φ₁.imp ψ₁))) :=
      Theorems.Combinators.bCombinator
    have h1 := DerivationTree.modus_ponens [] _ _ b1 d_ψ_bwd
    have b2_pre : DerivationTree FrameClass.Base [] ((φ₂.imp ψ₂).imp ((φ₁.imp φ₂).imp (φ₁.imp ψ₂))) :=
      Theorems.Combinators.bCombinator
    have flip2 : DerivationTree FrameClass.Base []
        (((φ₂.imp ψ₂).imp ((φ₁.imp φ₂).imp (φ₁.imp ψ₂))).imp
         ((φ₁.imp φ₂).imp ((φ₂.imp ψ₂).imp (φ₁.imp ψ₂)))) :=
      Theorems.Combinators.flip
    have b2 := DerivationTree.modus_ponens [] _ _ flip2 b2_pre
    have h2 := DerivationTree.modus_ponens [] _ _ b2 d_φ_fwd
    exact ⟨Theorems.Combinators.impTrans h2 h1⟩

/-- Conjunction respects provable equivalence. -/
theorem provEquiv_and_congr {φ₁ φ₂ ψ₁ ψ₂ : Formula Atom}
    (hφ : φ₁ ≈ₚ φ₂) (hψ : ψ₁ ≈ₚ ψ₂) : φ₁.and ψ₁ ≈ₚ φ₂.and ψ₂ := by
  have hψ_neg := provEquiv_neg_congr hψ
  have h_imp := provEquiv_imp_congr hφ hψ_neg
  exact provEquiv_neg_congr h_imp

/-- Disjunction respects provable equivalence. -/
theorem provEquiv_or_congr {φ₁ φ₂ ψ₁ ψ₂ : Formula Atom}
    (hφ : φ₁ ≈ₚ φ₂) (hψ : ψ₁ ≈ₚ ψ₂) : φ₁.or ψ₁ ≈ₚ φ₂.or ψ₂ := by
  have hφ_neg := provEquiv_neg_congr hφ
  exact provEquiv_imp_congr hφ_neg hψ

/-- Negation lifted to the Lindenbaum algebra quotient. -/
noncomputable def negQuot : LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift (fun φ => toQuot φ.neg)
    (fun _ _ h => Quotient.sound (provEquiv_neg_congr h))

/-- Implication lifted to the Lindenbaum algebra quotient. -/
noncomputable def impQuot : LindenbaumAlg Atom → LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift₂ (fun φ ψ => toQuot (φ.imp ψ))
    (fun _ _ _ _ h1 h2 => Quotient.sound (provEquiv_imp_congr h1 h2))

/-- Conjunction lifted to the Lindenbaum algebra quotient. -/
noncomputable def andQuot : LindenbaumAlg Atom → LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift₂ (fun φ ψ => toQuot (φ.and ψ))
    (fun _ _ _ _ h1 h2 => Quotient.sound (provEquiv_and_congr h1 h2))

/-- Disjunction lifted to the Lindenbaum algebra quotient. -/
noncomputable def orQuot : LindenbaumAlg Atom → LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift₂ (fun φ ψ => toQuot (φ.or ψ))
    (fun _ _ _ _ h1 h2 => Quotient.sound (provEquiv_or_congr h1 h2))

/-- Box modality lifted to the Lindenbaum algebra quotient. -/
noncomputable def boxQuot : LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift (fun φ => toQuot φ.box)
    (fun _ _ h => Quotient.sound (provEquiv_box_congr h))

/-- The G (allFuture) operator lifted to the Lindenbaum algebra quotient. -/
noncomputable def G_quot : LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift (fun φ => toQuot φ.allFuture)
    (fun _ _ h => Quotient.sound (provEquiv_allFuture_congr h))

/-- The H (allPast) operator lifted to the Lindenbaum algebra quotient. -/
noncomputable def H_quot : LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift (fun φ => toQuot φ.allPast)
    (fun _ _ h => Quotient.sound (provEquiv_allPast_congr h))

/-- Top element of the Lindenbaum algebra, represented by `⊥ → ⊥` (i.e., `⊤`). -/
def topQuot : LindenbaumAlg Atom := toQuot (Formula.bot.imp Formula.bot)
/-- Bottom element of the Lindenbaum algebra, represented by `⊥`. -/
def botQuot : LindenbaumAlg Atom := toQuot Formula.bot

/-- Temporal duality (swapping G/H) preserves derivability. -/
theorem swapTemporal_derives {φ ψ : Formula Atom} (h : Derives φ ψ) :
    Derives φ.swapTemporal ψ.swapTemporal := by
  unfold Derives at *
  obtain ⟨d⟩ := h
  have d_swap := DerivationTree.temporal_duality (φ.imp ψ) d
  simp only [Formula.swapTemporal] at d_swap
  exact ⟨d_swap⟩

/-- Temporal swap respects provable equivalence. -/
theorem provEquiv_swapTemporal_congr {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) :
    φ.swapTemporal ≈ₚ ψ.swapTemporal :=
  ⟨swapTemporal_derives h.1, swapTemporal_derives h.2⟩

/-- Temporal swap (sigma involution) lifted to the Lindenbaum algebra quotient. -/
noncomputable def sigmaQuot : LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift (fun φ => toQuot φ.swapTemporal)
    (fun _ _ h => Quotient.sound (provEquiv_swapTemporal_congr h))

/-- The sigma quotient operation is an involution: applying it twice is the identity. -/
theorem sigma_quot_involution (a : LindenbaumAlg Atom) : sigmaQuot (sigmaQuot a) = a := by
  induction a using Quotient.ind
  rename_i φ
  show toQuot (φ.swapTemporal.swapTemporal) = toQuot φ
  rw [Formula.swapTemporal_involution]

/-- Sigma commutes with negation on the Lindenbaum algebra. -/
theorem sigma_quot_neg (a : LindenbaumAlg Atom) :
    sigmaQuot (negQuot a) = negQuot (sigmaQuot a) := by
  induction a using Quotient.ind
  rename_i φ
  show toQuot (φ.neg.swapTemporal) = negQuot (toQuot (φ.swapTemporal))
  simp only [Formula.neg, Formula.swapTemporal]
  rfl

/-- Sigma distributes over disjunction (supremum) on the Lindenbaum algebra. -/
theorem sigma_quot_sup (a b : LindenbaumAlg Atom) :
    sigmaQuot (orQuot a b) = orQuot (sigmaQuot a) (sigmaQuot b) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  show toQuot ((φ.or ψ).swapTemporal) = orQuot (toQuot φ.swapTemporal) (toQuot ψ.swapTemporal)
  simp only [Formula.or, Formula.neg, Formula.swapTemporal]
  rfl

/-- Sigma maps G to H: `σ(G a) = H(σ a)`. -/
theorem sigma_quot_G_H (a : LindenbaumAlg Atom) :
    sigmaQuot (G_quot a) = H_quot (sigmaQuot a) := by
  induction a using Quotient.ind
  rename_i φ
  show toQuot (φ.allFuture.swapTemporal) = H_quot (toQuot φ.swapTemporal)
  simp only [Formula.swapTemporal_allFuture]
  rfl

/-- Sigma maps H to G: `σ(H a) = G(σ a)`. -/
theorem sigma_quot_H_G (a : LindenbaumAlg Atom) :
    sigmaQuot (H_quot a) = G_quot (sigmaQuot a) := by
  induction a using Quotient.ind
  rename_i φ
  show toQuot (φ.allPast.swapTemporal) = G_quot (toQuot φ.swapTemporal)
  simp only [Formula.swapTemporal_allPast]
  rfl

/-- Sigma commutes with box: `σ(□ a) = □(σ a)`. -/
theorem sigma_quot_box (a : LindenbaumAlg Atom) :
    sigmaQuot (boxQuot a) = boxQuot (sigmaQuot a) := by
  induction a using Quotient.ind
  rename_i φ
  show toQuot (φ.box.swapTemporal) = boxQuot (toQuot φ.swapTemporal)
  simp only [Formula.swapTemporal]
  rfl

end Cslib.Logic.Bimodal.Metalogic.Algebraic.LindenbaumQuotient
