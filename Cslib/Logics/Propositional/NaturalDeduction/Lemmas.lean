/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Foundations.Logic.InferenceSystem.Basic

/-! # Auxilliary results on natural deduction

In this file we prove the expected results that `ND₁ T` is always intuitionistic, and that various
axiomatisations of classical logic (`CPL Atom` using double-negation elimination, `LEM Atom` using
the law of excluded middle, and `Peirce Atom` using Peirce's law) are classical inference systems.
We provide derived rules for common intuitionistic and classical proof patterns.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL.NaturalDeduction

variable {Atom : Type u} [DecidableEq Atom] {T : Set (Proposition Atom)}

open Proposition InferenceSystem DerivableIn IsIntuitionistic IsClassical Derivation

/-! ### Classes of inference systems -/

instance instIsIntuitionisticND₁ : IsIntuitionistic (ND₁ T) (Proposition Atom) where
  derivationBotImp A := ass (A := ⊥) |>.efq A |>.impI

/-- Derivation of efq in an arbitrary context. -/
def derivBotImpCtx (Γ : Ctx Atom) (A : Proposition Atom) : (ND T)⇓(Γ ⊢ ⊥ → A) :=
  (derivationBotImp A : (ND₁ T)⇓(⊥ → A)).weakCtx

/-- Prove any proposition from contradictory hypotheses. -/
def contra {Γ : Ctx Atom} (A B : Proposition Atom)
    (hΓ : A ∈ Γ := by membership) (hΓ' : (¬A) ∈ Γ := by membership) : (ND T)⇓(Γ ⊢ B) :=
  efq B <| impE (A := A) ass ass

instance instIsClassicalCPL : IsClassical (ND₁ <| CPL Atom) (Proposition Atom) where
  derivationDNE A := ax

/-- Proof by contradiction as a derived rule. -/
def byContra [IsClassical (ND₁ T) (Proposition Atom)] {Γ : Ctx Atom}
    {A : Proposition Atom} (D : (ND T)⇓(insert (¬ A) Γ ⊢ ⊥)) : (ND T)⇓(Γ ⊢ A) :=
  impE (derivationDNE A : (ND₁ T)⇓(¬¬A → A)).weakCtx D.impI

/-- Law of excluded middle in a classical theory. -/
def lem [IsClassical (ND₁ T) (Proposition Atom)] (A : Proposition Atom) : (ND₁ T)⇓(A ∨ ¬ A) := by
  apply byContra
  apply impE (A := A ∨ ¬ A) ass
  apply orI₂; apply impI
  exact impE (A := A ∨ ¬ A) ass (orI₁ ass)

/-- Peirce's law in a classical theory. -/
def peirce [IsClassical (ND₁ T) (Proposition Atom)] (A B : Proposition Atom) :
    (ND₁ T)⇓(((A → B) → A) → A) := by
  apply impI; apply byContra
  apply impE (A := A) ass
  apply impE (A := A → B) ass
  exact impI _ <| contra A B

instance instIsClassicalLEM : IsClassical (ND₁ <| LEM Atom) (Proposition Atom) where
  derivationDNE A := by
    apply impI
    apply orE (A := A) (B := ¬ A) ax ass
    apply impE (A := ⊥) (derivBotImpCtx _ A)
    apply impE (A := ¬ A) ass ass

instance instIsClassicalPeirce : IsClassical (ND₁ <| Peirce Atom) (Proposition Atom) where
  derivationDNE A := by
    apply impI
    apply impE (A := (A → ⊥) → A) ax
    apply impI
    apply contra (A := ¬A)

/-! ### Further operations on deductions -/

/-- Move the axioms used in a derivation `D` to the context, obtaining a derivation in
intuitionistic logic. -/
def Derivation.collectAx {Γ : Ctx Atom} {B : Proposition Atom} :
    (Derivation T Γ B) → Σ Δ : {Δ : Ctx Atom // ↑Δ ⊆ T}, Derivation (IPL Atom) (Γ ∪ Δ) B
  | @ax _ _ _ _ B _ => ⟨⟨{B}, by grind⟩, ass⟩
  | ass _ => ⟨⟨∅, by grind⟩, ass⟩
  | efq A D => let ⟨Δ, D'⟩ := D.collectAx; ⟨Δ, D'.efq A⟩
  | andI D E =>
    let ⟨Δ₁, D'⟩ := collectAx D
    let ⟨Δ₂, E'⟩ := collectAx E
    ⟨⟨Δ₁ ∪ Δ₂, by grind⟩, andI D'.weakCtx E'.weakCtx⟩
  | andE₁ D => let ⟨Δ, D'⟩ := collectAx D; ⟨Δ, andE₁ D'⟩
  | andE₂ D => let ⟨Δ, D'⟩ := collectAx D; ⟨Δ, andE₂ D'⟩
  | orI₁ D => let ⟨Δ, D'⟩ := collectAx D; ⟨Δ, orI₁ D'⟩
  | orI₂ D => let ⟨Δ, D'⟩ := collectAx D; ⟨Δ, orI₂ D'⟩
  | orE D E₁ E₂ =>
    let ⟨Δ, D'⟩ := collectAx D
    let ⟨Δ₁, E₁'⟩ := collectAx E₁
    let ⟨Δ₂, E₂'⟩ := collectAx E₂
    ⟨⟨Δ ∪ Δ₁ ∪ Δ₂, by grind⟩, orE D'.weakCtx E₁'.weakCtx E₂'.weakCtx⟩
  | impI Γ D => let ⟨Δ, D'⟩ := collectAx D; ⟨Δ, impI (Γ ∪ Δ) D'.weakCtx⟩
  | impE D E =>
    let ⟨Δ₁, D'⟩ := collectAx D
    let ⟨Δ₂, E'⟩ := collectAx E
    ⟨⟨Δ₁ ∪ Δ₂, by grind⟩, impE (D'.weakCtx) (E'.weakCtx)⟩

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.collect_ax {Γ : Ctx Atom}
    {B : Proposition Atom} : DerivableIn (ND T) (Γ ⊢ B) →
      ∃ Δ : Ctx Atom, DerivableIn (ND <| IPL Atom) ((Γ ∪ Δ) ⊢ B) ∧ ↑Δ ⊆ T
  | ⟨D⟩ => let ⟨⟨Δ, hΔ⟩, D'⟩ := D.collectAx; ⟨Δ, ⟨⟨D'⟩, hΔ⟩⟩

/-- Remove some assumptions by moving them to the theory. -/
def Derivation.assToAx' {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    Derivation T Γ B → Derivation (T ∪ Δ) (Γ \ Δ) B
  | @ass _ _ _ _ B _ => by
    by_cases B ∈ Δ
    case pos => exact ax
    case neg => exact ass
  | ax _ => ax
  | efq A D => D.assToAx'.efq A
  | andI D E => andI (assToAx' D) (assToAx' E)
  | andE₁ D => andE₁ (assToAx' D)
  | andE₂ D => andE₂ (assToAx' D)
  | orI₁ D => orI₁ (assToAx' D)
  | orI₂ D => orI₂ (assToAx' D)
  | @orE _ _ _ _ A' B C D E₁ E₂ =>
    orE (assToAx' D)
      (assToAx' (Δ := Δ) (B := C) E₁).weakCtx
      (assToAx' (Δ := Δ) (B := C) E₂).weakCtx
  | @impI _ _ _ A' B _ D => impI _ (assToAx' (Δ := Δ) (B := B) D).weakCtx
  | impE D E => impE (assToAx' D) (assToAx' E)

/-- Remove dependence on some assumptions by adding them to the theory. -/
def Derivation.assToAx {Γ Δ : Ctx Atom} {B : Proposition Atom}
    (D : Derivation T (Γ ∪ Δ) B) : Derivation (T ∪ Δ) Γ B := (assToAx' D).weakCtx

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.ass_to_ax {Γ Δ : Ctx Atom}
    {B : Proposition Atom} : DerivableIn (ND T) ((Γ ∪ Δ) ⊢ B) → DerivableIn (ND <| T ∪ Δ) (Γ ⊢ B)
  | ⟨D⟩ => ⟨Derivation.assToAx D⟩

/-- Move a finset of axioms to the context. -/
def Derivation.axToAss {Γ Δ : Ctx Atom} {B : Proposition Atom}
    (D : (ND <| T ∪ Δ)⇓(Γ ⊢ B)) : (ND T)⇓((Γ ∪ Δ) ⊢ B) :=
  let ⟨⟨Δ', hΔ'⟩, D'⟩ := collectAx D
  (D'.assToAx' (Δ := Δ' \ Δ)).weak (by grind)

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.ax_to_ass {Γ Δ : Ctx Atom}
    {B : Proposition Atom} : DerivableIn (ND <| T ∪ Δ) (Γ ⊢ B) → DerivableIn (ND T) ((Γ ∪ Δ) ⊢ B)
  | ⟨D⟩ => ⟨D.axToAss⟩

theorem derivableIn_union_theory_iff_ctx {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    DerivableIn (ND <| T ∪ Δ) (Γ ⊢ B) ↔ DerivableIn (ND T) ((Γ ∪ Δ) ⊢ B) :=
  ⟨ax_to_ass, ass_to_ax⟩

theorem derivableIn_iff_exists {Γ : Ctx Atom} {B : Proposition Atom} :
    DerivableIn (ND T) (Γ ⊢ B) ↔
      ∃ Δ : Ctx Atom, DerivableIn (ND <| IPL Atom) ((Γ ∪ Δ) ⊢ B) ∧ ↑Δ ⊆ T :=
  ⟨collect_ax, fun ⟨Δ, h, hsub⟩ ↦ h.ass_to_ax.weak_theory⟩

theorem derivableIn_nd₁_iff_exists {A : Proposition Atom} :
    DerivableIn (ND₁ T) A ↔ ∃ Γ : Ctx Atom, DerivableIn (ND <| IPL Atom) (Γ ⊢ A) ∧ ↑Γ ⊆ T := by
  rw [nd₁_iff_derivableIn_nd_empty, derivableIn_iff_exists]
  simp

end Cslib.Logic.PL.NaturalDeduction
