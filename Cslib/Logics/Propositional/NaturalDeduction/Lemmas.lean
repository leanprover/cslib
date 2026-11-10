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
the law of excluded middle, and `Pierce Atom` using Pierce's law) are classical inference systems.
We provide derived rules for common intuitionistic and classical proof patterns.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL.NaturalDeduction

variable {Atom : Type u} [DecidableEq Atom] {T : Set (Proposition Atom)}

open Proposition InferenceSystem DerivableIn IsIntuitionistic IsClassical Derivation

instance instIsIntuitionisticND₁ : IsIntuitionistic (ND₁ T) (Proposition Atom) where
  derivationBotImp A := ass (A := ⊥) |>.efq A |>.impI

/-- Derivation of efq in an arbitrary context. -/
def derBotImpCtx (Γ : Ctx Atom) (A : Proposition Atom) : (ND T)⇓(Γ ⊢ ⊥ → A) :=
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

/-- Pierce's law in a classical theory. -/
def pierce [IsClassical (ND₁ T) (Proposition Atom)] (A B : Proposition Atom) :
    (ND₁ T)⇓(((A → B) → A) → A) := by
  apply impI; apply byContra
  apply impE (A := A) ass
  apply impE (A := A → B) ass
  exact impI _ <| contra A B

instance instIsClassicalLEM : IsClassical (ND₁ <| LEM Atom) (Proposition Atom) where
  derivationDNE A := by
    apply impI
    apply orE (A := A) (B := ¬ A) ax ass
    apply impE (A := ⊥) (derBotImpCtx _ A)
    apply impE (A := ¬ A) ass ass

instance instIsClassicalPierce : IsClassical (ND₁ <| Pierce Atom) (Proposition Atom) where
  derivationDNE A := by
    apply impI
    apply impE (A := (A → ⊥) → A) ax
    apply impI
    apply contra (A := ¬A)

end Cslib.Logic.PL.NaturalDeduction
