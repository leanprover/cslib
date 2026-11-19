/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.InferenceSystem.Defs
public import Cslib.Foundations.Logic.Operators

/-! # API for inference systems -/

@[expose] public section

namespace Cslib.Logic.InferenceSystem

/-- Intuitionistic inference systems derive the principle of explosion. -/
class IsIntuitionistic (S α : Type*) [Bot α] [HasImp α] [InferenceSystem S α] where
  /-- A chosen derivation of `⊥ → a`. -/
  derivationBotImp (a : α) : S⇓(⊥ → a)

lemma derivableIn_bot_imp {S α : Type*} [Bot α] [HasImp α] [InferenceSystem S α]
    [IsIntuitionistic S α] (a : α) : DerivableIn S (⊥ → a) :=
  ⟨IsIntuitionistic.derivationBotImp a⟩

/-- Classical inference systems derive double-negation elimination. -/
class IsClassical (S α : Type*) [HasNot α] [HasImp α] [InferenceSystem S α] where
  /-- A chosen derivation of `¬¬a → a`. -/
  derivationDNE (a : α) : S⇓(¬¬a → a)

lemma derivableIn_dne {S α : Type*} [HasNot α] [HasImp α] [InferenceSystem S α]
    [IsClassical S α] (a : α) : DerivableIn S (¬¬a → a) :=
  ⟨IsClassical.derivationDNE a⟩

end Cslib.Logic.InferenceSystem
