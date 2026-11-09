/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.Combinators

/-! # Ordering of inference systems -/

@[expose] public section

namespace Cslib.Logic.InferenceSystem

section Ordering

variable {S₁ S₂ S₃ α : Type*} [InferenceSystem S₁ α] [InferenceSystem S₂ α] [InferenceSystem S₃ α]

variable (S₁ S₂) in
structure Embedding where
  mapDerivation {a : α} (D : S₁⇓a) : S₂⇓a

namespace Embedding

variable (S₁) in
protected def refl : Embedding S₁ S₁ where
  mapDerivation D := D

protected def trans (e₁ : Embedding S₁ S₂) (e₂ : Embedding S₂ S₃) : Embedding S₁ S₃ where
  mapDerivation D := e₂.mapDerivation (e₁.mapDerivation D)

@[implicit_reducible]
def hasEFQ [HasImp α] [Bot α] [h : HasEFQ S₁ α] (e : Embedding S₁ S₂) :
    HasEFQ S₂ α where
  botImp a := e.mapDerivation (h.botImp a)

@[implicit_reducible]
def isClassical [HasImp α] [HasNot α] [h : HasDNE S₁ α] (e : Embedding S₁ S₂) :
    HasDNE S₂ α where
  dne a := e.mapDerivation (h.dne a)

@[implicit_reducible]
def hasLEM [HasOr α] [HasNot α] [h : HasLEM S₁ α] (e : Embedding S₁ S₂) :
    HasLEM S₂ α where
  lem a := e.mapDerivation (h.lem a)

@[implicit_reducible]
def hasPierce [HasImp α] [h : HasPierce S₁ α] (e : Embedding S₁ S₂) :
    HasPierce S₂ α where
  pierce a b := e.mapDerivation (h.pierce a b)

end Embedding

variable (S₁ S₂) in
structure WeakerThan where
  mapDerivableIn {a : α} (h : DerivableIn S₁ a) : DerivableIn S₂ a

lemma Embedding.weakerThan (e : Embedding S₁ S₂) : WeakerThan S₁ S₂ where
  mapDerivableIn h := ⟨e.mapDerivation h.some⟩

noncomputable def WeakerThan.embedding (h : WeakerThan S₁ S₂) : Embedding S₁ S₂ where
  mapDerivation D := (h.mapDerivableIn ⟨D⟩).some

theorem weakerThan_iff_nonempty_embedding : WeakerThan S₁ S₂ ↔ Nonempty (Embedding S₁ S₂) :=
  ⟨fun h ↦ ⟨h.embedding⟩, fun ⟨h⟩ ↦ h.weakerThan⟩

variable (S₁ S₂) in
structure IsEquivalent where
  derivableIn_iff (a : α) : DerivableIn S₁ a ↔ DerivableIn S₂ a

lemma IsEquivalent.refl : IsEquivalent S₁ S₁ where
  derivableIn_iff _ := .rfl

lemma IsEquivalent.symm (h₁ : IsEquivalent S₁ S₂) : IsEquivalent S₂ S₁ where
  derivableIn_iff a := (h₁.derivableIn_iff a).symm

lemma IsEquivalent.trans (h₁ : IsEquivalent S₁ S₂) (h₂ : IsEquivalent S₂ S₃) :
    IsEquivalent S₁ S₃ where
  derivableIn_iff a := (h₁.derivableIn_iff a).trans (h₂.derivableIn_iff a)

lemma IsEquivalent.weakerThan_left (h : IsEquivalent S₁ S₂) : WeakerThan S₁ S₂ where
  mapDerivableIn := (h.derivableIn_iff _).mp

lemma IsEquivalent.weakerThan_right (h : IsEquivalent S₁ S₂) : WeakerThan S₂ S₁ where
  mapDerivableIn := (h.derivableIn_iff _).mpr

theorem isEquivalent_iff_weakerThan : IsEquivalent S₁ S₂ ↔ WeakerThan S₁ S₂ ∧ WeakerThan S₂ S₁ :=
  ⟨fun h ↦ ⟨h.weakerThan_left, h.weakerThan_right⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨fun _ ↦ ⟨h₁.mapDerivableIn, h₂.mapDerivableIn⟩⟩⟩

end Ordering

end Cslib.Logic.InferenceSystem
