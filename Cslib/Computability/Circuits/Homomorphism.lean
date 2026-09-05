/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuits.Signature

/-!
# Homomorphisms of interpretations

A homomorphism between two interpretations of the same signature is a map of
carriers that commutes with every operation. This file defines identity and
composition and proves their laws.

The main use of homomorphisms in this library is that evaluation of lines,
programs, and circuits commutes with them (`Line.map_eval`, `Program.map_eval`,
`Program.map_trace`, and `Circuit.map_eval`).
-/

@[expose] public section

namespace Cslib.Circuits

universe v u u₁ u₂ u₃ u₄

variable {σ : Signature.{v}} {U : Type u}
variable {U₁ : Type u₁} {U₂ : Type u₂} {U₃ : Type u₃} {U₄ : Type u₄}

/-- A map that preserves every operation in a pair of interpretations. -/
structure Homomorphism (i₁ : Interpretation σ U₁) (i₂ : Interpretation σ U₂) where
  /-- The underlying map. -/
  map : U₁ → U₂
  /-- The map commutes with every operation in the signature. -/
  homomorphic :
    ∀ (op : σ.Op) (input : Fin (σ.Arity op) → U₁),
      map (i₁ op input) = i₂ op (map ∘ input)

namespace Homomorphism

@[ext] theorem ext
    {source : Interpretation σ U₁}
    {target : Interpretation σ U₂}
    {left right : Homomorphism source target}
    (map_eq : left.map = right.map) : left = right := by
  cases left
  cases right
  cases map_eq
  rfl

/-- The identity map is a homomorphism. -/
def id (interpretation : Interpretation σ U) :
    Homomorphism interpretation interpretation where
  map := _root_.id
  homomorphic := by
    intro op input
    rfl

/-- Compose homomorphisms in the direction of their underlying maps. -/
def comp
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    {i₃ : Interpretation σ U₃}
    (outer : Homomorphism i₂ i₃)
    (inner : Homomorphism i₁ i₂) : Homomorphism i₁ i₃ where
  map := outer.map ∘ inner.map
  homomorphic := by
    intro op input
    rw [Function.comp_apply, inner.homomorphic, outer.homomorphic]
    congr 1

@[simp] theorem id_map
    (interpretation : Interpretation σ U) :
    (Homomorphism.id interpretation).map = _root_.id := rfl

@[simp] theorem comp_map
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    {i₃ : Interpretation σ U₃}
    (outer : Homomorphism i₂ i₃)
    (inner : Homomorphism i₁ i₂) :
    (outer.comp inner).map = outer.map ∘ inner.map := rfl

@[simp] theorem id_comp
    {source : Interpretation σ U₁}
    {target : Interpretation σ U₂}
    (homomorphism : Homomorphism source target) :
    (Homomorphism.id target).comp homomorphism = homomorphism := by
  apply Homomorphism.ext
  rfl

@[simp] theorem comp_id
    {source : Interpretation σ U₁}
    {target : Interpretation σ U₂}
    (homomorphism : Homomorphism source target) :
    homomorphism.comp (Homomorphism.id source) = homomorphism := by
  apply Homomorphism.ext
  rfl

theorem comp_assoc
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    {i₃ : Interpretation σ U₃}
    {i₄ : Interpretation σ U₄}
    (outer : Homomorphism i₃ i₄)
    (middle : Homomorphism i₂ i₃)
    (inner : Homomorphism i₁ i₂) :
    (outer.comp middle).comp inner = outer.comp (middle.comp inner) := by
  apply Homomorphism.ext
  rfl

end Homomorphism

end Cslib.Circuits
