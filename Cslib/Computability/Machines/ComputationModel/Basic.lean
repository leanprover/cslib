/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Foundations.Data.RelatesInSteps
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Logic.Function.Iterate

/-! # Transition Based Computation Models


-/

@[expose] public section

namespace Turing

/-- Bundle of a type `cfg` with a step function `cfg → Option cfg`. -/
class TransitionSystem (τ : Type*) where
  cfg (a : τ) : Type*
  step {a : τ} : cfg a → Option (cfg a)

/-- An abstract version of a turing machine with input alphabet `Γ₀` and output alphabet `Γ₁`. -/
class Transducer (τ : Type*) (Γᵢₙ Γₒᵤₜ : Type) extends TransitionSystem τ where
  init {a : τ} : List Γᵢₙ → cfg a
  output {a : τ} : cfg a → List Γₒᵤₜ


namespace TransitionSystem

variable {τ : Type*} [TransitionSystem τ]

def stepRelation (tm : τ) : (Option (cfg tm)) → (Option (cfg tm)) → Prop
  | a, b => a.bind step = b

/-- A "proof" of the fact that `f` eventually reaches `b` when repeatedly evaluated on `a`,
remembering the number of steps it takes. -/
structure EvalsTo (tm : τ) (a b : Option (cfg tm)) where
  steps : ℕ
  evals : (flip bind step)^[steps] a = b

structure EvalsToInTime (tm : τ) (a b : Option (cfg tm)) (n : ℕ) extends EvalsTo tm a b where
  steps_le : steps ≤ n

variable {tm : τ} {a b c : Option (cfg tm)} {n n₁ n₂ : ℕ}

def EvalsTo.refl : EvalsTo tm a a where
  steps := 0
  evals := rfl

def EvalsTo.trans (h₁ : EvalsTo tm a b) (h₂ : EvalsTo tm b c) : EvalsTo tm a c where
  steps := h₂.steps + h₁.steps
  evals := by rw [Function.iterate_add_apply, h₁.evals, h₂.evals]

def EvalsToInTime.refl : EvalsToInTime tm a a 0 where
  toEvalsTo := EvalsTo.refl
  steps_le := by rfl

def EvalsToInTime.trans (h₁ : EvalsToInTime tm a b n₁) (h₂ : EvalsToInTime tm b c n₂) :
    EvalsToInTime tm a c (n₂ + n₁) where
  toEvalsTo := EvalsTo.trans h₁.toEvalsTo h₂.toEvalsTo
  steps_le := add_le_add h₂.steps_le h₁.steps_le

def EvalsToInTime.of_le (h : EvalsToInTime tm a b n₁) (hn : n₁ ≤ n₂) :
    EvalsToInTime tm a b n₂ where
  toEvalsTo := h.toEvalsTo
  steps_le := le_trans h.steps_le hn


end TransitionSystem

namespace Transducer
open TransitionSystem

variable {τ : Type*} {Γᵢₙ Γₒᵤₜ : Type} [Transducer τ Γᵢₙ Γₒᵤₜ]

structure Outputs (tm : τ) (l : List Γᵢₙ) (l' : List Γₒᵤₜ) where
  haltState : (cfg tm)
  haltState_halts : TransitionSystem.step haltState = none
  evalsTo : TransitionSystem.EvalsTo tm (some (init l)) (some haltState)
  output_eq : output haltState =  l'

structure OutputsInTime (tm : τ) (n : ℕ) (l : List Γᵢₙ) (l' : List Γₒᵤₜ) where
  haltState : (cfg tm)
  haltState_halts : TransitionSystem.step haltState = none
  evals_to : TransitionSystem.EvalsToInTime tm (some (init l)) (some haltState) n
  output_eq : output haltState =  l'

def OutputsInTime.of_le {tm : τ} {n m : ℕ} {l : List Γᵢₙ} {l' : List Γₒᵤₜ} (hnm : n ≤ m)
    (hv : OutputsInTime tm n l l') : OutputsInTime tm m l l' where
  haltState := hv.haltState
  haltState_halts := hv.haltState_halts
  evals_to := TransitionSystem.EvalsToInTime.of_le hv.evals_to hnm
  output_eq := hv.output_eq

lemma OutputsInTime.output_unique {tm : τ} {n₁ n₂ : ℕ} {l : List Γᵢₙ} {l'₁ l'₂ : List Γₒᵤₜ}
    (ho₁ : OutputsInTime tm n₁ l l'₁) (ho₂ : OutputsInTime tm n₂ l l'₂) :
    l'₁ = l'₂ := by
  wlog hle : ho₁.evals_to.steps ≤ ho₂.evals_to.steps
  · symm
    exact this ho₂ ho₁ (Nat.le_of_not_le hle)
  · have : ho₁.evals_to.steps = ho₂.evals_to.steps := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hle
      cases d with
      | zero => symm; simpa using hd
      | succ d' =>
          have := ho₂.evals_to.evals
          rw [hd, Function.iterate_add_apply, ho₁.evals_to.evals,
            Function.iterate_succ_apply, Option.bind_eq_bind, flip, Option.bind_some,
            ho₁.haltState_halts, Function.iterate_fixed rfl] at this
          contradiction
    have : ho₁.haltState = ho₂.haltState := by
      apply Option.some.inj
      rw [← ho₁.evals_to.evals, ← ho₂.evals_to.evals, this]
    rw [← ho₁.output_eq, ← ho₂.output_eq, this]

end Transducer


end Turing
