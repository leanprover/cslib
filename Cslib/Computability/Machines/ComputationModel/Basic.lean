/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
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

/-- Bundle of a type `σ` with a step function `σ → Option σ`. -/
class TransitionModel (τ : Type*) where
  σ (a : τ) : Type
  step {a : τ} : σ a → Option (σ a)

/-- An abstract version of a turing machine with input alphabet `Γ₀` and output alphabet `Γ₁`. -/
class TransitionComputer (τ : Type*) (Γ₀ Γ₁ : Type) extends TransitionModel τ where
  init {a : τ} : List Γ₀ → σ a
  output {a : τ} : σ a → List Γ₁

notation "σ[" x "]" => TransitionModel.σ x


namespace TransitionModel

variable {τ : Type*} [TransitionModel τ]

def stepRelation (tm : τ) : (Option σ[tm]) → (Option σ[tm]) → Prop
  | a, b => a.bind step = b

/-- A "proof" of the fact that `f` eventually reaches `b` when repeatedly evaluated on `a`,
remembering the number of steps it takes. -/
structure EvalsTo (tm : τ) (a b : Option σ[tm]) where
  steps : ℕ
  evals : (flip bind step)^[steps] a = b

structure EvalsToInTime (tm : τ) (a b : Option σ[tm]) (n : ℕ) extends EvalsTo tm a b where
  steps_le : steps ≤ n

variable {tm : τ} {a b c : Option σ[tm]} {n n₁ n₂ : ℕ}

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


end TransitionModel

namespace TransitionComputer

variable {τ : Type*} {Γ₀ Γ₁ : Type} [TransitionComputer τ Γ₀ Γ₁]

structure Outputs (tm : τ) (l : List Γ₀) (l' : List Γ₁) where
  haltState : σ[tm]
  haltState_halts : TransitionModel.step haltState = none
  evalsTo : TransitionModel.EvalsTo tm (some (init l)) (some haltState)
  output_eq : output haltState =  l'

structure OutputsInTime (tm : τ) (n : ℕ) (l : List Γ₀) (l' : List Γ₁) where
  haltState : σ[tm]
  haltState_halts : TransitionModel.step haltState = none
  evals_to : TransitionModel.EvalsToInTime tm (some (init l)) (some haltState) n
  output_eq : output haltState =  l'

def OutputsInTime.of_le {tm : τ} {n m : ℕ} {l : List Γ₀} {l' : List Γ₁} (hnm : n ≤ m)
    (hv : OutputsInTime tm n l l') : OutputsInTime tm m l l' where
  haltState := hv.haltState
  haltState_halts := hv.haltState_halts
  evals_to := TransitionModel.EvalsToInTime.of_le hv.evals_to hnm
  output_eq := hv.output_eq

lemma OutputsInTime.output_unique {tm : τ} {n₁ n₂ : ℕ} {l : List Γ₀} {l'₁ l'₂ : List Γ₁}
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

end TransitionComputer


end Turing
