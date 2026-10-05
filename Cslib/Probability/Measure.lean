/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.UniformOn
public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Measure and kernel utilities

Small consequences of Mathlib's uniform measures, kernel composition, and posterior API.
General probability interfaces use `Measure` and `Kernel`; finite sampling uses `uniformOn`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Cslib.Probability.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Sample randomness and apply a jointly measurable deterministic computation. -/
noncomputable def sampleKernel {Randomness : Type*} [MeasurableSpace Randomness]
    (μ : Measure Randomness) (f : Randomness → α → β)
    (hf : Measurable (Function.uncurry f)) : Kernel α β :=
  Kernel.deterministic (Function.uncurry f) hf ∘ₖ (Kernel.const α μ ×ₖ Kernel.id)

@[simp]
theorem sampleKernel_apply {Randomness : Type*} [MeasurableSpace Randomness]
    (μ : Measure Randomness) [SFinite μ] (f : Randomness → α → β)
    (hf : Measurable (Function.uncurry f)) (a : α) :
    sampleKernel μ f hf a = μ.map (fun r => f r a) := by
  simp [sampleKernel, Kernel.comp_apply, Kernel.prod_apply, Kernel.id_apply,
    Measure.deterministic_comp_eq_map, Measure.prod_dirac,
    Measure.map_map hf measurable_prodMk_right, Function.comp_def]

instance {Randomness : Type*} [MeasurableSpace Randomness]
    (μ : Measure Randomness) [IsProbabilityMeasure μ] (f : Randomness → α → β)
    (hf : Measurable (Function.uncurry f)) : IsMarkovKernel (sampleKernel μ f hf) := by
  unfold sampleKernel
  infer_instance

/-- Uniform probability measure on a nonempty finite type. -/
noncomputable abbrev uniformOfFintype (α : Type*) [MeasurableSpace α]
    [Fintype α] [Nonempty α] : ProbabilityMeasure α :=
  (uniformOn (Set.univ : Set α)).toProbabilityMeasure

/-- Uniform sampling is invariant under an equivalence of finite discrete spaces. -/
theorem uniformOn_univ_map_equiv [Finite α] [Finite β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] (e : α ≃ β) :
    (uniformOn (Set.univ : Set α)).map e = uniformOn (Set.univ : Set β) := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_countable e) (measurableSet_singleton b)]
  have he : e ⁻¹' {b} = {e.symm b} := by
    ext a
    change e a = b ↔ a = e.symm b
    exact ⟨fun h => by simpa using congrArg e.symm h, fun h => by simp [h]⟩
  simp [he, uniformOn_univ, Fintype.card_congr e]

/-- An input-independent channel produces an independent joint distribution. -/
theorem compProd_eq_prod_of_outputIndist (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] (h : ∀ a₀ a₁, κ a₀ = κ a₁) :
    μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ) := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  obtain ⟨a⟩ := ‹Nonempty α›
  have hκ : κ = Kernel.const α (κ a) := Kernel.ext fun a' => h a' a
  rw [hκ]
  simp

/-- Independence leaves the prior unchanged almost surely under conditioning. -/
theorem posterior_eq_prior_of_compProd_eq_prod [StandardBorelSpace α] [Nonempty α]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    (h : μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ)) :
    posterior κ μ =ᵐ[κ ∘ₘ μ] fun _ => μ := by
  exact (ae_eq_posterior_of_compProd_eq (η := Kernel.const β μ) (by
    rw [h, Measure.compProd_const, Measure.prod_swap])).symm

end Cslib.Probability.Measure
