/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Composition

/-!
# Complexity of composed functions

Bounds depend on the actual input. Composition adds the component costs at `a` and `f a`, plus
the length of the encoded intermediate result. No monotonicity assumption is needed. Bounds on
encoded input length are recovered by weakening this pointwise statement.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ : Type*}

/-- Compose machine realizations of functions at their actual input-indexed bounds. -/
theorem comp_computesFunInTimeAndSpace
    {k₀ k₁ : ℕ} {Symbol State₀ State₁ : Type*}
    (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)
    {encA : α ↪ List Symbol} {encB : β ↪ List Symbol} {encC : γ ↪ List Symbol}
    {f : α → β} {g : β → γ} {tf sf : α → ℕ} {tg sg : β → ℕ}
    (hf : ComputesFunInTimeAndSpace tm₀ encA encB f tf sf)
    (hg : ComputesFunInTimeAndSpace tm₁ encB encC g tg sg) :
    ComputesFunInTimeAndSpace (comp tm₀ tm₁) encA encC (g ∘ f)
      (fun a => tf a + ((encB (f a)).length + 3) + 2 * tg (f a))
      (fun a => sf a + ((encB (f a)).length + 2) + sg (f a)) := by
  intro a
  obtain ⟨t₀, ht₀, s₀, hs₀, hc₀⟩ := hf a
  obtain ⟨t₁, ht₁, s₁, hs₁, hc₁⟩ := hg (f a)
  obtain ⟨t, ht, s, hs, hc⟩ := comp_computesInTimeAndSpace tm₀ tm₁ hc₀ hc₁
  exact ⟨t, by dsimp only; omega, s, by dsimp only; omega, hc⟩

/-- Function composition preserves computability, with explicit pointwise time and space bounds. -/
theorem computableInTimeAndSpace_comp
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {f : α → β} {g : β → γ} {tf sf : α → ℕ} {tg sg : β → ℕ}
    (hf : ComputableInTimeAndSpace f encA encB tf sf)
    (hg : ComputableInTimeAndSpace g encB encC tg sg) :
    ComputableInTimeAndSpace (g ∘ f) encA encC
      (fun a => tf a + ((encB (f a)).length + 3) + 2 * tg (f a))
      (fun a => sf a + ((encB (f a)).length + 2) + sg (f a)) := by
  obtain ⟨k₀, State₀, hfinite₀, tm₀, h₀⟩ := hf
  obtain ⟨k₁, State₁, hfinite₁, tm₁, h₁⟩ := hg
  let := Fintype.ofFinite State₀
  let := Fintype.ofFinite RewindState
  let := Fintype.ofFinite (InputState State₁)
  exact ⟨compositionTapeCount k₀ k₁, CompositionState State₀ State₁, inferInstance,
    comp tm₀ tm₁, comp_computesFunInTimeAndSpace tm₀ tm₁ h₀ h₁⟩

/-- Length-based bounds follow from the pointwise theorem and an intermediate-length bound. -/
theorem computableInTimeAndSpaceOfLength_comp
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {f : α → β} {g : β → γ} {tf sf tg sg L : ℕ → ℕ}
    (hf : ComputableInTimeAndSpaceOfLength f encA encB tf sf)
    (hg : ComputableInTimeAndSpaceOfLength g encB encC tg sg)
    (hL : ∀ a, (encB (f a)).length ≤ L (encA a).length)
    (htg : Monotone tg) (hsg : Monotone sg) :
    ComputableInTimeAndSpaceOfLength (g ∘ f) encA encC
      (fun n => tf n + (L n + 3) + 2 * tg (L n))
      (fun n => sf n + (L n + 2) + sg (L n)) := by
  apply (computableInTimeAndSpace_comp hf hg).mono
  · intro a
    have := hL a
    have := htg (hL a)
    dsimp only
    omega
  · intro a
    have := hL a
    have := hsg (hL a)
    dsimp only
    omega

end Turing.MultiTapeTM
