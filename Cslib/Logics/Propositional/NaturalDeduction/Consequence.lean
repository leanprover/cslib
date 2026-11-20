/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Foundations.Logic.ConsequenceRelation

/-! # Consequence in natural deduction

Derivability from an arbitrary set of premises in natural deduction for propositional logic, as a
consequence relation (`IsConsequence`).

## Main definitions

- `Cslib.Logic.PL.NaturalDeduction.Derives`: derivability from a set of premises.
-/

@[expose] public section

namespace Cslib.Logic.PL.NaturalDeduction

open InferenceSystem

variable {Atom : Type*} [DecidableEq Atom] {T : Set (Proposition Atom)}

/-- Derivability from a set of premises: some finite subset of the premises derives the
conclusion. -/
def Derives (T Γ : Set (Proposition Atom)) (A : Proposition Atom) : Prop :=
  ∃ Δ : Ctx Atom, ↑Δ ⊆ Γ ∧ DerivableIn (ND T) (Δ ⊢ A)

/-- Finitely many consequences of a set of premises are derivable from a single finite subset. -/
private theorem Derives.exists_ctx {Γ : Set (Proposition Atom)} {Δ : Ctx Atom}
    (h : ∀ B ∈ Δ, Derives T Γ B) :
    ∃ Γ₀ : Ctx Atom, ↑Γ₀ ⊆ Γ ∧ ∀ B ∈ Δ, DerivableIn (ND T) (Γ₀ ⊢ B) := by
  induction Δ using Finset.induction with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert B Δ₁ _ ih =>
    obtain ⟨Γ₁, hΓ₁, hΔ₁⟩ := ih fun C hC => h C (Finset.mem_insert_of_mem hC)
    obtain ⟨Γ₂, hΓ₂, hB⟩ := h B (Finset.mem_insert_self B Δ₁)
    refine ⟨Γ₁ ∪ Γ₂, by simp [hΓ₁, hΓ₂], fun C hC => ?_⟩
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact hB.weakCtx Finset.subset_union_right
    · exact (hΔ₁ C hC).weakCtx Finset.subset_union_left

instance : IsConsequence (Derives T) where
  of_mem {Γ A} h := ⟨{A}, by simpa using h, ⟨.ass (Finset.mem_singleton_self A)⟩⟩
  trans {Γ Δ A} h₁ := by
    rintro ⟨Δ₀, hΔ₀, hA⟩
    obtain ⟨Γ₀, hΓ₀, hall⟩ := Derives.exists_ctx fun B hB => h₁ B (hΔ₀ hB)
    exact ⟨Γ₀, hΓ₀, DerivableIn.cut_away hall (hA.weakCtx Finset.subset_union_right)⟩

end Cslib.Logic.PL.NaturalDeduction
