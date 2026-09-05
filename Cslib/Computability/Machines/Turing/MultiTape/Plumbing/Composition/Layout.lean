/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Composition.Defs

/-! # Relating the composition tape layout to injected work tapes -/

@[expose] public section

namespace Turing.MultiTapeTM.Composition

variable {k₀ k₁ : ℕ} {α : Type*}

/-- Extending the output machine yields the first block and the middle tape. -/
lemma extend_output (first : Fin k₀ → α) (middle : α) (second : Fin k₁ → α)
    (dummyFirst : Fin k₀ → α) (dummyMiddle : α) :
    ExtendTapes.extend (outputEmbedding k₀ k₁) (Fin.lastCases middle first)
      (tapes dummyFirst dummyMiddle second) = tapes first middle second := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change ExtendTapes.extend (outputEmbedding k₀ k₁) _ _ (outputEmbedding k₀ k₁ j) = _
    rw [ExtendTapes.extend_apply]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [tapes]
    · simp [tapes]
  · have hj : Fin.natAdd (k₀ + 1) j ∉ Set.range (outputEmbedding k₀ k₁) := by
      rintro ⟨a, ha⟩
      have := congrArg Fin.val ha
      simp only [outputEmbedding, Function.Embedding.coeFn_mk,
        Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    simp [ExtendTapes.extend, hj, tapes, show ¬k₀ + 1 + j.val < k₀ by omega,
      show k₀ + 1 + j.val ≠ k₀ by omega]

/-- Extending the input machine preserves the first block and fills the remaining tapes. -/
lemma extend_input (first : Fin k₀ → α) (middle : α) (second : Fin k₁ → α)
    (dummyMiddle : α) (dummySecond : Fin k₁ → α) :
    ExtendTapes.extend (inputEmbedding k₀ k₁) (Fin.cases middle second)
      (tapes first dummyMiddle dummySecond) = tapes first middle second := by
  funext i
  by_cases hi : i.val < k₀
  · have hn : i ∉ Set.range (inputEmbedding k₀ k₁) := by
      rintro ⟨a, ha⟩
      have := congrArg Fin.val ha
      change k₀ + a.val = i.val at this
      omega
    simp [ExtendTapes.extend, hn, tapes, hi]
  · let j : Fin (k₁ + 1) := ⟨i.val - k₀, by
      have := i.isLt
      dsimp [compositionTapeCount] at *
      omega⟩
    have hj : inputEmbedding k₀ k₁ j = i :=
      Fin.ext (by change k₀ + (i.val - k₀) = i.val; omega)
    rw [← hj, ExtendTapes.extend_apply]
    generalize j = a
    refine Fin.cases ?_ (fun a => ?_) a
    · simp [tapes]
    · simp only [Fin.cases_succ, tapes, inputEmbedding_val, Fin.val_succ,
        add_lt_iff_neg_left, not_lt_zero, ↓reduceDIte, Nat.add_eq_left,
        Nat.add_eq_zero_iff, one_ne_zero, and_false]
      congr 1
      apply Fin.ext
      simp
      omega

/-- A constant frame supplies the unused second tape block. -/
lemma extend_output_const (first : Fin k₀ → α) (middle d : α) :
    ExtendTapes.extend (outputEmbedding k₀ k₁) (Fin.lastCases middle first) (fun _ => d) =
      tapes first middle (fun _ => d) := by
  have hconst : tapes (fun _ : Fin k₀ => d) d (fun _ : Fin k₁ => d) = (fun _ => d) := by
    funext i
    simp [tapes]
  rw [← hconst]
  exact extend_output first middle (fun _ => d) (fun _ => d) d

end Turing.MultiTapeTM.Composition
