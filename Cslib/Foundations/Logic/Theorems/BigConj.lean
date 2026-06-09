/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Foundations.Logic.Theorems.Propositional.Core

/-! # Big Conjunction over Lists of Formulas

Defines `bigconj : List F → F` as a generic fold using
`HasBot.bot` and `HasImp.imp` (Lukasiewicz encoding of conjunction),
plus derivability lemmas for `[PropositionalHilbert S]`.

## Main Definitions

- `bigconj`: Big conjunction (`⊤` for empty, identity for singleton,
  nested conjunction for longer lists)
- `neg_bigconj`: Negation of big conjunction

## Main Results

- `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`: Simp lemmas
- `bigconj_mem_derivable`: If `φ ∈ L` and `⊢ bigconj L`,
  then `⊢ φ`
- `bigconj_derivable_intro`: If all members of `L` are derivable,
  then `⊢ bigconj L`

## Encoding

Conjunction uses the Lukasiewicz encoding:
`φ ∧ ψ := (φ → (ψ → ⊥)) → ⊥`
-/

namespace Cslib.Logic.Theorems.BigConj

set_option linter.style.longLine false

open Cslib.Logic

variable {F : Type*} [HasBot F] [HasImp F]

/-! ### Syntactic Definitions -/

/-- Big conjunction over a list of formulas.
    Base case: empty list folds to `⊤ := ⊥ → ⊥`.
    Singleton: just the formula.
    Longer: nested conjunction. -/
def bigconj : List F → F
  | [] => HasImp.imp HasBot.bot HasBot.bot
  | [φ] => φ
  | φ :: ψ :: rest =>
    HasImp.imp
      (HasImp.imp φ
        (HasImp.imp (bigconj (ψ :: rest)) HasBot.bot))
      HasBot.bot

/-- Negated big conjunction. -/
def neg_bigconj (L : List F) : F :=
  HasImp.imp (bigconj L) HasBot.bot

@[simp] theorem bigconj_nil :
    bigconj (F := F) [] =
      HasImp.imp HasBot.bot HasBot.bot := rfl

@[simp] theorem bigconj_singleton (φ : F) :
    bigconj [φ] = φ := rfl

@[simp] theorem bigconj_cons_cons (φ ψ : F)
    (rest : List F) :
    bigconj (φ :: ψ :: rest) =
      HasImp.imp
        (HasImp.imp φ
          (HasImp.imp (bigconj (ψ :: rest)) HasBot.bot))
        HasBot.bot := rfl

@[simp] theorem neg_bigconj_def (L : List F) :
    neg_bigconj L = HasImp.imp (bigconj L) HasBot.bot :=
  rfl

/-! ### Derivability Lemmas -/

variable {S : Type*} [InferenceSystem S F]
variable [PropositionalHilbert S (F := F)]

open Cslib.Logic.Theorems.Combinators
open Cslib.Logic.Theorems.Propositional.Core

noncomputable section

/-- If `φ ∈ L` and `⊢ bigconj L`, then `⊢ φ`. -/
theorem bigconj_mem_derivable {L : List F} {φ : F}
    (hmem : φ ∈ L)
    (hconj : InferenceSystem.DerivableIn S (bigconj L)) :
    InferenceSystem.DerivableIn S φ := by
  induction L with
  | nil => simp at hmem
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp [bigconj] at hconj
      simp at hmem
      rw [hmem]; exact hconj
    | cons b tail =>
      simp [bigconj] at hconj
      cases hmem with
      | head => exact ModusPonens.mp lce_imp hconj
      | tail _ hmem' =>
        have := ModusPonens.mp rce_imp hconj
        exact ih hmem' this

/-- If all members of `L` are derivable, then `⊢ bigconj L`. -/
theorem bigconj_derivable_intro {L : List F}
    (h : ∀ φ ∈ L, InferenceSystem.DerivableIn S φ) :
    InferenceSystem.DerivableIn S (bigconj L) := by
  induction L with
  | nil =>
    simp [bigconj]
    exact identity (S := S) HasBot.bot
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp [bigconj]
      exact h a (by simp)
    | cons b tail =>
      simp [bigconj]
      have ha := h a (by simp)
      have hrest : ∀ φ ∈ (b :: tail),
          InferenceSystem.DerivableIn S φ := by
        intro φ hmem
        exact h φ (by simp [hmem])
      have ih_result := ih hrest
      have pair := pairing (S := S) a (bigconj (b :: tail))
      exact ModusPonens.mp
        (ModusPonens.mp pair ha) ih_result

end -- noncomputable section

end Cslib.Logic.Theorems.BigConj
