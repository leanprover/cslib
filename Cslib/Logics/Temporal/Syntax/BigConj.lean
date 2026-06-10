/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Syntax.Formula

/-!
# Big Conjunction over Lists of Formulas

Defines `bigconj : List (Formula Atom) → Formula Atom` folding conjunction over a list,
with base case `⊤` (represented as `¬⊥`, i.e. `Formula.neg Formula.bot`), plus the derived
negation `negBigconj`.

## Main Definitions

- `bigconj : List (Formula Atom) → Formula Atom`
- `negBigconj : List (Formula Atom) → Formula Atom`
-/

@[expose] public section

namespace Cslib.Logic.Temporal

variable {Atom : Type u}

/-- Big conjunction over a list of formulas: `bigconj [φ₁, …, φₙ] = φ₁ ∧ … ∧ φₙ`.
    Base case: the empty list folds to `⊤`, represented as `¬⊥ = bot.imp bot`. -/
def bigconj : List (Formula Atom) → Formula Atom
  | []      => Formula.neg Formula.bot  -- `⊤` = `¬⊥`
  | [φ]     => φ
  | φ :: ψ :: rest => Formula.and φ (bigconj (ψ :: rest))

/-- Negated big conjunction. -/
def negBigconj (L : List (Formula Atom)) : Formula Atom := (bigconj L).neg

@[simp] theorem bigconj_nil :
    bigconj (Atom := Atom) [] = Formula.neg Formula.bot := rfl

@[simp] theorem bigconj_singleton (φ : Formula Atom) :
    bigconj [φ] = φ := rfl

@[simp] theorem bigconj_cons_cons (φ ψ : Formula Atom) (rest : List (Formula Atom)) :
    bigconj (φ :: ψ :: rest) = Formula.and φ (bigconj (ψ :: rest)) := rfl

@[simp] theorem negBigconj_def (L : List (Formula Atom)) :
    negBigconj L = (bigconj L).neg := rfl

end Cslib.Logic.Temporal
