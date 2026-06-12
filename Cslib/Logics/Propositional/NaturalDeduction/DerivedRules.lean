/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Std.Tactic.BVDecide.Normalize

/-! # Derived Rules for Natural Deduction

This module provides derived introduction and elimination rules for the
Lukasiewicz-encoded propositional connectives (negation, top, conjunction,
disjunction, biconditional) in the standalone natural deduction system
(`Theory.Derivation` with `Finset` contexts).

## Main Definitions

### Negation
- `negI`: Negation introduction (wrapper for `impI`)
- `negE`: Negation elimination (wrapper for `impE`)

### Verum
- `topI`: Top introduction

### Conjunction
- `andI`: Conjunction introduction
- `andE1`: Left conjunction elimination (requires `[IsClassical T]`)
- `andE2`: Right conjunction elimination (requires `[IsClassical T]`)

### Disjunction
- `orI1`: Left disjunction introduction
- `orI2`: Right disjunction introduction
- `orE`: Disjunction elimination (requires `[IsClassical T]`)

### Double Negation Elimination
- `dne`: Double negation elimination (requires `[IsClassical T]`)

### Biconditional
- `iffI`: Biconditional introduction
- `iffE1`: Left biconditional elimination (requires `[IsClassical T]`)
- `iffE2`: Right biconditional elimination (requires `[IsClassical T]`)

### Prop-level Wrappers
All rules have `DerivableIn`-level versions with the suffix `DerivableIn`.

## Design

All rules are computable (the ND system's `impI` is a primitive constructor).
Elimination rules for conjunction, disjunction, and biconditional require
`[IsClassical T]` because the Lukasiewicz encoding of these connectives
is only classically equivalent to their standard definitions.

## References

* Cslib/Logics/Propositional/NaturalDeduction/Basic.lean -- standalone ND system
* Cslib/Logics/Propositional/Defs.lean -- connective definitions
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom]
variable {T : Theory Atom}
variable {Γ : Ctx Atom}
variable {A B C : Proposition Atom}

/-! ## Negation Rules -/

/-- **Negation Introduction** (negI): From `Gamma, A |- bot`, derive `Gamma |- neg A`.

Since `neg A := A -> bot`, this is simply implication introduction. -/
def Theory.Derivation.negI
    (d : T.Derivation (insert A Γ) ⊥) :
    T.Derivation Γ (¬A) :=
  Derivation.impI Γ d

/-- **Negation Elimination** (negE): From `Gamma |- neg A` and `Gamma |- A`,
derive `Gamma |- bot`.

Since `neg A := A -> bot`, this is simply implication elimination. -/
def Theory.Derivation.negE
    (d₁ : T.Derivation Γ (¬A))
    (d₂ : T.Derivation Γ A) :
    T.Derivation Γ ⊥ :=
  Derivation.impE d₁ d₂

/-! ## Verum -/

/-- **Top Introduction** (topI): `Gamma |- top` for any context.

Since `top := bot -> bot`, introduce the implication and use the assumption. -/
def Theory.Derivation.topI :
    T.Derivation Γ (⊤ : Proposition Atom) :=
  Derivation.impI Γ <| Derivation.ass <| by grind

/-! ## Conjunction Rules -/

/-- **Conjunction Introduction** (andI): From `Gamma |- A` and `Gamma |- B`,
derive `Gamma |- A and B`.

Since `A and B := (A -> (B -> bot)) -> bot`, we introduce the outer implication,
then apply the hypothesis `A -> (B -> bot)` to `A` and `B` to obtain `bot`. -/
def Theory.Derivation.andI
    (d₁ : T.Derivation Γ A)
    (d₂ : T.Derivation Γ B) :
    T.Derivation Γ (A ∧ B) := by
  -- Goal: Gamma |- (A -> (B -> bot)) -> bot
  -- A.and B unfolds to (A.imp (B.imp .bot)).imp .bot
  apply Derivation.impI Γ
  -- insert (A.imp (B.imp bot)) Gamma |- bot
  apply Derivation.impE (A := B)
  · apply Derivation.impE (A := A)
    · exact Derivation.ass (by simp [Finset.mem_insert])
    · exact d₁.weakCtx (by simp [Finset.subset_insert])
  · exact d₂.weakCtx (by simp [Finset.subset_insert])

/-- **Double Negation Elimination** (DNE): From `Gamma |- neg neg A`,
derive `Gamma |- A`.

Uses the classical axiom `(neg neg A -> A) in T` via `IsClassical.dne`. -/
def Theory.Derivation.dne [IsClassical T]
    (d : T.Derivation Γ (¬¬A)) :
    T.Derivation Γ A :=
  Derivation.impE (Derivation.ax (IsClassical.dne A)) d

/-- **Left Conjunction Elimination** (andE1): From `Gamma |- A and B`,
derive `Gamma |- A`.

Since `A and B := neg(A -> neg B)`, we derive `neg neg A` from the hypothesis
and apply double negation elimination.

Proof: Assume `neg A`. Then `A -> neg B` (from `neg A` and `A`, get `bot`,
then `neg B` by `impI`). But `neg(A -> neg B)`, contradiction. So `neg neg A`.
By DNE, `A`. -/
def Theory.Derivation.andE1 [IsClassical T]
    (d : T.Derivation Γ (A ∧ B)) :
    T.Derivation Γ A := by
  -- d : Gamma |- (A -> (B -> bot)) -> bot
  -- Show Gamma |- neg neg A, then apply dne
  apply Derivation.dne
  -- Goal: Gamma |- (A -> bot) -> bot, i.e., ¬¬A
  apply Derivation.negI (A := ¬A)
  -- insert (¬A) Gamma |- bot
  -- Apply d (weakened) to (A -> (B -> bot))
  -- where A -> (B -> bot) is: assume A, assume B, from ¬A and A get bot
  apply Derivation.impE (B := Proposition.bot)
  · exact d.weakCtx (by simp [Finset.subset_insert])
  · -- insert (¬A) Gamma |- A -> (B -> bot)
    apply Derivation.impI
    -- insert A (insert (¬A) Gamma) |- B -> bot
    apply Derivation.impI
    -- insert B (insert A (insert (¬A) Gamma)) |- bot
    -- Apply ¬A to A: negE
    apply Derivation.negE (A := A)
    · exact Derivation.ass (by simp [Finset.mem_insert])
    · exact Derivation.ass (by simp [Finset.mem_insert])

/-- **Right Conjunction Elimination** (andE2): From `Gamma |- A and B`,
derive `Gamma |- B`.

Since `A and B := neg(A -> neg B)`, we derive `neg neg B` from the hypothesis
and apply double negation elimination.

Proof: Assume `neg B`. Then `A -> neg B` (by weakening `neg B` under `A`).
But `neg(A -> neg B)`, contradiction. So `neg neg B`. By DNE, `B`. -/
def Theory.Derivation.andE2 [IsClassical T]
    (d : T.Derivation Γ (A ∧ B)) :
    T.Derivation Γ B := by
  -- d : Gamma |- (A -> (B -> bot)) -> bot
  -- Show Gamma |- neg neg B, then apply dne
  apply Derivation.dne
  -- Goal: Gamma |- (B -> bot) -> bot, i.e., ¬¬B
  apply Derivation.negI (A := ¬B)
  -- insert (¬B) Gamma |- bot
  -- Apply d (weakened) to A -> (B -> bot)
  -- where A -> (B -> bot) is derived by: assume A, then ¬B weakened
  apply Derivation.impE (B := Proposition.bot)
  · exact d.weakCtx (by simp [Finset.subset_insert])
  · -- insert (¬B) Gamma |- A -> (B -> bot)
    apply Derivation.impI
    -- insert A (insert (¬B) Gamma) |- B -> bot (= ¬B)
    -- ¬B is in the outer context, weaken into this one
    exact (Derivation.ass (by simp [Finset.mem_insert] : (¬B) ∈
      insert (¬B) Γ)).weakCtx (by simp [Finset.subset_insert])

/-! ## Disjunction Rules -/

/-- **Left Disjunction Introduction** (orI1): From `Gamma |- A`,
derive `Gamma |- A or B`.

Since `A or B := neg A -> B`, introduce the implication. From `neg A` and `A`,
derive `bot`, then `B` by ex falso. -/
def Theory.Derivation.orI1
    (d : T.Derivation Γ A) :
    T.Derivation Γ (A ∨ B) := by
  -- Goal: Gamma |- (A -> bot) -> B
  -- A.or B = (A.imp bot).imp B, so impI inserts (A.imp bot)
  apply Derivation.impI Γ
  -- insert (A.imp bot) Gamma |- B
  apply Derivation.botE
  -- insert (A.imp bot) Gamma |- bot
  apply Derivation.impE (A := A)
  · -- insert (A.imp bot) Gamma |- A -> bot = neg A
    exact Derivation.ass (Finset.mem_insert_self _ _)
  · exact d.weakCtx (Finset.subset_insert _ _)

/-- **Right Disjunction Introduction** (orI2): From `Gamma |- B`,
derive `Gamma |- A or B`.

Since `A or B := neg A -> B`, introduce the implication and weaken. -/
def Theory.Derivation.orI2
    (d : T.Derivation Γ B) :
    T.Derivation Γ (A ∨ B) :=
  -- Goal: Gamma |- (A -> bot) -> B
  Derivation.impI Γ (d.weakCtx (by simp [Finset.subset_insert]))

/-- **Disjunction Elimination** (orE): From `Gamma |- A or B`,
`Gamma, A |- C`, and `Gamma, B |- C`, derive `Gamma |- C`.

Uses classical reasoning. From `A -> C` (by impI on the A-case) and
`neg A -> C` (composing the disjunction `neg A -> B` with `B -> C`), derive `C`
by assuming `neg C`, contraposing `A -> C` to get `neg A`, then `C` from
`neg A -> C`, contradicting `neg C`. -/
def Theory.Derivation.orE [IsClassical T]
    (d : T.Derivation Γ (A ∨ B))
    (dA : T.Derivation (insert A Γ) C)
    (dB : T.Derivation (insert B Γ) C) :
    T.Derivation Γ C := by
  -- Step 1: Gamma |- A -> C
  have hAC : T.Derivation Γ (A → C) := Derivation.impI Γ dA
  -- Step 2: Gamma |- B -> C
  have hBC : T.Derivation Γ (B → C) := Derivation.impI Γ dB
  -- Step 3: Gamma |- ¬A -> C (compose d : ¬A -> B with hBC : B -> C)
  have hNAC : T.Derivation Γ (¬A → C) := by
    apply Derivation.impI Γ
    -- insert (¬A) Gamma |- C
    apply Derivation.impE (A := B)
    · exact hBC.weakCtx (by simp [Finset.subset_insert])
    · apply Derivation.impE (A := Proposition.neg A)
      · exact d.weakCtx (by simp [Finset.subset_insert])
      · exact Derivation.ass (by simp [Finset.mem_insert])
  -- Step 4: Apply DNE
  apply Derivation.dne
  -- Gamma |- ¬¬C
  apply Derivation.negI (A := Proposition.neg C)
  -- insert (¬C) Gamma |- bot
  -- Derive ¬A: assume A, derive C via hAC, but ¬C, contradiction
  have hContra : T.Derivation (insert (Proposition.neg C) Γ) (¬A) := by
    apply Derivation.negI
    -- insert A (insert (¬C) Gamma) |- bot
    apply Derivation.negE (A := C)
    · exact Derivation.ass (by simp [Finset.mem_insert])
    · apply Derivation.impE (A := A)
      · exact hAC.weakCtx (Finset.subset_insert _ _ |>.trans (Finset.subset_insert _ _))
      · exact Derivation.ass (by simp [Finset.mem_insert])
  -- Derive C from ¬A -> C and ¬A
  have hC : T.Derivation (insert (Proposition.neg C) Γ) C :=
    Derivation.impE
      (hNAC.weakCtx (by simp [Finset.subset_insert]))
      hContra
  -- ¬C applied to C gives bot
  exact Derivation.negE (A := C) (Derivation.ass (by simp [Finset.mem_insert])) hC

/-! ## Biconditional Rules -/

/-- **Biconditional Introduction** (iffI): From `Gamma |- A -> B` and
`Gamma |- B -> A`, derive `Gamma |- A iff B`.

Since `A iff B := (A -> B) and (B -> A)`, this is conjunction introduction
applied to the two implications. -/
def Theory.Derivation.iffI
    (d₁ : T.Derivation Γ (A → B))
    (d₂ : T.Derivation Γ (B → A)) :
    T.Derivation Γ (A ↔ B) :=
  Derivation.andI d₁ d₂

/-- **Left Biconditional Elimination** (iffE1): From `Gamma |- A iff B`,
derive `Gamma |- A -> B`.

Since `A iff B := (A -> B) and (B -> A)`, this is left conjunction elimination. -/
def Theory.Derivation.iffE1 [IsClassical T]
    (d : T.Derivation Γ (A ↔ B)) :
    T.Derivation Γ (A → B) :=
  Derivation.andE1 d

/-- **Right Biconditional Elimination** (iffE2): From `Gamma |- A iff B`,
derive `Gamma |- B -> A`.

Since `A iff B := (A -> B) and (B -> A)`, this is right conjunction elimination. -/
def Theory.Derivation.iffE2 [IsClassical T]
    (d : T.Derivation Γ (A ↔ B)) :
    T.Derivation Γ (B → A) :=
  Derivation.andE2 d

/-! ## DerivableIn-level Wrappers -/

/-- Negation introduction at the `DerivableIn` level. -/
theorem DerivableIn.negI
    (h : DerivableIn T ((insert A Γ) ⊢ (⊥ : Proposition Atom))) :
    DerivableIn T (Γ ⊢ ¬A) :=
  let ⟨d⟩ := h; ⟨d.negI⟩

/-- Negation elimination at the `DerivableIn` level. -/
theorem DerivableIn.negE
    (h₁ : DerivableIn T (Γ ⊢ ¬A))
    (h₂ : DerivableIn T (Γ ⊢ A)) :
    DerivableIn T (Γ ⊢ (⊥ : Proposition Atom)) :=
  let ⟨d₁⟩ := h₁; let ⟨d₂⟩ := h₂; ⟨d₁.negE d₂⟩

/-- Top introduction at the `DerivableIn` level. -/
theorem DerivableIn.topI :
    DerivableIn T (Γ ⊢ (⊤ : Proposition Atom)) :=
  ⟨Theory.Derivation.topI⟩

/-- Conjunction introduction at the `DerivableIn` level. -/
theorem DerivableIn.andI
    (h₁ : DerivableIn T (Γ ⊢ A))
    (h₂ : DerivableIn T (Γ ⊢ B)) :
    DerivableIn T (Γ ⊢ A ∧ B) :=
  let ⟨d₁⟩ := h₁; let ⟨d₂⟩ := h₂; ⟨d₁.andI d₂⟩

/-- Left conjunction elimination at the `DerivableIn` level. -/
theorem DerivableIn.andE1 [IsClassical T]
    (h : DerivableIn T (Γ ⊢ A ∧ B)) :
    DerivableIn T (Γ ⊢ A) :=
  let ⟨d⟩ := h; ⟨d.andE1⟩

/-- Right conjunction elimination at the `DerivableIn` level. -/
theorem DerivableIn.andE2 [IsClassical T]
    (h : DerivableIn T (Γ ⊢ A ∧ B)) :
    DerivableIn T (Γ ⊢ B) :=
  let ⟨d⟩ := h; ⟨d.andE2⟩

/-- Left disjunction introduction at the `DerivableIn` level. -/
theorem DerivableIn.orI1
    (h : DerivableIn T (Γ ⊢ A)) :
    DerivableIn T (Γ ⊢ A ∨ B) :=
  let ⟨d⟩ := h; ⟨d.orI1⟩

/-- Right disjunction introduction at the `DerivableIn` level. -/
theorem DerivableIn.orI2
    (h : DerivableIn T (Γ ⊢ B)) :
    DerivableIn T (Γ ⊢ A ∨ B) :=
  let ⟨d⟩ := h; ⟨d.orI2⟩

/-- Disjunction elimination at the `DerivableIn` level. -/
theorem DerivableIn.orE [IsClassical T]
    (h : DerivableIn T (Γ ⊢ A ∨ B))
    (hA : DerivableIn T ((insert A Γ) ⊢ C))
    (hB : DerivableIn T ((insert B Γ) ⊢ C)) :
    DerivableIn T (Γ ⊢ C) :=
  let ⟨d⟩ := h; let ⟨dA⟩ := hA; let ⟨dB⟩ := hB; ⟨d.orE dA dB⟩

/-- Double negation elimination at the `DerivableIn` level. -/
theorem DerivableIn.dne [IsClassical T]
    (h : DerivableIn T (Γ ⊢ ¬¬A)) :
    DerivableIn T (Γ ⊢ A) :=
  let ⟨d⟩ := h; ⟨d.dne⟩

/-- Biconditional introduction at the `DerivableIn` level. -/
theorem DerivableIn.iffI
    (h₁ : DerivableIn T (Γ ⊢ A → B))
    (h₂ : DerivableIn T (Γ ⊢ B → A)) :
    DerivableIn T (Γ ⊢ A ↔ B) :=
  let ⟨d₁⟩ := h₁; let ⟨d₂⟩ := h₂; ⟨d₁.iffI d₂⟩

/-- Left biconditional elimination at the `DerivableIn` level. -/
theorem DerivableIn.iffE1 [IsClassical T]
    (h : DerivableIn T (Γ ⊢ A ↔ B)) :
    DerivableIn T (Γ ⊢ A → B) :=
  let ⟨d⟩ := h; ⟨d.iffE1⟩

/-- Right biconditional elimination at the `DerivableIn` level. -/
theorem DerivableIn.iffE2 [IsClassical T]
    (h : DerivableIn T (Γ ⊢ A ↔ B)) :
    DerivableIn T (Γ ⊢ B → A) :=
  let ⟨d⟩ := h; ⟨d.iffE2⟩

end Cslib.Logic.PL
