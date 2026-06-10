/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.FromHilbert

/-! # Derived Rules for the Hilbert System

This module provides derived introduction and elimination rules for the
Lukasiewicz-encoded propositional connectives (negation, top, conjunction,
disjunction, biconditional) in the Hilbert-style proof system
(`DerivationTree` with `List` contexts).

## Main Definitions

### Negation
- `negI`: Negation introduction (noncomputable, uses deduction theorem)
- `negE`: Negation elimination (computable, modus ponens)

### Verum
- `topI`: Top introduction (computable)

### Conjunction
- `andI`: Conjunction introduction (noncomputable)
- `andE1`: Left conjunction elimination (computable)
- `andE2`: Right conjunction elimination (computable)

### Disjunction
- `orI1`: Left disjunction introduction (noncomputable)
- `orI2`: Right disjunction introduction (computable)
- `orE`: Disjunction elimination (noncomputable)

### Double Negation Elimination
- `dne`: Double negation elimination (computable)

### Biconditional
- `iffI`: Biconditional introduction (noncomputable)
- `iffE1`: Left biconditional elimination (computable)
- `iffE2`: Right biconditional elimination (computable)

### Prop-level Wrappers
All rules have `Deriv`-level versions with the suffix `Deriv`.

## Design

Rules that use `impI` (the deduction theorem) are `noncomputable`.
Elimination rules that rely only on axioms + modus ponens are computable.
The Hilbert system has Peirce's law as a primitive axiom, so no `IsClassical`
constraint is needed.

## References

* `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` -- ND wrappers
* `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- Hilbert system
* `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- axiom schemata
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

variable {Atom : Type*}

/-! ## Negation Rules -/

/-- **Negation Introduction** (negI): From `A :: Gamma |- bot`, derive `Gamma |- neg A`.

Since `neg A := A -> bot`, this is `impI`. -/
noncomputable def hilbertNegI {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree (A :: Γ) Proposition.bot) :
    DerivationTree Γ (Proposition.neg A) :=
  impI d

/-- **Negation Elimination** (negE): From `Gamma |- neg A` and `Gamma |- A`,
derive `Gamma |- bot`.

Since `neg A := A -> bot`, this is `impE`. -/
def hilbertNegE {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d₁ : DerivationTree Γ (Proposition.neg A))
    (d₂ : DerivationTree Γ A) :
    DerivationTree Γ Proposition.bot :=
  impE d₁ d₂

/-! ## Verum -/

/-- **Top Introduction** (topI): `Gamma |- top` for any context.

Since `top := bot -> bot`, use EFQ at `bot` and weaken. -/
def hilbertTopI {Γ : List (PL.Proposition Atom)} :
    DerivationTree Γ (Proposition.top : PL.Proposition Atom) :=
  DerivationTree.weakening [] Γ _
    (DerivationTree.ax [] _ (.efq Proposition.bot))
    (fun _ h => nomatch h)

/-! ## Double Negation Elimination -/

/-- **Double Negation Elimination** (dne): From `Gamma |- neg neg A`,
derive `Gamma |- A`.

Uses Peirce(A, bot) to get ((A -> bot) -> A) -> A, then EFQ to get
bot -> A, then composes neg neg A = (A -> bot) -> bot with (bot -> A)
via the B-combinator to get (A -> bot) -> A, and applies Peirce. -/
def hilbertDne {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree Γ (Proposition.neg (Proposition.neg A))) :
    DerivationTree Γ A := by
  -- d : Gamma |- (A -> bot) -> bot
  -- Peirce(A, bot): ((A -> bot) -> A) -> A
  have peirce := DerivationTree.ax Γ _ (PropositionalAxiom.peirce A Proposition.bot)
  -- EFQ(A): bot -> A
  have efq := DerivationTree.ax Γ _ (PropositionalAxiom.efq A)
  -- ImplyS to compose: (A -> bot) -> bot with bot -> A gives (A -> bot) -> A
  -- Actually, use B-combinator pattern:
  -- S: (p -> (q -> r)) -> ((p -> q) -> (p -> r))
  -- We want (A -> bot) -> A.
  -- From d : (A -> bot) -> bot and efq : bot -> A
  -- ImplyK: (bot -> A) -> ((A -> bot) -> (bot -> A))
  -- so: (A -> bot) -> (bot -> A) from ImplyK applied to efq
  have k_efq := DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _
      (PropositionalAxiom.implyK (Proposition.bot.imp A)
        (A.imp Proposition.bot)))
    efq
  -- ImplyS at ((A -> bot) -> (bot -> A)) -> (((A -> bot) -> bot) -> ((A -> bot) -> A))
  -- S(A -> bot, bot, A):
  --   ((A->bot) -> (bot -> A)) -> (((A->bot) -> bot) -> ((A->bot) -> A))
  have s_ax := DerivationTree.ax Γ _
    (PropositionalAxiom.implyS (A.imp Proposition.bot) Proposition.bot A)
  -- Apply S to k_efq: ((A -> bot) -> bot) -> ((A -> bot) -> A)
  have composed := DerivationTree.modus_ponens Γ _ _ s_ax k_efq
  -- Apply to d: (A -> bot) -> A
  have imp_peirce := DerivationTree.modus_ponens Γ _ _ composed d
  -- Apply Peirce: A
  exact DerivationTree.modus_ponens Γ _ _ peirce imp_peirce

/-! ## Conjunction Rules -/

/-- **Conjunction Introduction** (andI): From `Gamma |- A` and `Gamma |- B`,
derive `Gamma |- A and B`.

Since `A and B := (A -> (B -> bot)) -> bot`, introduce the implication
using the deduction theorem, then apply the hypothesis. -/
noncomputable def hilbertAndI {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Γ A)
    (d₂ : DerivationTree Γ B) :
    DerivationTree Γ (A.and B) := by
  -- Goal: Gamma |- (A -> (B -> bot)) -> bot
  apply impI
  -- (A -> (B -> bot)) :: Gamma |- bot
  apply impE (A := B)
  · apply impE (A := A)
    · exact assume List.mem_cons_self
    · exact hilbertWeakening d₁ (fun x hx => List.mem_cons_of_mem _ hx)
  · exact hilbertWeakening d₂ (fun x hx => List.mem_cons_of_mem _ hx)

/-- **Left Conjunction Elimination** (andE1): From `Gamma |- A and B`,
derive `Gamma |- A`.

Uses Peirce(A, B -> bot) + EFQ composition. Since A and B = neg(A -> neg B),
we derive A from neg(A -> neg B) using:
1. Peirce(A, B -> bot): ((A -> (B -> bot)) -> A) -> A
2. EFQ(A -> (B -> bot)): bot -> (A -> (B -> bot)), which gives
   neg(A -> (B -> bot)) -> ((A -> (B -> bot)) -> A) via ImplyK pattern
3. Composition gives A. -/
def hilbertAndE1 {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Γ (A.and B)) :
    DerivationTree Γ A := by
  -- d : Gamma |- (A -> (B -> bot)) -> bot  (= neg (A -> neg B))
  -- Peirce(A, B -> bot): ((A -> B -> bot) -> A) -> A
  have peirce := DerivationTree.ax Γ _
    (PropositionalAxiom.peirce A (B.imp Proposition.bot))
  -- EFQ for the inner type: bot -> A
  have efq := DerivationTree.ax Γ _ (PropositionalAxiom.efq A)
  -- We need: (A -> (B -> bot)) -> A
  -- From d: neg(A -> neg B) = (A -> (B -> bot)) -> bot
  -- and efq: bot -> A
  -- Compose: (A -> (B -> bot)) -> A via S combinator on d and efq
  -- K(efq): (A -> (B -> bot)) -> (bot -> A)
  have k_efq := DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _
      (PropositionalAxiom.implyK (Proposition.bot.imp A) (A.imp (B.imp Proposition.bot))))
    efq
  -- S(A -> (B -> bot), bot, A)
  have s_ax := DerivationTree.ax Γ _
    (PropositionalAxiom.implyS (A.imp (B.imp Proposition.bot)) Proposition.bot A)
  -- S applied to k_efq: ((A -> B -> bot) -> bot) -> ((A -> B -> bot) -> A)
  have composed := DerivationTree.modus_ponens Γ _ _ s_ax k_efq
  -- Apply to d: (A -> B -> bot) -> A
  have result := DerivationTree.modus_ponens Γ _ _ composed d
  -- Apply Peirce: A
  exact DerivationTree.modus_ponens Γ _ _ peirce result

/-- **Right Conjunction Elimination** (andE2): From `Gamma |- A and B`,
derive `Gamma |- B`.

Uses Peirce(B, bot) + ImplyK to extract B from neg(A -> neg B).
Since A and B = (A -> (B -> bot)) -> bot:
1. ImplyK(B -> bot, A): (B -> bot) -> (A -> (B -> bot))
2. Compose with d: (B -> bot) -> bot = neg neg B
3. Apply dne: B. -/
def hilbertAndE2 {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Γ (A.and B)) :
    DerivationTree Γ B := by
  -- d : Gamma |- (A -> (B -> bot)) -> bot
  -- ImplyK(B -> bot, A): (B -> bot) -> (A -> (B -> bot))
  have k_ax := DerivationTree.ax Γ _
    (PropositionalAxiom.implyK (B.imp Proposition.bot) A)
  -- Compose k_ax with d via the S combinator.
  -- We have k_ax: (B -> bot) -> (A -> (B -> bot))
  -- and d: (A -> (B -> bot)) -> bot
  -- We want: (B -> bot) -> bot
  -- This is imp_trans: compose via S combinator
  -- K(d): (B -> bot) -> ((A -> (B -> bot)) -> bot)
  have k_d := DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _
      (PropositionalAxiom.implyK
        ((A.imp (B.imp Proposition.bot)).imp Proposition.bot)
        (B.imp Proposition.bot)))
    d
  -- S(B -> bot, A -> (B -> bot), bot)
  have s_ax := DerivationTree.ax Γ _
    (PropositionalAxiom.implyS (B.imp Proposition.bot)
      (A.imp (B.imp Proposition.bot)) Proposition.bot)
  -- Apply S to k_d: ((B -> bot) -> (A -> (B -> bot))) -> ((B -> bot) -> bot)
  have composed := DerivationTree.modus_ponens Γ _ _ s_ax k_d
  -- Apply to k_ax: (B -> bot) -> bot = neg neg B
  have dne_hyp := DerivationTree.modus_ponens Γ _ _ composed k_ax
  -- Apply dne
  exact hilbertDne dne_hyp

/-! ## Disjunction Rules -/

/-- **Left Disjunction Introduction** (orI1): From `Gamma |- A`,
derive `Gamma |- A or B`.

Since `A or B := (A -> bot) -> B`, use the deduction theorem:
assume `A -> bot`, derive `bot` from `A` and `A -> bot`, then `B` by EFQ. -/
noncomputable def hilbertOrI1 {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Γ A) :
    DerivationTree Γ (A.or B) := by
  -- Goal: Gamma |- (A -> bot) -> B
  apply impI
  -- (A -> bot) :: Gamma |- B
  apply botE
  -- (A -> bot) :: Gamma |- bot
  apply impE (A := A)
  · exact assume List.mem_cons_self
  · exact hilbertWeakening d (fun x hx => List.mem_cons_of_mem _ hx)

/-- **Right Disjunction Introduction** (orI2): From `Gamma |- B`,
derive `Gamma |- A or B`.

Since `A or B := (A -> bot) -> B`, use ImplyK: `B -> ((A -> bot) -> B)`. -/
def hilbertOrI2 {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Γ B) :
    DerivationTree Γ (A.or B) :=
  -- ImplyK(B, A -> bot): B -> ((A -> bot) -> B)
  DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _ (PropositionalAxiom.implyK B (A.imp Proposition.bot)))
    d

/-- **Disjunction Elimination** (orE): From `Gamma |- A or B`,
`A :: Gamma |- C`, and `B :: Gamma |- C`, derive `Gamma |- C`.

Uses the deduction theorem to get `A -> C` and `B -> C`, then
composes `(A -> bot) -> B` with `B -> C` to get `(A -> bot) -> C` = `neg A -> C`.
Then uses classical reasoning (via `dne` and Peirce) to derive `C`. -/
noncomputable def hilbertOrE {Γ : List (PL.Proposition Atom)}
    {A B C : PL.Proposition Atom}
    (d : DerivationTree Γ (A.or B))
    (dA : DerivationTree (A :: Γ) C)
    (dB : DerivationTree (B :: Γ) C) :
    DerivationTree Γ C := by
  -- d : Gamma |- (A -> bot) -> B
  -- Step 1: Gamma |- A -> C
  have hAC : DerivationTree Γ (A.imp C) := impI dA
  -- Step 2: Gamma |- B -> C
  have hBC : DerivationTree Γ (B.imp C) := impI dB
  -- Step 3: Gamma |- (A -> bot) -> C (compose d with hBC)
  -- Using impI: assume (A -> bot), derive B from d, then C from hBC
  have hNAC : DerivationTree Γ (Proposition.neg A |>.imp C) := by
    apply impI
    -- (A -> bot) :: Gamma |- C
    apply impE (A := B)
    · exact hilbertWeakening hBC (fun x hx => List.mem_cons_of_mem _ hx)
    · apply impE (A := Proposition.neg A)
      · exact hilbertWeakening d (fun x hx => List.mem_cons_of_mem _ hx)
      · exact assume List.mem_cons_self
  -- Step 4: Derive C via DNE
  -- Assume neg C (= C -> bot)
  -- From A -> C, contrapose: neg C -> neg A via impI + impE
  -- Then neg A -> C from hNAC gives C, contradicting neg C
  -- So neg neg C, and DNE gives C
  apply hilbertDne
  -- Gamma |- neg neg C = (C -> bot) -> bot
  apply hilbertNegI
  -- (C -> bot) :: Gamma |- bot
  -- Derive neg A from contraposing A -> C
  have hContra : DerivationTree (Proposition.neg C :: Γ) (Proposition.neg A) := by
    apply hilbertNegI
    -- A :: (C -> bot) :: Gamma |- bot
    apply impE (A := C)
    · exact assume (List.mem_cons_of_mem _ List.mem_cons_self)
    · apply impE (A := A)
      · exact hilbertWeakening (hilbertWeakening hAC
          (fun x hx => List.mem_cons_of_mem _ hx))
          (fun x hx => List.mem_cons_of_mem _ hx)
      · exact assume List.mem_cons_self
  -- C -> bot :: Gamma |- C from hNAC and hContra
  have hC : DerivationTree (Proposition.neg C :: Γ) C :=
    impE
      (hilbertWeakening hNAC (fun x hx => List.mem_cons_of_mem _ hx))
      hContra
  -- Apply neg C to C
  exact hilbertNegE (assume List.mem_cons_self) hC

/-! ## Biconditional Rules -/

/-- **Biconditional Introduction** (iffI): From `Gamma |- A -> B` and
`Gamma |- B -> A`, derive `Gamma |- A iff B`.

Since `A iff B := (A -> B) and (B -> A)`, this is `andI`. -/
noncomputable def hilbertIffI {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Γ (A.imp B))
    (d₂ : DerivationTree Γ (B.imp A)) :
    DerivationTree Γ (A.iff B) :=
  hilbertAndI d₁ d₂

/-- **Left Biconditional Elimination** (iffE1): From `Gamma |- A iff B`,
derive `Gamma |- A -> B`.

Since `A iff B := (A -> B) and (B -> A)`, this is `andE1`. -/
def hilbertIffE1 {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Γ (A.iff B)) :
    DerivationTree Γ (A.imp B) :=
  hilbertAndE1 d

/-- **Right Biconditional Elimination** (iffE2): From `Gamma |- A iff B`,
derive `Gamma |- B -> A`.

Since `A iff B := (A -> B) and (B -> A)`, this is `andE2`. -/
def hilbertIffE2 {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Γ (A.iff B)) :
    DerivationTree Γ (B.imp A) :=
  hilbertAndE2 d

/-! ## Deriv-level Wrappers -/

/-- Negation introduction at the `Deriv` level. -/
theorem hilbertNegIDeriv {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h : Deriv (A :: Γ) Proposition.bot) : Deriv Γ (Proposition.neg A) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertNegI d⟩

/-- Negation elimination at the `Deriv` level. -/
theorem hilbertNegEDeriv {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h₁ : Deriv Γ (Proposition.neg A))
    (h₂ : Deriv Γ A) : Deriv Γ Proposition.bot := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂; exact ⟨hilbertNegE d₁ d₂⟩

/-- Top introduction at the `Deriv` level. -/
theorem hilbertTopIDeriv {Γ : List (PL.Proposition Atom)} :
    Deriv Γ (Proposition.top : PL.Proposition Atom) :=
  ⟨hilbertTopI⟩

/-- Conjunction introduction at the `Deriv` level. -/
theorem hilbertAndIDeriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Γ A) (h₂ : Deriv Γ B) : Deriv Γ (A.and B) := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂; exact ⟨hilbertAndI d₁ d₂⟩

/-- Left conjunction elimination at the `Deriv` level. -/
theorem hilbertAndE1Deriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Γ (A.and B)) : Deriv Γ A := by
  obtain ⟨d⟩ := h; exact ⟨hilbertAndE1 d⟩

/-- Right conjunction elimination at the `Deriv` level. -/
theorem hilbertAndE2Deriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Γ (A.and B)) : Deriv Γ B := by
  obtain ⟨d⟩ := h; exact ⟨hilbertAndE2 d⟩

/-- Left disjunction introduction at the `Deriv` level. -/
theorem hilbertOrI1Deriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Γ A) : Deriv Γ (A.or B) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertOrI1 d⟩

/-- Right disjunction introduction at the `Deriv` level. -/
theorem hilbertOrI2Deriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Γ B) : Deriv Γ (A.or B) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertOrI2 d⟩

/-- Disjunction elimination at the `Deriv` level. -/
theorem hilbertOrEDeriv {Γ : List (PL.Proposition Atom)}
    {A B C : PL.Proposition Atom}
    (h : Deriv Γ (A.or B))
    (hA : Deriv (A :: Γ) C)
    (hB : Deriv (B :: Γ) C) : Deriv Γ C := by
  obtain ⟨d⟩ := h; obtain ⟨dA⟩ := hA; obtain ⟨dB⟩ := hB
  exact ⟨hilbertOrE d dA dB⟩

/-- Double negation elimination at the `Deriv` level. -/
theorem hilbertDneDeriv {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h : Deriv Γ (Proposition.neg (Proposition.neg A))) : Deriv Γ A := by
  obtain ⟨d⟩ := h; exact ⟨hilbertDne d⟩

/-- Biconditional introduction at the `Deriv` level. -/
theorem hilbertIffIDeriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Γ (A.imp B))
    (h₂ : Deriv Γ (B.imp A)) : Deriv Γ (A.iff B) := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂; exact ⟨hilbertIffI d₁ d₂⟩

/-- Left biconditional elimination at the `Deriv` level. -/
theorem hilbertIffE1Deriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Γ (A.iff B)) : Deriv Γ (A.imp B) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertIffE1 d⟩

/-- Right biconditional elimination at the `Deriv` level. -/
theorem hilbertIffE2Deriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Γ (A.iff B)) : Deriv Γ (B.imp A) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertIffE2 d⟩

end Cslib.Logic.PL
