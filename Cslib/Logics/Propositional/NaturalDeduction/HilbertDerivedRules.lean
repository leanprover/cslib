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

Rules are organized into two layers:

## Intuitionistic Layer (K, S, EFQ)
Introduction rules that require only the minimal intuitionistic axioms:
- `hilbertNegI`, `hilbertNegE`, `hilbertTopI`
- `hilbertAndI`, `hilbertOrI1`, `hilbertOrI2`, `hilbertIffI`

## Classical Layer (K, S, EFQ, Peirce)
Elimination rules that additionally require Peirce's law:
- `hilbertDne` (double negation elimination)
- `hilbertAndE1`, `hilbertAndE2`
- `hilbertOrE`
- `hilbertIffE1`, `hilbertIffE2`

### Prop-level Wrappers
All rules have `Deriv`-level versions with the suffix `Deriv`.

## Design

Rules that use `impI` (the deduction theorem) are `noncomputable`.
Elimination rules that rely only on axioms + modus ponens are computable.
All definitions are parameterized over a generic axiom predicate `Axioms`
with explicit axiom witnesses, following the pattern from `DeductionTheorem.lean`.

## References

* `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` -- ND wrappers
* `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- Hilbert system
* `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- axiom schemata
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

variable {Atom : Type*}

/-! ## Intuitionistic Layer (K, S, EFQ) -/

/-! ### Negation Rules -/

/-- **Negation Introduction** (negI): From `A :: Gamma |- bot`, derive `Gamma |- neg A`.

Since `neg A := A -> bot`, this is `impI`. Requires K and S axioms. -/
noncomputable def hilbertNegI
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree Axioms (A :: Γ) Proposition.bot) :
    DerivationTree Axioms Γ (Proposition.neg A) :=
  impI h_K h_S d

/-- **Negation Elimination** (negE): From `Gamma |- neg A` and `Gamma |- A`,
derive `Gamma |- bot`.

Since `neg A := A -> bot`, this is `impE`. No axiom parameters needed. -/
def hilbertNegE
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (Proposition.neg A))
    (d₂ : DerivationTree Axioms Γ A) :
    DerivationTree Axioms Γ Proposition.bot :=
  impE d₁ d₂

/-! ### Verum -/

/-- **Top Introduction** (topI): `Gamma |- top` for any context.

Since `top := bot -> bot`, use EFQ at `bot` and weaken. Requires EFQ axiom. -/
def hilbertTopI
    {Axioms : PL.Proposition Atom → Prop}
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : List (PL.Proposition Atom)} :
    DerivationTree Axioms Γ (Proposition.top : PL.Proposition Atom) :=
  DerivationTree.weakening [] Γ _
    (DerivationTree.ax [] _ (h_EFQ Proposition.bot))
    (fun _ h => nomatch h)

/-! ### Conjunction Introduction -/

/-- **Conjunction Introduction** (andI): From `Gamma |- A` and `Gamma |- B`,
derive `Gamma |- A and B`.

Since `A and B := (A -> (B -> bot)) -> bot`, introduce the implication
using the deduction theorem, then apply the hypothesis. Requires K and S axioms. -/
noncomputable def hilbertAndI
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ A)
    (d₂ : DerivationTree Axioms Γ B) :
    DerivationTree Axioms Γ (A.and B) := by
  -- Goal: Gamma |- (A -> (B -> bot)) -> bot
  apply impI h_K h_S
  -- (A -> (B -> bot)) :: Gamma |- bot
  apply impE (A := B)
  · apply impE (A := A)
    · exact assume List.mem_cons_self
    · exact hilbertWeakening d₁ (fun x hx => List.mem_cons_of_mem _ hx)
  · exact hilbertWeakening d₂ (fun x hx => List.mem_cons_of_mem _ hx)

/-! ### Disjunction Introduction -/

/-- **Left Disjunction Introduction** (orI1): From `Gamma |- A`,
derive `Gamma |- A or B`.

Since `A or B := (A -> bot) -> B`, use the deduction theorem:
assume `A -> bot`, derive `bot` from `A` and `A -> bot`, then `B` by EFQ.
Requires K, S, and EFQ axioms. -/
noncomputable def hilbertOrI1
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ A) :
    DerivationTree Axioms Γ (A.or B) := by
  -- Goal: Gamma |- (A -> bot) -> B
  apply impI h_K h_S
  -- (A -> bot) :: Gamma |- B
  apply botE h_EFQ
  -- (A -> bot) :: Gamma |- bot
  apply impE (A := A)
  · exact assume List.mem_cons_self
  · exact hilbertWeakening d (fun x hx => List.mem_cons_of_mem _ hx)

/-- **Right Disjunction Introduction** (orI2): From `Gamma |- B`,
derive `Gamma |- A or B`.

Since `A or B := (A -> bot) -> B`, use ImplyK: `B -> ((A -> bot) -> B)`.
Requires K axiom. -/
def hilbertOrI2
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ B) :
    DerivationTree Axioms Γ (A.or B) :=
  -- ImplyK(B, A -> bot): B -> ((A -> bot) -> B)
  DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _ (h_K B (A.imp Proposition.bot)))
    d

/-! ### Biconditional Introduction -/

/-- **Biconditional Introduction** (iffI): From `Gamma |- A -> B` and
`Gamma |- B -> A`, derive `Gamma |- A iff B`.

Since `A iff B := (A -> B) and (B -> A)`, this is `andI`. Requires K and S axioms. -/
noncomputable def hilbertIffI
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (A.imp B))
    (d₂ : DerivationTree Axioms Γ (B.imp A)) :
    DerivationTree Axioms Γ (A.iff B) :=
  hilbertAndI h_K h_S d₁ d₂

/-! ### Intuitionistic Deriv-level Wrappers -/

/-- Negation introduction at the `Deriv` level. -/
theorem hilbertNegIDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h : Deriv Axioms (A :: Γ) Proposition.bot) :
    Deriv Axioms Γ (Proposition.neg A) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertNegI h_K h_S d⟩

/-- Negation elimination at the `Deriv` level. -/
theorem hilbertNegEDeriv
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h₁ : Deriv Axioms Γ (Proposition.neg A))
    (h₂ : Deriv Axioms Γ A) :
    Deriv Axioms Γ Proposition.bot := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂; exact ⟨hilbertNegE d₁ d₂⟩

/-- Top introduction at the `Deriv` level. -/
theorem hilbertTopIDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : List (PL.Proposition Atom)} :
    Deriv Axioms Γ (Proposition.top : PL.Proposition Atom) :=
  ⟨hilbertTopI h_EFQ⟩

/-- Conjunction introduction at the `Deriv` level. -/
theorem hilbertAndIDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Axioms Γ A)
    (h₂ : Deriv Axioms Γ B) :
    Deriv Axioms Γ (A.and B) := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂; exact ⟨hilbertAndI h_K h_S d₁ d₂⟩

/-- Left disjunction introduction at the `Deriv` level. -/
theorem hilbertOrI1Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ A) : Deriv Axioms Γ (A.or B) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertOrI1 h_K h_S h_EFQ d⟩

/-- Right disjunction introduction at the `Deriv` level. -/
theorem hilbertOrI2Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ B) : Deriv Axioms Γ (A.or B) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertOrI2 h_K d⟩

/-- Biconditional introduction at the `Deriv` level. -/
theorem hilbertIffIDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Axioms Γ (A.imp B))
    (h₂ : Deriv Axioms Γ (B.imp A)) :
    Deriv Axioms Γ (A.iff B) := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂; exact ⟨hilbertIffI h_K h_S d₁ d₂⟩

/-! ## Classical Layer (K, S, EFQ, Peirce) -/

/-! ### Double Negation Elimination -/

/-- **Double Negation Elimination** (dne): From `Gamma |- neg neg A`,
derive `Gamma |- A`.

Uses Peirce(A, bot) to get ((A -> bot) -> A) -> A, then EFQ to get
bot -> A, then composes neg neg A = (A -> bot) -> bot with (bot -> A)
via the B-combinator to get (A -> bot) -> A, and applies Peirce.
Requires K, S, EFQ, and Peirce axioms. -/
def hilbertDne
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (Proposition.neg (Proposition.neg A))) :
    DerivationTree Axioms Γ A := by
  -- d : Gamma |- (A -> bot) -> bot
  -- Peirce(A, bot): ((A -> bot) -> A) -> A
  have peirce := DerivationTree.ax Γ _ (h_Peirce A Proposition.bot)
  -- EFQ(A): bot -> A
  have efq := DerivationTree.ax Γ _ (h_EFQ A)
  -- ImplyK: (bot -> A) -> ((A -> bot) -> (bot -> A))
  have k_efq := DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _
      (h_K (Proposition.bot.imp A)
        (A.imp Proposition.bot)))
    efq
  -- ImplyS at ((A -> bot) -> (bot -> A)) -> (((A -> bot) -> bot) -> ((A -> bot) -> A))
  have s_ax := DerivationTree.ax Γ _
    (h_S (A.imp Proposition.bot) Proposition.bot A)
  -- Apply S to k_efq: ((A -> bot) -> bot) -> ((A -> bot) -> A)
  have composed := DerivationTree.modus_ponens Γ _ _ s_ax k_efq
  -- Apply to d: (A -> bot) -> A
  have imp_peirce := DerivationTree.modus_ponens Γ _ _ composed d
  -- Apply Peirce: A
  exact DerivationTree.modus_ponens Γ _ _ peirce imp_peirce

/-! ### Conjunction Elimination -/

/-- **Left Conjunction Elimination** (andE1): From `Gamma |- A and B`,
derive `Gamma |- A`.

Uses Peirce(A, B -> bot) + EFQ composition.
Requires K, S, EFQ, and Peirce axioms. -/
def hilbertAndE1
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (A.and B)) :
    DerivationTree Axioms Γ A := by
  -- d : Gamma |- (A -> (B -> bot)) -> bot
  have peirce := DerivationTree.ax Γ _
    (h_Peirce A (B.imp Proposition.bot))
  have efq := DerivationTree.ax Γ _ (h_EFQ A)
  have k_efq := DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _
      (h_K (Proposition.bot.imp A) (A.imp (B.imp Proposition.bot))))
    efq
  have s_ax := DerivationTree.ax Γ _
    (h_S (A.imp (B.imp Proposition.bot)) Proposition.bot A)
  have composed := DerivationTree.modus_ponens Γ _ _ s_ax k_efq
  have result := DerivationTree.modus_ponens Γ _ _ composed d
  exact DerivationTree.modus_ponens Γ _ _ peirce result

/-- **Right Conjunction Elimination** (andE2): From `Gamma |- A and B`,
derive `Gamma |- B`.

Uses ImplyK to extract B -> (A -> (B -> bot)), composes with d to get
neg neg B, then applies dne.
Requires K, S, EFQ, and Peirce axioms. -/
def hilbertAndE2
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (A.and B)) :
    DerivationTree Axioms Γ B := by
  -- d : Gamma |- (A -> (B -> bot)) -> bot
  have k_ax := DerivationTree.ax Γ _
    (h_K (B.imp Proposition.bot) A)
  have k_d := DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _
      (h_K
        ((A.imp (B.imp Proposition.bot)).imp Proposition.bot)
        (B.imp Proposition.bot)))
    d
  have s_ax := DerivationTree.ax Γ _
    (h_S (B.imp Proposition.bot)
      (A.imp (B.imp Proposition.bot)) Proposition.bot)
  have composed := DerivationTree.modus_ponens Γ _ _ s_ax k_d
  have dne_hyp := DerivationTree.modus_ponens Γ _ _ composed k_ax
  exact hilbertDne h_K h_S h_EFQ h_Peirce dne_hyp

/-! ### Disjunction Elimination -/

/-- **Disjunction Elimination** (orE): From `Gamma |- A or B`,
`A :: Gamma |- C`, and `B :: Gamma |- C`, derive `Gamma |- C`.

Uses the deduction theorem, composition, and classical reasoning (DNE).
Requires K, S, EFQ, and Peirce axioms. -/
noncomputable def hilbertOrE
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B C : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (A.or B))
    (dA : DerivationTree Axioms (A :: Γ) C)
    (dB : DerivationTree Axioms (B :: Γ) C) :
    DerivationTree Axioms Γ C := by
  -- d : Gamma |- (A -> bot) -> B
  -- Step 1: Gamma |- A -> C
  have hAC : DerivationTree Axioms Γ (A.imp C) := impI h_K h_S dA
  -- Step 2: Gamma |- B -> C
  have hBC : DerivationTree Axioms Γ (B.imp C) := impI h_K h_S dB
  -- Step 3: Gamma |- (A -> bot) -> C (compose d with hBC)
  have hNAC : DerivationTree Axioms Γ (Proposition.neg A |>.imp C) := by
    apply impI h_K h_S
    -- (A -> bot) :: Gamma |- C
    apply impE (A := B)
    · exact hilbertWeakening hBC (fun x hx => List.mem_cons_of_mem _ hx)
    · apply impE (A := Proposition.neg A)
      · exact hilbertWeakening d (fun x hx => List.mem_cons_of_mem _ hx)
      · exact assume List.mem_cons_self
  -- Step 4: Derive C via DNE
  apply hilbertDne h_K h_S h_EFQ h_Peirce
  -- Gamma |- neg neg C = (C -> bot) -> bot
  apply hilbertNegI h_K h_S
  -- (C -> bot) :: Gamma |- bot
  have hContra : DerivationTree Axioms (Proposition.neg C :: Γ) (Proposition.neg A) := by
    apply hilbertNegI h_K h_S
    -- A :: (C -> bot) :: Gamma |- bot
    apply impE (A := C)
    · exact assume (List.mem_cons_of_mem _ List.mem_cons_self)
    · apply impE (A := A)
      · exact hilbertWeakening (hilbertWeakening hAC
          (fun x hx => List.mem_cons_of_mem _ hx))
          (fun x hx => List.mem_cons_of_mem _ hx)
      · exact assume List.mem_cons_self
  -- C -> bot :: Gamma |- C from hNAC and hContra
  have hC : DerivationTree Axioms (Proposition.neg C :: Γ) C :=
    impE
      (hilbertWeakening hNAC (fun x hx => List.mem_cons_of_mem _ hx))
      hContra
  -- Apply neg C to C
  exact hilbertNegE (assume List.mem_cons_self) hC

/-! ### Biconditional Elimination -/

/-- **Left Biconditional Elimination** (iffE1): From `Gamma |- A iff B`,
derive `Gamma |- A -> B`.

Since `A iff B := (A -> B) and (B -> A)`, this is `andE1`.
Requires K, S, EFQ, and Peirce axioms. -/
def hilbertIffE1
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (A.iff B)) :
    DerivationTree Axioms Γ (A.imp B) :=
  hilbertAndE1 h_K h_S h_EFQ h_Peirce d

/-- **Right Biconditional Elimination** (iffE2): From `Gamma |- A iff B`,
derive `Gamma |- B -> A`.

Since `A iff B := (A -> B) and (B -> A)`, this is `andE2`.
Requires K, S, EFQ, and Peirce axioms. -/
def hilbertIffE2
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (A.iff B)) :
    DerivationTree Axioms Γ (B.imp A) :=
  hilbertAndE2 h_K h_S h_EFQ h_Peirce d

/-! ### Classical Deriv-level Wrappers -/

/-- Double negation elimination at the `Deriv` level. -/
theorem hilbertDneDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h : Deriv Axioms Γ (Proposition.neg (Proposition.neg A))) :
    Deriv Axioms Γ A := by
  obtain ⟨d⟩ := h; exact ⟨hilbertDne h_K h_S h_EFQ h_Peirce d⟩

/-- Left conjunction elimination at the `Deriv` level. -/
theorem hilbertAndE1Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ (A.and B)) : Deriv Axioms Γ A := by
  obtain ⟨d⟩ := h; exact ⟨hilbertAndE1 h_K h_S h_EFQ h_Peirce d⟩

/-- Right conjunction elimination at the `Deriv` level. -/
theorem hilbertAndE2Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ (A.and B)) : Deriv Axioms Γ B := by
  obtain ⟨d⟩ := h; exact ⟨hilbertAndE2 h_K h_S h_EFQ h_Peirce d⟩

/-- Disjunction elimination at the `Deriv` level. -/
theorem hilbertOrEDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B C : PL.Proposition Atom}
    (h : Deriv Axioms Γ (A.or B))
    (hA : Deriv Axioms (A :: Γ) C)
    (hB : Deriv Axioms (B :: Γ) C) :
    Deriv Axioms Γ C := by
  obtain ⟨d⟩ := h; obtain ⟨dA⟩ := hA; obtain ⟨dB⟩ := hB
  exact ⟨hilbertOrE h_K h_S h_EFQ h_Peirce d dA dB⟩

/-- Left biconditional elimination at the `Deriv` level. -/
theorem hilbertIffE1Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ (A.iff B)) :
    Deriv Axioms Γ (A.imp B) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertIffE1 h_K h_S h_EFQ h_Peirce d⟩

/-- Right biconditional elimination at the `Deriv` level. -/
theorem hilbertIffE2Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ (A.iff B)) :
    Deriv Axioms Γ (B.imp A) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertIffE2 h_K h_S h_EFQ h_Peirce d⟩

end Cslib.Logic.PL
