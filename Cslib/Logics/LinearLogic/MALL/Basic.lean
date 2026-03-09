/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Acclavio, Fabrizio Montesi
-/

module

public import Cslib.Init
public import Cslib.Foundations.Syntax.Context
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.LogicalEquivalence
public import Mathlib.Data.Multiset.Fold
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Union
public import Cslib.Foundations.Data.FinFun

@[expose] public section

/-! # Multiplicative Additive Linear Logic (MALL)

## References

* [J.-Y. Girard, *Linear Logic: its syntax and semantics*][Girard1995]

-/

namespace Cslib.Logic

universe u

variable {Atom : Type u}

namespace MALL

/-- Propositions. -/
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | atomDual (x : Atom)
  -- | one
  -- | zero
  -- | top
  -- | bot
  /-- The multiplicative conjunction connective. -/
  | tensor (a b : Proposition Atom)
  /-- The multiplicative disjunction connective. -/
  | parr (a b : Proposition Atom)
  /-- The additive disjunction connective. -/
  | oplus (a b : Proposition Atom)
  /-- The additive conjunction connective. -/
  | with (a b : Proposition Atom)
deriving DecidableEq, BEq

-- instance : Zero (Proposition Atom) := ⟨.zero⟩
-- instance : One (Proposition Atom) := ⟨.one⟩

-- instance : Top (Proposition Atom) := ⟨.top⟩
-- instance : Bot (Proposition Atom) := ⟨.bot⟩

@[inherit_doc] scoped infix:35 " ⊗ " => Proposition.tensor
@[inherit_doc] scoped infix:35 " ⊕ " => Proposition.oplus
@[inherit_doc] scoped infix:30 " ⅋ " => Proposition.parr
@[inherit_doc] scoped infix:30 " & " => Proposition.with

/-- Propositional duality. -/
@[scoped grind =]
def Proposition.dual : Proposition Atom → Proposition Atom
  | atom x => atomDual x
  | atomDual x => atom x
  -- | one => bot
  -- | bot => one
  -- | zero => top
  -- | top => zero
  | tensor a b => parr a.dual b.dual
  | parr a b => tensor a.dual b.dual
  | oplus a b => .with a.dual b.dual
  | .with a b => oplus a.dual b.dual

@[inherit_doc] scoped postfix:max "⫠" => Proposition.dual

/-- A sequent in MALL is a multiset of propositions. -/
abbrev Sequent Atom := Multiset (Proposition Atom)

open Proposition in
/-- A proof in the sequent calculus for classical linear logic. -/
inductive Proof : Sequent Atom → Type u where
  | ax : Proof {a, a⫠}
  -- | cut : Proof (a ::ₘ Γ) → Proof (a⫠ ::ₘ Δ) → Proof (Γ + Δ)
  -- | one : Proof {1}
  -- | bot : Proof Γ → Proof (⊥ ::ₘ Γ)
  | parr : Proof (a ::ₘ b ::ₘ Γ) → Proof ((a ⅋ b) ::ₘ Γ)
  | tensor : Proof (a ::ₘ Γ) → Proof (b ::ₘ Δ) → Proof ((a ⊗ b) ::ₘ (Γ + Δ))
  | oplus₁ : Proof (a ::ₘ Γ) → Proof ((a ⊕ b) ::ₘ Γ)
  | oplus₂ : Proof (b ::ₘ Γ) → Proof ((a ⊕ b) ::ₘ Γ)
  | with : Proof (a ::ₘ Γ) → Proof (b ::ₘ Γ) → Proof ((a & b) ::ₘ Γ)
  -- | top : Proof (⊤ ::ₘ Γ)
  -- No rule for zero.

namespace ProofNet

inductive BinTree (α : Type*) where
  | leaf (a : α)
  | node (a : α) (t₁ : BinTree α) (t₂ : BinTree α)

inductive PropositionTree.Value (Atom : Type u) where
  | atom (a : Atom)
  | atomDual (a : Atom)
  | tensor
  | parr
  | oplus
  | with

def BinTree.names [DecidableEq α] (t : BinTree α) : Finset α :=
  match t with
  | leaf a => {a}
  | node a t₁ t₂ => {a} ∪ t₁.names ∪ t₂.names

def PropositionTree (Atom Name : Type*) [DecidableEq Name] :=
  Σ (t : BinTree Name), ({n // n ∈ t.names} → PropositionTree.Value Atom)

def BinTree.wellFormed [DecidableEq α] (t : BinTree α) : Prop :=
  match t with
  | leaf _ => True
  | node a t₁ t₂ => Disjoint t₁.names t₂.names ∧ a ∉ t₁.names ∪ t₂.names

abbrev Sequent (Atom Name : Type*) [DecidableEq Name] := Multiset (PropositionTree Atom Name)

def Sequent.wellFormed [DecidableEq Name] (Γ : Sequent Atom Name) :=
  Γ.map (BinTree.names ·.1)
  |> Multiset.fold (Disjoint · ·)
  -- |> Multiset.fold (· ∪ ·) ∅

end ProofNet

end MALL
end Cslib.Logic
