/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Rademaker
-/

import Cslib.Logics.LinearLogic.CLL.Basic

namespace CslibTests

/-! # Tests for Classical Linear Logic

I use `Proposition Nat` as the concrete instantiation for atoms.
-/

open Cslib.CLL

/-! ## Proposition construction tests -/

-- Define some atomic propositions for testing
abbrev P := Proposition Nat

def a : P  := .atom 0
def a' : P := .atomDual 0
def b : P  := .atom 1
def c : P  := .atom 2

-- Test that notations work correctly
example : P := a ⊗ b           -- tensor
example : P := a ⅋ b           -- parr
example : P := a ⊕ b           -- oplus
example : P := a & b           -- with
example : P := !a              -- bang
example : P := ʔa              -- quest
example : P := (1 : P)         -- one
example : P := (0 : P)         -- zero
example : P := (⊤ : P)         -- top
example : P := (⊥ : P)         -- bot
example : P := a ⊸ b           -- linear implication

-- Test nested propositions
example : P := (a ⊗ b) ⅋ c
example : P := !(a ⊗ b)
example : P := a ⊕ (b & c)

/-! ## Duality tests -/

-- dual_involution: a⫠⫠ = a
example : (a⫠⫠ : P) = a := Proposition.dual_involution a
example : (a ⊗ b)⫠⫠ = (a ⊗ b : P) := Proposition.dual_involution (a ⊗ b)
example : (!a)⫠⫠ = (!a : P) := Proposition.dual_involution (!a)

-- Dual of specific propositions
example : (a⫠ : P) = a' := rfl
example : ((1 : P)⫠) = ⊥ := rfl
example : ((0 : P)⫠) = ⊤ := rfl
example : (a ⊗ b)⫠ = (a⫠ ⅋ b⫠ : P) := rfl
example : (a ⅋ b)⫠ = (a⫠ ⊗ b⫠ : P) := rfl
example : (a ⊕ b)⫠ = (a⫠ & b⫠ : P) := rfl
example : (a & b)⫠ = (a⫠ ⊕ b⫠ : P) := rfl
example : (!a)⫠ = (ʔ(a⫠) : P) := rfl
example : (ʔa)⫠ = (!(a⫠) : P) := rfl

-- dual_neq: no proposition equals its dual
example : a ≠ a⫠ := Proposition.dual_neq a
example : (1 : P) ≠ (1 : P)⫠ := Proposition.dual_neq 1

-- dual_inj: duality is injective
example : (a⫠ = b⫠) ↔ (a = b) := Proposition.dual_inj a b


/-! ## Basic proof tests -/

-- Axiom: ⊢ a, a⫠
example : ⇓({a, a⫠} : Sequent Nat) := Proof.ax
example : ⇓({a⫠, a} : Sequent Nat) := Proof.ax'

-- One: ⊢ 1
example : ⇓({1} : Sequent Nat) := Proof.one

-- Top: ⊢ ⊤, Γ
example : ⇓({⊤} : Sequent Nat) := Proof.top
example : ⇓(⊤ ::ₘ {a} : Sequent Nat) := Proof.top

-- Bot: from ⊢ Γ derive ⊢ ⊥, Γ
example : ⇓(⊥ ::ₘ {1} : Sequent Nat) := Proof.bot Proof.one

-- Parr: from ⊢ a, b, Γ derive ⊢ a ⅋ b, Γ
example : ⇓({a ⅋ a⫠} : Sequent Nat) := Proof.parr Proof.ax

-- Tensor: from ⊢ a, Γ and ⊢ b, Δ derive ⊢ a ⊗ b, Γ, Δ
example : ⇓({a ⊗ b, a⫠, b⫠} : Sequent Nat) := Proof.tensor Proof.ax Proof.ax

-- Oplus: from ⊢ a, Γ derive ⊢ a ⊕ b, Γ
example : ⇓({a ⊕ b, a⫠} : Sequent Nat) := Proof.oplus₁ Proof.ax
example : ⇓({a ⊕ b, b⫠} : Sequent Nat) := Proof.oplus₂ Proof.ax

-- With: from ⊢ a, Γ and ⊢ b, Γ derive ⊢ a & b, Γ
example : ⇓({a & a, a⫠} : Sequent Nat) := Proof.with Proof.ax Proof.ax

-- Quest: from ⊢ a, Γ derive ⊢ ʔa, Γ
example : ⇓({ʔa, a⫠} : Sequent Nat) := Proof.quest Proof.ax

-- Weaken: from ⊢ Γ derive ⊢ ʔa, Γ
example : ⇓({ʔa, 1} : Sequent Nat) := Proof.weaken Proof.one


/-! ## Logical equivalence tests (proof-irrelevant) -/

-- Reflexivity
example : (a : P) ≡ a := Proposition.Equiv.refl a

-- Symmetry
example (h : (a : P) ≡ b) : b ≡ a := Proposition.Equiv.symm h

-- Transitivity
example (hab : (a : P) ≡ b) (hbc : b ≡ c) : a ≡ c := Proposition.Equiv.trans hab hbc

-- Coercion from proof-relevant to proof-irrelevant (via .toProp)
example : (!⊤ : P) ≡ 1 := Proposition.bang_top_eqv_one.toProp
example : (ʔ0 : P) ≡ ⊥ := Proposition.quest_zero_eqv_bot.toProp
example : (a ⊗ 0 : P) ≡ 0 := (Proposition.tensor_zero_eqv_zero a).toProp
example : (a ⅋ ⊤ : P) ≡ ⊤ := (Proposition.parr_top_eqv_top a).toProp
example : (a ⊗ b : P) ≡ b ⊗ a := Proposition.tensor_symm.toProp
example : (a ⊗ (b ⊗ c) : P) ≡ (a ⊗ b) ⊗ c := Proposition.tensor_assoc.toProp
example : (a ⊗ (b ⊕ c) : P) ≡ (a ⊗ b) ⊕ (a ⊗ c) := (Proposition.tensor_distrib_oplus a b c).toProp
example : (a ⊕ a : P) ≡ a := Proposition.oplus_idem.toProp
example : (a & a : P) ≡ a := Proposition.with_idem.toProp


/-! ## Proof-relevant equivalence tests -/

-- equiv.refl
example : (a : P) ≡⇓ a := Proposition.equiv.refl a

-- equiv.symm
example (h : (a : P) ≡⇓ b) : b ≡⇓ a := Proposition.equiv.symm a h

-- equiv.trans
example (hab : (a : P) ≡⇓ b) (hbc : (b : P) ≡⇓ c) : a ≡⇓ c := Proposition.equiv.trans hab hbc

-- Proof-relevant versions of logical equivalences
example : (!⊤ : P) ≡⇓ 1 := Proposition.bang_top_eqv_one
example : (ʔ0 : P) ≡⇓ ⊥ := Proposition.quest_zero_eqv_bot
example : (a ⊗ b : P) ≡⇓ b ⊗ a := Proposition.tensor_symm
example : (a ⊗ (b ⊗ c) : P) ≡⇓ (a ⊗ b) ⊗ c := Proposition.tensor_assoc
example : (a ⊕ a : P) ≡⇓ a := Proposition.oplus_idem
example : (a & a : P) ≡⇓ a := Proposition.with_idem


/-! ## Inversion tests -/

-- parr_inversion
example (h : ⇓({a ⅋ b} : Sequent Nat)) : ⇓({a, b} : Sequent Nat) := Proof.parr_inversion h

-- bot_inversion
example (h : ⇓({⊥, 1} : Sequent Nat)) : ⇓({1} : Sequent Nat) := Proof.bot_inversion h

-- with_inversion
example (h : ⇓({a & b} : Sequent Nat)) : ⇓({a} : Sequent Nat) := Proof.with_inversion₁ h
example (h : ⇓({a & b} : Sequent Nat)) : ⇓({b} : Sequent Nat) := Proof.with_inversion₂ h


/-! ## Positive/Negative classification tests -/

-- Positive propositions
example : Proposition.positive a = true := rfl
example : Proposition.positive (1 : P) = true := rfl
example : Proposition.positive (0 : P) = true := rfl
example : Proposition.positive (a ⊗ b) = true := rfl
example : Proposition.positive (a ⊕ b) = true := rfl
example : Proposition.positive (!a) = true := rfl

-- Negative propositions
example : Proposition.negative (Proposition.atomDual 0 : P) = true := rfl
example : Proposition.negative (⊥ : P) = true := rfl
example : Proposition.negative (⊤ : P) = true := rfl
example : Proposition.negative (a ⅋ b) = true := rfl
example : Proposition.negative (a & b) = true := rfl
example : Proposition.negative (ʔa) = true := rfl


/-! ## linear logic proofs tests -/

/-- Example 37 Figure 5 from https://arxiv.org/abs/1904.06850

B ⊢ (!(A ⊸ B) ⊸ B) ⊗ (B ⊸ (!A ⊸ B))

This translates to the sequent:

⊢ B⫠, (!(A ⊸ B) ⊸ B) ⊗ (B ⊸ (!A ⊸ B))

Breaking down the formula:

         A ⊸ B = A⫠ ⅋ B (linear implication)
      !(A ⊸ B) = !(A⫠ ⅋ B)
   (!(A ⊸ B))⫠ = ʔ((A⫠ ⅋ B)⫠) = ʔ(A ⊗ B⫠)
  !(A ⊸ B) ⊸ B = (!(A ⊸ B))⫠ ⅋ B = ʔ(A ⊗ B⫠) ⅋ B
        !A ⊸ B = (!A)⫠ ⅋ B = ʔA⫠ ⅋ B
  B ⊸ (!A ⊸ B) = B⫠ ⅋ (ʔA⫠ ⅋ B)
-/
example : ⇓({b⫠, (!(a ⊸ b) ⊸ b) ⊗ (b ⊸ (!a ⊸ b))} : Sequent Nat) := by
  apply Proof.rwConclusion (Multiset.pair_comm ..)
  -- tensor rule, We need Γ + Δ = {b⫠}, so Γ = {b⫠} and Δ = {}
  apply Proof.tensor (Γ := {b⫠}) (Δ := {})
  · -- !(a ⊸ b) ⊸ b = ʔ(a ⊗ b⫠) ⅋ b
    apply Proof.parr   -- Apply parr to get: ⊢ ʔ(a ⊗ b⫠), b, b⫠
    apply Proof.weaken
    apply Proof.ax
  · -- b ⊸ (!a ⊸ b) = b⫠ ⅋ (ʔa⫠ ⅋ b)
    apply Proof.parr   -- Apply parr to get: ⊢ b⫠, ʔa⫠ ⅋ b
    apply Proof.rwConclusion (Multiset.pair_comm ..)
    apply Proof.parr   -- Apply parr to get: ⊢ b⫠, ʔa⫠, b
    apply Proof.weaken
    exact Proof.ax


end CslibTests
