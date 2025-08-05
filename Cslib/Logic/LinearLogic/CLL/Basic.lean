/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Aesop
import Mathlib.Order.Notation

/-! # Classical Linear Logic

## TODO
- First-order polymorphism.
- Logical equivalences.
- Cut elimination.

## References

* [J.-Y. Girard, *Linear Logic: its syntax and semantics*] [Girard1995]

-/

universe u

section CLL

variable {Atom : Type u}

namespace CLL

/-- Propositions. -/
inductive Proposition {Atom : Type u} : Type u where
  | atom (x : Atom)
  | atomDual (x : Atom)
  | one
  | zero
  | top
  | bot
  | tensor (a b : @Proposition Atom)
  | parr (a b : @Proposition Atom)
  | oplus (a b : @Proposition Atom)
  | with (a b : @Proposition Atom)
  | bang (a : @Proposition Atom)
  | quest (a : @Proposition Atom)
deriving DecidableEq, BEq

instance : One (@Proposition Atom) where
  one := Proposition.one

instance : Zero (@Proposition Atom) where
  zero := Proposition.zero

instance : Top (@Proposition Atom) where
  top := Proposition.top

instance : Bot (@Proposition Atom) where
  bot := Proposition.bot

scoped infix:35 " ⊗ " => Proposition.tensor
scoped infix:30 " ⅋ " => Proposition.parr

/-- Positive propositions. -/
def Proposition.Pos (a : @Proposition Atom) : Prop :=
  match a with
  | atom _ => True
  | one => True
  | zero => True
  | tensor _ _ => True
  | oplus _ _ => True
  | bang _ => True
  | _ => False

/-- Negative propositions. -/
def Proposition.Neg (a : @Proposition Atom) : Prop :=
  match a with
  | atomDual _ => True
  | bot => True
  | top => True
  | parr _ _ => True
  | Proposition.with _ _ => True
  | quest _ => True
  | _ => False

/-- Whether a `Proposition` is positive is decidable. -/
instance Proposition.pos_decidable (a : @Proposition Atom) : Decidable a.Pos := by
  cases a <;> 
  simp only [Proposition.Pos] <;> 
  first | apply Decidable.isTrue; trivial | apply Decidable.isFalse; trivial

/-- Whether a `Proposition` is negative is decidable. -/
instance Proposition.neg_decidable (a : @Proposition Atom) : Decidable a.Neg := by
  cases a <;> 
  simp only [Proposition.Neg] <;> 
  first | apply Decidable.isTrue; trivial | apply Decidable.isFalse; trivial

/-- Propositional duality. -/
def Proposition.dual (a : @Proposition Atom) : @Proposition Atom :=
  match a with
  | atom x => atomDual x
  | atomDual x => atom x
  | one => bot
  | bot => one
  | zero => top
  | top => zero
  | tensor a b => parr a.dual b.dual
  | parr a b => tensor a.dual b.dual
  | oplus a b => Proposition.with a.dual b.dual
  | Proposition.with a b => oplus a.dual b.dual
  | bang a => quest a.dual
  | quest a => bang a.dual

/-- No proposition is equal to its dual. -/
theorem Proposition.dual.neq (a : @Proposition Atom) : a ≠ a.dual := by
  cases a <;> simp [Proposition.dual]

/-- Two propositions are equal iff their respective duals are equal. -/
theorem Proposition.dual.eq_iff (a b : @Proposition Atom) : a = b ↔ a.dual = b.dual := by
  apply Iff.intro <;> intro h
  · cases a <;> cases b <;> simp at h <;> simp [h]
  · induction a generalizing b <;> cases b
    all_goals try cases h
    all_goals try rfl
    all_goals simp_all [Proposition.dual]; aesop

/-- Duality is an involution. -/
theorem Proposition.dual.involution (a : @Proposition Atom) : a.dual.dual = a := by
  induction a <;> simp only [dual]
  case tensor a b iha ihb =>
    simp only [iha, ihb]
  case parr a b iha ihb =>
    simp only [iha, ihb]
  case oplus a b iha ihb =>
    simp only [iha, ihb]
  case _ a b iha ihb =>
    simp only [iha, ihb]
  case bang a iha =>
    simp only [iha]
  case quest a iha =>
    simp only [iha]

/-- Linear implication. -/
def Proposition.linImpl (a b : @Proposition Atom) : @Proposition Atom := a.dual.parr b

/-- A sequent in CLL is a list of propositions. -/
abbrev Sequent := List (@Proposition Atom)

/-- Checks that all propositions in `Γ` are question marks. -/
def Sequent.allQuest (Γ : @Sequent Atom) :=
  ∀ a ∈ Γ, ∃ b, a = Proposition.quest b

open Proposition in
/-- Sequent calculus for CLL. -/
inductive Proof : @Sequent Atom → Prop where
  | ax : Proof [a, a.dual]
  | cut : Proof (a :: Γ) → Proof (a.dual :: Δ) → Proof (Γ ++ Δ)
  | exchange : List.Perm Γ Δ → Proof Γ → Proof Δ
  | one : Proof [one]
  | bot : Proof Γ → Proof (bot :: Γ)
  | parr : Proof (a :: b :: Γ) → Proof ((parr a b) :: Γ)
  | tensor : Proof (a :: Γ) → Proof (b :: Δ) → Proof ((tensor a b) :: (Γ ++ Δ))
  | oplus₁ : Proof (a :: Γ) → Proof ((oplus a b) :: Γ)
  | oplus₂ : Proof (b :: Γ) → Proof ((oplus a b) :: Γ)
  | with : Proof (a :: Γ) → Proof (b :: Γ) → Proof ((a.with b) :: Γ)
  | top : Proof (top :: Γ)
  | quest : Proof (a :: Γ) → Proof (quest a :: Γ)
  | weaken : Proof Γ → Proof (quest a :: Γ)
  | contract : Proof (quest a :: quest a :: Γ) → Proof (quest a :: Γ)
  | bang {Γ : @Sequent Atom} {a} : Γ.allQuest → Proof (a :: Γ) → Proof (bang a :: Γ)

scoped notation "⊢" Γ:90 => Proof Γ

section LogicalEquiv

/-! ## Logical equivalences -/

/-- Two propositions are equivalent if one implies the other and vice versa. -/
def Proposition.equiv (a b : @Proposition Atom) : Prop := ⊢[a.dual, b] ∧ ⊢[b.dual, a]

scoped infix:29 " ≡ " => Proposition.equiv

namespace Proposition

/-- !⊤ ≡ 1 -/
theorem bang_top_eqv_one : (@bang Atom ⊤) ≡ 1 := by
  constructor
  · apply Proof.weaken
    exact Proof.one
  · apply Proof.bot
    apply Proof.bang
    · intro _ _; contradiction
    exact Proof.top

/-- ?0 ≡ ⊥ -/
theorem quest_zero_eqv_bot : (@quest Atom 0) ≡ ⊥ := by
  constructor
  · apply Proof.exchange (List.Perm.swap (bang top) bot [])
    apply Proof.bot
    apply Proof.bang
    · intro _ _; contradiction
    exact Proof.top
  · apply Proof.exchange (List.Perm.swap one (quest zero) [])
    apply Proof.weaken
    exact Proof.one

/-- a ⊗ 0 ≡ 0 -/
theorem tensor_zero_eqv_zero (a : @Proposition Atom) :
    a ⊗ 0 ≡ 0 := by
  constructor
  · apply Proof.parr
    apply Proof.exchange (List.Perm.swap a.dual (top) [zero])
    exact Proof.top
  · exact Proof.top

/-- a ⅋ ⊤ ≡ ⊤ -/
theorem parr_top_eqv_top (a : @Proposition Atom) :
    a ⅋ ⊤ ≡ ⊤ := by
  constructor
  · apply Proof.exchange (List.Perm.swap (parr a top).dual top [])
    exact Proof.top
  · apply Proof.exchange (List.Perm.swap top.dual (parr a top) [])
    apply Proof.parr
    apply Proof.exchange (List.Perm.swap a top [top.dual])
    exact Proof.top

end Proposition

end LogicalEquiv

end CLL

end CLL
