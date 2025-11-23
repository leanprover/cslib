/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Init
import Mathlib.Order.Notation
import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Fold
import Mathlib.Data.Multiset.AddSub

/-! # Classical Linear Logic

## TODO
- First-order polymorphism.
- Cut elimination.

## References

* [J.-Y. Girard, *Linear Logic: its syntax and semantics*][Girard1995]

-/

namespace Cslib

universe u

variable {Atom : Type u}

namespace CLL

/-- Propositions. -/
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | atomDual (x : Atom)
  | one
  | zero
  | top
  | bot
  /-- The multiplicative conjunction connective. -/
  | tensor (a b : Proposition Atom)
  /-- The multiplicative disjunction connective. -/
  | parr (a b : Proposition Atom)
  /-- The additive disjunction connective. -/
  | oplus (a b : Proposition Atom)
  /-- The additive conjunction connective. -/
  | with (a b : Proposition Atom)
  /-- The "of course" exponential. -/
  | bang (a : Proposition Atom)
  /-- The "why not" exponential.
  This is written as ʔ, or \_?, to distinguish itself from the lean syntatical hole ? syntax -/
  | quest (a : Proposition Atom)
deriving DecidableEq, BEq

instance : Zero (Proposition Atom) := ⟨.zero⟩
instance : One (Proposition Atom) := ⟨.one⟩

instance : Top (Proposition Atom) := ⟨.top⟩
instance : Bot (Proposition Atom) := ⟨.bot⟩

@[inherit_doc] scoped infix:35 " ⊗ " => Proposition.tensor
@[inherit_doc] scoped infix:35 " ⊕ " => Proposition.oplus
@[inherit_doc] scoped infix:30 " ⅋ " => Proposition.parr
@[inherit_doc] scoped infix:30 " & " => Proposition.with

@[inherit_doc] scoped prefix:95 "!" => Proposition.bang
@[inherit_doc] scoped prefix:95 "ʔ" => Proposition.quest

/-- Positive propositions. -/
def Proposition.positive : Proposition Atom → Bool
  | atom _ => true
  | one => true
  | zero => true
  | tensor _ _ => true
  | oplus _ _ => true
  | bang _ => true
  | _ => false

/-- Negative propositions. -/
def Proposition.negative : Proposition Atom → Bool
  | atomDual _ => true
  | bot => true
  | top => true
  | parr _ _ => true
  | .with _ _ => true
  | quest _ => true
  | _ => false

/-- Whether a `Proposition` is positive is decidable. -/
instance Proposition.positive_decidable (a : Proposition Atom) : Decidable a.positive := by
  unfold Proposition.positive
  split <;> infer_instance

/-- Whether a `Proposition` is negative is decidable. -/
instance Proposition.negative_decidable (a : Proposition Atom) : Decidable a.negative := by
  unfold Proposition.negative
  split <;> infer_instance

/-- Propositional duality. -/
@[scoped grind =]
def Proposition.dual : Proposition Atom → Proposition Atom
  | atom x => atomDual x
  | atomDual x => atom x
  | one => bot
  | bot => one
  | zero => top
  | top => zero
  | tensor a b => parr a.dual b.dual
  | parr a b => tensor a.dual b.dual
  | oplus a b => .with a.dual b.dual
  | .with a b => oplus a.dual b.dual
  | bang a => quest a.dual
  | quest a => bang a.dual

@[inherit_doc] scoped postfix:max "⫠" => Proposition.dual

/-- No proposition is equal to its dual. -/
@[scoped grind .]
theorem Proposition.dual_neq (a : Proposition Atom) : a ≠ a⫠ := by
  cases a <;> simp [Proposition.dual]

/-- Two propositions are equal iff their respective duals are equal. -/
@[scoped grind =, simp]
theorem Proposition.dual_inj (a b : Proposition Atom) : a⫠ = b⫠ ↔ a = b := by
  refine ⟨fun h ↦ ?_, congrArg dual⟩
  induction a generalizing b <;> cases b
  all_goals grind

/-- Duality is an involution. -/
@[scoped grind =, simp]
theorem Proposition.dual.involution (a : Proposition Atom) : a⫠⫠ = a := by
  induction a <;> simp_all [dual]

/-- Linear implication. -/
@[scoped grind .]
def Proposition.linImpl (a b : Proposition Atom) : Proposition Atom := a⫠ ⅋ b

@[inherit_doc] scoped infix:25 " ⊸ " => Proposition.linImpl

/-- A sequent in CLL is a multiset of propositions. -/
abbrev Sequent Atom := Multiset (Proposition Atom)

/-- Checks that all propositions in a sequent `Γ` are question marks. -/
def Sequent.allQuest (Γ : Sequent Atom) :=
  Γ.map (· matches ʔ_)
  |> Multiset.fold Bool.and true

open Proposition in
/-- A proof in the sequent calculus for classical linear logic. -/
inductive Proof : Sequent Atom → Type u where
  | ax : Proof {a, a⫠}
  | cut : Proof (a ::ₘ Γ) → Proof (a⫠ ::ₘ Δ) → Proof (Γ + Δ)
  | one : Proof {1}
  | bot : Proof Γ → Proof (⊥ ::ₘ Γ)
  | parr : Proof (a ::ₘ b ::ₘ Γ) → Proof ((a ⅋ b) ::ₘ Γ)
  | tensor : Proof (a ::ₘ Γ) → Proof (b ::ₘ Δ) → Proof ((a ⊗ b) ::ₘ (Γ + Δ))
  | oplus₁ : Proof (a ::ₘ Γ) → Proof ((a ⊕ b) ::ₘ Γ)
  | oplus₂ : Proof (b ::ₘ Γ) → Proof ((a ⊕ b) ::ₘ Γ)
  | with : Proof (a ::ₘ Γ) → Proof (b ::ₘ Γ) → Proof ((a & b) ::ₘ Γ)
  | top : Proof (⊤ ::ₘ Γ)
  | quest : Proof (a ::ₘ Γ) → Proof (ʔa ::ₘ Γ)
  | weaken : Proof Γ → Proof (ʔa ::ₘ Γ)
  | contract : Proof (ʔa ::ₘ ʔa ::ₘ Γ) → Proof (ʔa ::ₘ Γ)
  | bang {Γ : Sequent Atom} {a} : Γ.allQuest → Proof (a ::ₘ Γ) → Proof ((!a) ::ₘ Γ)
  -- No rule for zero.

@[inherit_doc]
scoped notation "⇓" Γ:90 => Proof Γ

@[scoped grind .]
def Proof.sequent_rw (h : Γ = Δ) (p : ⇓Γ) : ⇓Δ := by rw [h] at p; exact p

/-- A sequent is provable if there exists a proof that concludes it. -/
@[scoped grind =]
def Sequent.Provable (Γ : Sequent Atom) := Nonempty (⇓Γ)

/-- Having a proof of Γ shows that it is provable. -/
theorem Sequent.Provable.fromProof {Γ : Sequent Atom} (p : ⇓Γ) : Γ.Provable := ⟨p⟩

/-- Having a proof of Γ shows that it is provable. -/
@[scoped grind .]
noncomputable def Sequent.Provable.toProof {Γ : Sequent Atom} (p : Γ.Provable) : ⇓Γ :=
  Classical.choice p

instance : Coe (Proof Γ) (Γ.Provable) where
  coe p := Sequent.Provable.fromProof p

noncomputable instance : Coe (Γ.Provable) (Proof Γ) where
  coe p := p.toProof

/-- The axiom, but where the order of propositions is reversed. -/
@[scoped grind <=]
def Proof.ax' {a : Proposition Atom} : ⇓{a⫠, a} := by
  rw [Multiset.pair_comm]
  exact Proof.ax

/-- Cut, but where the premises are reversed. -/
@[scoped grind .]
def Proof.cut' (p : ⇓(a⫠ ::ₘ Γ)) (q : ⇓(a ::ₘ Δ)) : ⇓(Γ + Δ) :=
  let r : ⇓(a⫠⫠ ::ₘ Δ) := by
    rw [← Proposition.dual.involution a] at q
    exact q
  p.cut r

/-- Inversion of the ⅋ rule. -/
@[scoped grind .]
def Proof.parr_inversion {a b} {Γ : Sequent Atom}
  (h : ⇓((a ⅋ b) ::ₘ Γ)) : ⇓(a ::ₘ b ::ₘ Γ) := by
  have : (a ::ₘ b ::ₘ Γ) = ({a, b} + Γ) := by simp
  rw [this]
  apply Proof.cut' (a := (a ⅋ b)) (Γ := {a, b}) (Δ := Γ)
  · simp only [Proposition.dual]
    have : ({a, b} : Sequent Atom) = ({a} + {b}) := by simp
    rw [this]
    apply Proof.tensor (Γ := {a}) <;> exact Proof.ax'
  · exact h

/-- Inversion of the ⊥ rule. -/
@[scoped grind .]
def Proof.bot_inversion {Γ : Sequent Atom} (h : ⇓(⊥ ::ₘ Γ)) : ⇓Γ := by
  convert Proof.cut' (a := ⊥) (Γ := {}) (Δ := Γ) Proof.one h
  simp

/-- Inversion of the & rule, first component. -/
@[scoped grind .]
def Proof.with_inversion₁ {a b : Proposition Atom} {Γ : Sequent Atom}
    (h : ⇓((a & b) ::ₘ Γ)) : ⇓(a ::ₘ Γ) := by
  apply Proof.cut' (a := a & b) (Γ := [a]) (Δ := Γ)
  · exact Proof.oplus₁ Proof.ax'
  · exact h

/-- Inversion of the & rule, second component. -/
@[scoped grind .]
def Proof.with_inversion₂ {a b : Proposition Atom} {Γ : Sequent Atom}
    (h : ⇓((a & b) ::ₘ Γ)) : ⇓(b ::ₘ Γ) := by
  apply Proof.cut' (a := a & b) (Γ := [b]) (Δ := Γ)
  · exact Proof.oplus₂ Proof.ax'
  · exact h

section LogicalEquiv

/-! ## Logical equivalences -/

/-- Two propositions are equivalent if one implies the other and vice versa.
Proof-relevant version. -/
def Proposition.equiv (a b : Proposition Atom) := ⇓{a⫠, b} × ⇓{b⫠, a}

open Sequent in
/-- Propositional equivalence, proof-irrelevant version (`Prop`). -/
def Proposition.Equiv (a b : Proposition Atom) := Provable {a⫠, b} ∧ Provable {b⫠, a}

/-- Conversion from proof-relevant to proof-irrelevant versions of propositional
equivalence. -/
theorem Proposition.equiv.toProp (h : Proposition.equiv a b) : Proposition.Equiv a b := by
  obtain ⟨p, q⟩ := h
  apply Sequent.Provable.fromProof at p
  apply Sequent.Provable.fromProof at q
  constructor <;> assumption

scoped infix:29 " ≡⇓ " => Proposition.equiv
scoped infix:29 " ≡ " => Proposition.Equiv

/-- Proof-relevant equivalence is coerciable into proof-irrelevant equivalence. -/
instance {a b : Proposition Atom} : Coe (a ≡⇓ b) (a ≡ b) where
  coe := Proposition.equiv.toProp

noncomputable def Proposition.chooseEquiv (h : a ≡ b) : a ≡⇓ b :=
  ⟨h.1.toProof, h.2.toProof⟩

namespace Proposition

open Sequent

@[scoped grind .]
def equiv.refl (a : Proposition Atom) : a ≡⇓ a := by
  constructor <;> exact Proof.ax'

@[scoped grind .]
def equiv.symm (a : Proposition Atom) (h : a ≡⇓ b) : b ≡⇓ a := ⟨h.2, h.1⟩

@[scoped grind .]
def equiv.trans {a b c : Proposition Atom} (hab : a ≡⇓ b) (hbc : b ≡⇓ c) : a ≡⇓ c := by
  constructor
  · obtain ⟨hab1, _⟩ := hab
    rw [Multiset.pair_comm] at hab1
    apply hab1.cut hbc.1
  · obtain ⟨_, hbc2⟩ := hbc
    rw [Multiset.pair_comm] at hbc2
    apply hbc2.cut hab.2

@[refl, scoped grind .]
theorem Equiv.refl (a : Proposition Atom) : a ≡ a := equiv.refl a

@[symm, scoped grind .]
theorem Equiv.symm {a b : Proposition Atom} (h : a ≡ b) : b ≡ a := ⟨h.2, h.1⟩

@[scoped grind .]
theorem Equiv.trans {a b c : Proposition Atom} (hab : a ≡ b) (hbc : b ≡ c) : a ≡ c :=
  ⟨
    Provable.fromProof
      (Proof.cut (hab.1.toProof.sequent_rw (Multiset.pair_comm _ _)) hbc.1.toProof),
    Provable.fromProof
      (Proof.cut (hbc.2.toProof.sequent_rw (Multiset.pair_comm _ _)) hab.2.toProof)
  ⟩

/-- The canonical equivalence relation for propositions. -/
def propositionSetoid : Setoid (Proposition Atom) :=
  ⟨Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

@[scoped grind .]
def bang_top_eqv_one : (!⊤ : Proposition Atom) ≡⇓ 1 := by
  constructor
  · apply Proof.weaken
    exact Proof.one
  · apply Proof.bot
    apply Proof.bang
    · rfl
    · exact Proof.top

@[scoped grind .]
def quest_zero_eqv_bot : (ʔ0 : Proposition Atom) ≡⇓ ⊥ := by
  constructor
  · simp only [Proposition.dual]
    apply Proof.sequent_rw (Multiset.pair_comm ..)
    apply Proof.bot
    apply Proof.bang
    · rfl
    · exact Proof.top
  · apply Proof.sequent_rw (Multiset.pair_comm ..)
    apply Proof.weaken
    exact Proof.one

@[scoped grind .]
def tensor_zero_eqv_zero (a : Proposition Atom) : a ⊗ 0 ≡⇓ 0 := by
  refine ⟨?_, .top⟩
  apply Proof.parr
  simp only [Proposition.dual]
  apply Proof.sequent_rw (Multiset.cons_swap ..)
  exact Proof.top

@[scoped grind .]
def parr_top_eqv_top (a : Proposition Atom) :
    a ⅋ ⊤ ≡⇓ ⊤ := by
  constructor
  · apply Proof.sequent_rw (Multiset.cons_swap ..)
    exact Proof.top
  · apply Proof.sequent_rw (Multiset.cons_swap ..)
    apply Proof.parr
    apply Proof.sequent_rw (Multiset.cons_swap ..)
    exact Proof.top

attribute [scoped grind _=_] Multiset.singleton_add
attribute [scoped grind =] Multiset.add_comm
attribute [scoped grind =] Multiset.add_assoc

open scoped Multiset in
@[scoped grind .]
def tensor_distrib_oplus (a b c : Proposition Atom) :
    a ⊗ (b ⊕ c) ≡⇓ (a ⊗ b) ⊕ (a ⊗ c) := by
  constructor
  · apply Proof.parr
    apply Proof.sequent_rw (Multiset.cons_swap ..)
    apply Proof.with
    · have : (b⫠ ::ₘ a⫠ ::ₘ {(a ⊗ b) ⊕ (a ⊗ c)}) = (((a ⊗ b) ⊕ (a ⊗ c)) ::ₘ ({a⫠} + {b⫠})) :=
        by grind
      rw [this]
      apply Proof.oplus₁
      apply Proof.tensor <;> exact Proof.ax
    · have : (c⫠ ::ₘ a⫠ ::ₘ {(a ⊗ b) ⊕ (a ⊗ c)}) = (((a ⊗ b) ⊕ (a ⊗ c)) ::ₘ ({a⫠} + {c⫠})) :=
        by grind
      rw [this]
      apply Proof.oplus₂
      apply Proof.tensor <;> exact Proof.ax
  · apply Proof.with
    · apply Proof.parr
      have : (a⫠ ::ₘ b⫠ ::ₘ {a ⊗ (b ⊕ c)}) = ((a ⊗ (b ⊕ c)) ::ₘ ({a⫠} + {b⫠})) := by grind
      rw [this]
      apply Proof.tensor
      · exact Proof.ax
      · apply Proof.oplus₁
        exact Proof.ax
    · apply Proof.parr
      have : (a⫠ ::ₘ c⫠ ::ₘ {a ⊗ (b ⊕ c)}) = ((a ⊗ (b ⊕ c)) ::ₘ ({a⫠} + {c⫠})) := by grind
      rw [this]
      apply Proof.tensor
      · exact Proof.ax
      · apply Proof.oplus₂
        exact Proof.ax

/-- The proposition at the head of a proof can be substituted by an equivalent
  proposition. -/
@[scoped grind .]
def subst_eqv_head {Γ : Sequent Atom} {a b : Proposition Atom}
    (heqv : a ≡⇓ b) (p : ⇓(a ::ₘ Γ)) : ⇓(b ::ₘ Γ) := by
  have : (b ::ₘ Γ) = Γ + {b} := by grind
  rw [this]
  apply p.cut heqv.1

open scoped Multiset in
/-- Any proposition in a proof (regardless of its position) can be substituted by
  an equivalent proposition. -/
@[scoped grind .]
def subst_eqv {Γ Δ : Sequent Atom} {a b : Proposition Atom}
    (heqv : a ≡⇓ b) (p : ⇓(Γ + {a} + Δ)) : ⇓(Γ + {b} + Δ) := by
  -- simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hr : ∀ a, (Γ + {a} + Δ) = a ::ₘ (Γ + Δ) := by grind
  rw [hr] at ⊢ p
  apply subst_eqv_head heqv p

@[scoped grind .]
def tensor_symm {a b : Proposition Atom} : a ⊗ b ≡⇓ b ⊗ a := by
  constructor
  · apply Proof.parr
    have : (a⫠ ::ₘ b⫠ ::ₘ {b ⊗ a}) = ((b ⊗ a) ::ₘ ({b⫠} + {a⫠})) := by grind
    rw [this]
    apply Proof.tensor <;> exact Proof.ax
  · apply Proof.parr
    have : (b⫠ ::ₘ a⫠ ::ₘ {a ⊗ b}) = ((a ⊗ b) ::ₘ ({a⫠} + {b⫠})) := by grind
    rw [this]
    apply Proof.tensor <;> exact Proof.ax

open scoped Multiset in
@[scoped grind .]
def tensor_assoc {a b c : Proposition Atom} : a ⊗ (b ⊗ c) ≡⇓ (a ⊗ b) ⊗ c := by
  constructor
  · apply Proof.parr
    rw [Multiset.cons_swap]
    apply Proof.parr
    have : (b⫠ ::ₘ c⫠ ::ₘ a⫠ ::ₘ {(a ⊗ b) ⊗ c}) =
        (((a ⊗ b) ⊗ c) ::ₘ (({a⫠} + {b⫠}) + {c⫠})) := by grind
    rw [this]
    apply Proof.tensor
    · apply Proof.tensor <;> exact Proof.ax
    · exact Proof.ax
  · apply Proof.parr
    apply Proof.parr
    have : (a⫠ ::ₘ b⫠ ::ₘ c⫠ ::ₘ {a ⊗ (b ⊗ c)}) = ((a ⊗ (b ⊗ c)) ::ₘ ({a⫠} + ({b⫠} + {c⫠}))) :=
      by grind
    rw [this]
    apply Proof.tensor
    · exact Proof.ax
    · apply Proof.tensor <;> exact Proof.ax

instance {Γ : Sequent Atom} :
    IsSymm (Proposition Atom) (fun a b => Sequent.Provable ((a ⊗ b) ::ₘ Γ)) where
  symm _ _ h := Sequent.Provable.fromProof (subst_eqv_head tensor_symm h.toProof)

@[scoped grind .]
def oplus_idem {a : Proposition Atom} : a ⊕ a ≡⇓ a := by
  constructor
  · apply Proof.with <;> exact Proof.ax'
  · have : ({a⫠, a ⊕ a} : Sequent Atom) = {a ⊕ a, a⫠} := by sorry
    rw [this]
    apply Proof.oplus₁
    exact Proof.ax

@[scoped grind .]
def with_idem {a : Proposition Atom} : a & a ≡⇓ a := by
  constructor
  · apply Proof.oplus₁
    exact Proof.ax'
  · have : ({a⫠, a & a} : Sequent Atom) = {a & a, a⫠} := by sorry
    rw [this]
    apply Proof.with <;> exact Proof.ax

end Proposition

end LogicalEquiv

end CLL

end Cslib
