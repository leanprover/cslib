/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init
public import Cslib.Foundations.Syntax.Context
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.LogicalEquivalence
public import Mathlib.Data.Multiset.Fold

@[expose] public section

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

/-- Propositional contexts (single-hole contexts for propositions). -/
inductive Proposition.Context (Atom : Type u) : Type u where
  | hole
  | tensorL (c : Context Atom) (b : Proposition Atom)
  | tensorR (a : Proposition Atom) (c : Context Atom)
  | parrL (c : Context Atom) (b : Proposition Atom)
  | parrR (a : Proposition Atom) (c : Context Atom)
  | oplusL (c : Context Atom) (b : Proposition Atom)
  | oplusR (a : Proposition Atom) (c : Context Atom)
  | withL (c : Context Atom) (b : Proposition Atom)
  | withR (a : Proposition Atom) (c : Context Atom)
  | bang (c : Context Atom)
  | quest (c : Context Atom)
deriving DecidableEq, BEq

/-- Replaces the hole in a propositional context with a propositions. -/
@[scoped grind =]
def Proposition.Context.fill (c : Context Atom) (a : Proposition Atom) : Proposition Atom :=
  match c with
  | hole => a
  | tensorL c b => .tensor (c.fill a) b
  | tensorR b c => .tensor b (c.fill a)
  | parrL c b => .parr (c.fill a) b
  | parrR b c => .parr b (c.fill a)
  | oplusL c b => .oplus (c.fill a) b
  | oplusR b c => .oplus b (c.fill a)
  | withL c b => .with (c.fill a) b
  | withR b c => .with b (c.fill a)
  | bang c => .bang (c.fill a)
  | quest c => .quest (c.fill a)

instance : HasContext (Proposition Atom) := ⟨Proposition.Context Atom, Proposition.Context.fill⟩

/-- Definition of context filling. -/
@[scoped grind =]
theorem Proposition.context_fill_def (c : Context Atom) (a : Proposition Atom) :
  c<[a] = c.fill a := rfl

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
instance Proposition.positive_decidable (a : Proposition Atom) : Decidable a.positive :=
  a.positive.decEq true

/-- Whether a `Proposition` is negative is decidable. -/
instance Proposition.negative_decidable (a : Proposition Atom) : Decidable a.negative :=
  a.negative.decEq true

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

@[scoped grind =]
theorem Proposition.top_eq_zero_dual : ⊤ = (0⫠ : Proposition Atom) := rfl

/-- Duality preserves size. -/
@[scoped grind _=_]
theorem Proposition.dual_sizeOf (a : Proposition Atom) : sizeOf a = sizeOf a⫠ := by
  induction a <;> simp [dual] <;> grind

/-- No proposition is equal to its dual. -/
@[scoped grind .]
theorem Proposition.dual_neq (a : Proposition Atom) : a ≠ a⫠ := by
  cases a <;> simp [Proposition.dual]

/-- Two propositions are equal iff their respective duals are equal. -/
@[scoped grind =, simp]
theorem Proposition.dual_inj (a b : Proposition Atom) : a⫠ = b⫠ ↔ a = b := by
  refine ⟨fun h ↦ ?_, congrArg dual⟩
  induction a generalizing b <;> cases b <;> grind

/-- Duality is an involution. -/
@[scoped grind =, simp]
theorem Proposition.dual_involution (a : Proposition Atom) : a⫠⫠ = a := by
  induction a <;> grind [dual]

/-- Linear implication. -/
@[scoped grind =]
def Proposition.linImpl (a b : Proposition Atom) : Proposition Atom := a⫠ ⅋ b

@[inherit_doc] scoped infix:25 " ⊸ " => Proposition.linImpl

/-- A sequent in CLL is a multiset of propositions. -/
abbrev Sequent Atom := Multiset (Proposition Atom)

/-- Checks that all propositions in a sequent `Γ` are question marks. -/
def Sequent.allQuest (Γ : Sequent Atom) :=
  Γ.map (· matches ʔ_)
  |> Multiset.fold Bool.and true

/-- Judgemental contexts for CLL. -/
def Sequent.Context Atom := Sequent Atom

/-- Filling a judgemental context returns a sequent. -/
def Sequent.Context.fill (Γc : Sequent.Context Atom) (a : Proposition Atom) := a ::ₘ Γc

instance : HasHContext (Sequent Atom) (Proposition Atom) :=
  ⟨Sequent.Context Atom, Sequent.Context.fill⟩

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

open Logic

instance : InferenceSystem (Sequent Atom) := ⟨Proof⟩

open InferenceSystem

/-- Convenience definition for rewriting conclusions in proofs. -/
@[scoped grind =]
def Proof.rwConclusion {Γ Δ : Sequent Atom} (h : Γ = Δ) (p : ⇓Γ) := InferenceSystem.rwConclusion h p

/-- The axiom, but where the order of propositions is reversed. -/
@[scoped grind <=]
def Proof.ax' {a : Proposition Atom} : ⇓({a⫠, a} : Sequent Atom) :=
  Multiset.pair_comm a (a⫠) ▸ Proof.ax

/-- Cut, but where the premises are reversed. -/
@[scoped grind =]
def Proof.cut' (p : ⇓(a⫠ ::ₘ Γ)) (q : ⇓(a ::ₘ Δ)) : ⇓(Γ + Δ) :=
  let r : ⇓(a⫠⫠ ::ₘ Δ) := (Proposition.dual_involution a).symm ▸ q
  p.cut r

/-- Inversion of the ⅋ rule. -/
@[scoped grind =]
def Proof.parr_inversion {Γ : Sequent Atom} (h : ⇓((a ⅋ b) ::ₘ Γ)) : ⇓(a ::ₘ b ::ₘ Γ) :=
  show a ::ₘ b ::ₘ Γ = {a, b} + Γ by simp ▸
    cut' (show ({a, b} : Sequent Atom) = {a} + {b} by simp ▸ tensor ax' ax') h

/-- Inversion of the ⊥ rule. -/
@[scoped grind =]
def Proof.bot_inversion {Γ : Sequent Atom} (h : ⇓(⊥ ::ₘ Γ)) : ⇓Γ := by
  convert Proof.cut' (a := ⊥) (Γ := {}) (Δ := Γ) Proof.one h
  simp

/-- Inversion of the & rule, first component. -/
@[scoped grind =]
def Proof.with_inversion₁ {Γ : Sequent Atom} (h : ⇓((a & b) ::ₘ Γ)) : ⇓(a ::ₘ Γ) :=
  cut' (a := a & b) (oplus₁ ax') h

/-- Inversion of the & rule, second component. -/
@[scoped grind =]
def Proof.with_inversion₂ {Γ : Sequent Atom} (h : ⇓((a & b) ::ₘ Γ)) : ⇓(b ::ₘ Γ) :=
  cut' (a := a & b) (oplus₂ ax') h

section LogicalEquiv

/-! ## Logical equivalences -/

/-- Two propositions are equivalent if one implies the other and vice versa.
Proof-relevant version. -/
def Proposition.equiv (a b : Proposition Atom) :=
  ⇓({a⫠, b} : Sequent Atom) × ⇓({b⫠, a} : Sequent Atom)

@[inherit_doc]
scoped infix:29 " ≡⇓ " => Proposition.equiv

open Sequent in
/-- Propositional equivalence, proof-irrelevant version (`Prop`). -/
def Proposition.Equiv (a b : Proposition Atom) :=
  Derivable ({a⫠, b} : Sequent Atom) ∧ Derivable ({b⫠, a} : Sequent Atom)

@[inherit_doc]
scoped infix:29 " ≡ " => Proposition.Equiv

/-- Conversion from proof-relevant to proof-irrelevant versions of propositional
equivalence. -/
theorem Proposition.equiv.toProp (h : a ≡⇓ b) : a ≡ b := ⟨h.1, h.2⟩

/-- Proof-relevant equivalence is coerciable into proof-irrelevant equivalence. -/
instance : Coe (a ≡⇓ b) (a ≡ b) := ⟨Proposition.equiv.toProp⟩

/-- Transforms a proof-irrelevant equivalence into a proof-relevant one (this is not computable). -/
noncomputable def chooseEquiv (h : a ≡ b) : a ≡⇓ b := ⟨h.1, h.2⟩

namespace Proposition

open Sequent

/-- Proof-relevant equivalence is reflexive. -/
@[scoped grind =]
def equiv.refl (a : Proposition Atom) : a ≡⇓ a := ⟨Proof.ax', Proof.ax'⟩

/-- Proof-relevant equivalence is symmetric. -/
@[scoped grind =]
def equiv.symm (a : Proposition Atom) (h : a ≡⇓ b) : b ≡⇓ a := ⟨h.2, h.1⟩

/-- Proof-relevant equivalence is transitive. -/
@[scoped grind =]
def equiv.trans {a b c : Proposition Atom} (hab : a ≡⇓ b) (hbc : b ≡⇓ c) : a ≡⇓ c :=
  ⟨(Multiset.pair_comm b (a⫠) ▸ hab.fst).cut hbc.fst,
   (Multiset.pair_comm b (c⫠) ▸ hbc.snd).cut hab.snd⟩

/-- Proof-irrelevant equivalence is reflexive. -/
@[refl, scoped grind .]
theorem Equiv.refl (a : Proposition Atom) : a ≡ a := equiv.refl a

/-- Proof-irrelevant equivalence is symmetric. -/
@[symm, scoped grind →]
theorem Equiv.symm {a b : Proposition Atom} (h : a ≡ b) : b ≡ a := ⟨h.2, h.1⟩

/-- Proof-irrelevant equivalence is transitive. -/
@[scoped grind →]
theorem Equiv.trans {a b c : Proposition Atom} (hab : a ≡ b) (hbc : b ≡ c) : a ≡ c :=
  equiv.trans (chooseEquiv hab) (chooseEquiv hbc)

/-- The canonical equivalence relation for propositions. -/
def propositionSetoid : Setoid (Proposition Atom) :=
  ⟨Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

instance : IsEquiv (Proposition Atom) Proposition.Equiv where
  refl := Equiv.refl
  symm a b := Equiv.symm (a := a) (b := b)
  trans a b c := Equiv.trans (a := a) (b := b) (c := c)

/-- !⊤ ≡⇓ 1 -/
@[scoped grind =]
def bang_top_eqv_one : (!⊤ : Proposition Atom) ≡⇓ 1 :=
  ⟨.weaken .one, .bot (.bang rfl .top)⟩

/-- ʔ0 ≡⇓ ⊥ -/
@[scoped grind =]
def quest_zero_eqv_bot : (ʔ0 : Proposition Atom) ≡⇓ ⊥ :=
  ⟨rwConclusion (Multiset.pair_comm ..) <| .bot (.bang rfl .top),
   rwConclusion (Multiset.pair_comm ..) <| .weaken .one⟩

/-- a ⊗ 0 ≡⇓ 0 -/
@[scoped grind =]
def tensor_zero_eqv_zero (a : Proposition Atom) : a ⊗ 0 ≡⇓ 0 :=
  ⟨.parr <| .rwConclusion (Multiset.cons_swap ..) .top, .top⟩

/-- a ⅋ ⊤ ≡⇓ ⊤ -/
@[scoped grind =]
def parr_top_eqv_top (a : Proposition Atom) : a ⅋ ⊤ ≡⇓ ⊤ :=
  ⟨.rwConclusion (Multiset.cons_swap ..) .top,
   .rwConclusion (Multiset.cons_swap ..) <| .parr <| .rwConclusion (Multiset.cons_swap ..) .top⟩

attribute [local grind _=_] Multiset.coe_eq_coe
attribute [local grind _=_] Multiset.cons_coe
attribute [local grind _=_] Multiset.singleton_add
attribute [local grind =] Multiset.add_comm
attribute [local grind =] Multiset.add_assoc
attribute [local grind =] Multiset.insert_eq_cons

open scoped Multiset in
/-- ⊗ distributed over ⊕. -/
@[scoped grind =]
def tensor_distrib_oplus (a b c : Proposition Atom) : a ⊗ (b ⊕ c) ≡⇓ (a ⊗ b) ⊕ (a ⊗ c) :=
  ⟨.parr <|
    .rwConclusion (Multiset.cons_swap ..) <|
    .with
      (show (b⫠ ::ₘ a⫠ ::ₘ {(a ⊗ b) ⊕ (a ⊗ c)}) = (((a ⊗ b) ⊕ (a ⊗ c)) ::ₘ ({a⫠} + {b⫠})) by grind ▸
       .oplus₁ (.tensor .ax .ax))
      (show (c⫠ ::ₘ a⫠ ::ₘ {(a ⊗ b) ⊕ (a ⊗ c)}) = (((a ⊗ b) ⊕ (a ⊗ c)) ::ₘ ({a⫠} + {c⫠})) by grind ▸
      .oplus₂ (.tensor .ax .ax)),
   .with
      (.parr <|
        show (a⫠ ::ₘ b⫠ ::ₘ {a ⊗ (b ⊕ c)}) = ((a ⊗ (b ⊕ c)) ::ₘ ({a⫠} + {b⫠})) by grind ▸
        .tensor .ax (.oplus₁ .ax))
      (.parr <|
        show (a⫠ ::ₘ c⫠ ::ₘ {a ⊗ (b ⊕ c)}) = ((a ⊗ (b ⊕ c)) ::ₘ ({a⫠} + {c⫠})) by grind ▸
        .tensor .ax (.oplus₂ .ax))⟩

/-- The proposition at the head of a proof can be substituted by an equivalent
  proposition. -/
@[scoped grind =]
def subst_eqv_head {Γ : Sequent Atom} (heqv : a ≡⇓ b) (p : ⇓(a ::ₘ Γ)) : ⇓(b ::ₘ Γ) :=
  show b ::ₘ Γ = Γ + {b} by grind ▸ p.cut heqv.1

theorem add_middle_eq_cons {a : Proposition Atom} : Γ + {a} + Δ = a ::ₘ (Γ + Δ) := by
  grind

open scoped Multiset in
/-- Any proposition in a proof (regardless of its position) can be substituted by
  an equivalent proposition. -/
@[scoped grind =]
def subst_eqv {Γ Δ : Sequent Atom} (heqv : a ≡⇓ b) (p : ⇓(Γ + {a} + Δ)) : ⇓(Γ + {b} + Δ) :=
  add_middle_eq_cons ▸ subst_eqv_head heqv (add_middle_eq_cons ▸ p)

open scoped Context

@[local grind .]
private lemma Proposition.equiv_tensor₁ {a a' b : Proposition Atom} (h : a ≡ a') :
    a ⊗ b ≡ a' ⊗ b := by
  obtain ⟨h₁, h₂⟩ := h
  obtain h₁ := h₁.some
  obtain h₂ := h₂.some
  constructor
  case left =>
    constructor
    simp only [Proposition.dual]
    apply Proof.parr
    rw [show (a⫠ ::ₘ b⫠ ::ₘ {a' ⊗ b}) = ((a' ⊗ b) ::ₘ ({a⫠} + {b⫠})) by grind]
    apply Proof.tensor
    · apply h₁.rwConclusion (by grind)
    · exact Proof.ax
  case right =>
    constructor
    simp only [Proposition.dual]
    apply Proof.parr
    rw [show (a'⫠ ::ₘ b⫠ ::ₘ {a ⊗ b}) = ((a ⊗ b) ::ₘ ({a'⫠} + {b⫠})) by grind]
    apply Proof.tensor
    · apply h₂.rwConclusion (by grind)
    · exact Proof.ax

@[local grind .]
private lemma Proposition.equiv_tensor₂ {a b b' : Proposition Atom} (h : b ≡ b') :
    a ⊗ b ≡ a ⊗ b' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain h₁ := h₁.some
  obtain h₂ := h₂.some
  constructor
  case left =>
    constructor
    simp only [Proposition.dual]
    apply Proof.parr
    rw [show (a⫠ ::ₘ b⫠ ::ₘ {a ⊗ b'}) = ((a ⊗ b') ::ₘ ({a⫠} + {b⫠})) by grind]
    apply Proof.tensor
    · exact Proof.ax
    · apply h₁.rwConclusion (by grind)
  case right =>
    constructor
    simp only [Proposition.dual]
    apply Proof.parr
    rw [show (a⫠ ::ₘ b'⫠ ::ₘ {a ⊗ b}) = ((a ⊗ b) ::ₘ ({a⫠} + {b'⫠})) by grind]
    apply Proof.tensor
    · exact Proof.ax
    · apply h₂.rwConclusion (by grind)

@[local grind .]
private lemma Proposition.equiv_parr₁ {a a' b : Proposition Atom} (h : a ≡ a') :
    a ⅋ b ≡ a' ⅋ b := by
  obtain ⟨h₁, h₂⟩ := h
  obtain h₁ := h₁.some
  obtain h₂ := h₂.some
  constructor
  case left =>
    constructor
    simp only [Proposition.dual]
    rw [show {a⫠ ⊗ b⫠, a' ⅋ b} = (a' ⅋ b) ::ₘ {a⫠ ⊗ b⫠} by grind]
    apply Proof.parr
    rw [show (a' ::ₘ b ::ₘ {a⫠ ⊗ b⫠}) = ((a⫠ ⊗ b⫠) ::ₘ ({a'} + {b})) by grind]
    apply Proof.tensor
    · apply h₁.rwConclusion (by grind)
    · exact Proof.ax'
  case right =>
    constructor
    simp only [Proposition.dual]
    rw [show {a'⫠ ⊗ b⫠, a ⅋ b} = (a ⅋ b) ::ₘ {a'⫠ ⊗ b⫠} by grind]
    apply Proof.parr
    rw [show (a ::ₘ b ::ₘ {a'⫠ ⊗ b⫠}) = ((a'⫠ ⊗ b⫠) ::ₘ ({a} + {b})) by grind]
    apply Proof.tensor
    · apply h₂.rwConclusion (by grind)
    · exact Proof.ax'

@[local grind .]
private lemma Proposition.equiv_parr₂ {a b b' : Proposition Atom} (h : b ≡ b') :
    a ⅋ b ≡ a ⅋ b' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain h₁ := h₁.some
  obtain h₂ := h₂.some
  constructor
  case left =>
    constructor
    simp only [Proposition.dual]
    rw [show {a⫠ ⊗ b⫠, a ⅋ b'} = (a ⅋ b') ::ₘ {a⫠ ⊗ b⫠} by grind]
    apply Proof.parr
    rw [show (a ::ₘ b' ::ₘ {a⫠ ⊗ b⫠}) = ((a⫠ ⊗ b⫠) ::ₘ ({a} + {b'})) by grind]
    apply Proof.tensor
    · exact Proof.ax'
    · apply h₁.rwConclusion (by grind)
  case right =>
    constructor
    simp only [Proposition.dual]
    rw [show {a⫠ ⊗ b'⫠, a ⅋ b} = (a ⅋ b) ::ₘ {a⫠ ⊗ b'⫠} by grind]
    apply Proof.parr
    rw [show (a ::ₘ b ::ₘ {a⫠ ⊗ b'⫠}) = ((a⫠ ⊗ b'⫠) ::ₘ ({a} + {b})) by grind]
    apply Proof.tensor
    · exact Proof.ax'
    · apply h₂.rwConclusion (by grind)

@[local grind .]
private lemma Proposition.equiv_oplus₁ {a a' b : Proposition Atom} (h : a ≡ a') :
    a ⊕ b ≡ a' ⊕ b := by
  obtain ⟨h₁, h₂⟩ := h
  obtain h₁ := h₁.some
  obtain h₂ := h₂.some
  constructor
  case left =>
    constructor
    simp only [Proposition.dual]
    apply Proof.with
    · rw [show a⫠ ::ₘ {a' ⊕ b} = (a' ⊕ b) ::ₘ {a⫠} by grind]
      apply Proof.oplus₁
      apply h₁.rwConclusion (by grind)
    · rw [show b⫠ ::ₘ {a' ⊕ b} = (a' ⊕ b) ::ₘ {b⫠} by grind]
      apply Proof.oplus₂
      exact Proof.ax
  case right =>
    constructor
    simp only [Proposition.dual]
    apply Proof.with
    · rw [show a'⫠ ::ₘ {a ⊕ b} = (a ⊕ b) ::ₘ {a'⫠} by grind]
      apply Proof.oplus₁
      apply h₂.rwConclusion (by grind)
    · rw [show b⫠ ::ₘ {a ⊕ b} = (a ⊕ b) ::ₘ {b⫠} by grind]
      apply Proof.oplus₂
      exact Proof.ax

@[local grind .]
private lemma Proposition.equiv_oplus₂ {a b b' : Proposition Atom} (h : b ≡ b') :
    a ⊕ b ≡ a ⊕ b' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain h₁ := h₁.some
  obtain h₂ := h₂.some
  constructor
  case left =>
    constructor
    simp only [Proposition.dual]
    apply Proof.with
    · rw [show a⫠ ::ₘ {a ⊕ b'} = (a ⊕ b') ::ₘ {a⫠} by grind]
      apply Proof.oplus₁
      exact Proof.ax
    · rw [show b⫠ ::ₘ {a ⊕ b'} = (a ⊕ b') ::ₘ {b⫠} by grind]
      apply Proof.oplus₂
      apply h₁.rwConclusion (by grind)
  case right =>
    constructor
    simp only [Proposition.dual]
    apply Proof.with
    · rw [show a⫠ ::ₘ {a ⊕ b} = (a ⊕ b) ::ₘ {a⫠} by grind]
      apply Proof.oplus₁
      exact Proof.ax
    · rw [show b'⫠ ::ₘ {a ⊕ b} = (a ⊕ b) ::ₘ {b'⫠} by grind]
      apply Proof.oplus₂
      apply h₂.rwConclusion (by grind)

@[local grind .]
private lemma Proposition.equiv_with₁ {a a' b : Proposition Atom} (h : a ≡ a') :
    a & b ≡ a' & b := by
  obtain ⟨h₁, h₂⟩ := h
  obtain h₁ := h₁.some
  obtain h₂ := h₂.some
  constructor
  case left =>
    constructor
    simp only [Proposition.dual]
    rw [show {a⫠ ⊕ b⫠, a' & b} = (a' & b) ::ₘ {a⫠ ⊕ b⫠} by grind]
    apply Proof.with
    · rw [show a' ::ₘ {a⫠ ⊕ b⫠} = (a⫠ ⊕ b⫠) ::ₘ {a'} by grind]
      apply Proof.oplus₁
      apply h₁.rwConclusion (by grind)
    · rw [show b ::ₘ {a⫠ ⊕ b⫠} = (a⫠ ⊕ b⫠) ::ₘ {b} by grind]
      apply Proof.oplus₂
      exact Proof.ax'
  case right =>
    constructor
    simp only [Proposition.dual]
    rw [show {a'⫠ ⊕ b⫠, a & b} = (a & b) ::ₘ {a'⫠ ⊕ b⫠} by grind]
    apply Proof.with
    · rw [show a ::ₘ {a'⫠ ⊕ b⫠} = (a'⫠ ⊕ b⫠) ::ₘ {a} by grind]
      apply Proof.oplus₁
      apply h₂.rwConclusion (by grind)
    · rw [show b ::ₘ {a'⫠ ⊕ b⫠} = (a'⫠ ⊕ b⫠) ::ₘ {b} by grind]
      apply Proof.oplus₂
      exact Proof.ax'

@[local grind .]
private lemma Proposition.equiv_with₂ {a b b' : Proposition Atom} (h : b ≡ b') :
    a & b ≡ a & b' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain h₁ := h₁.some
  obtain h₂ := h₂.some
  constructor
  case left =>
    constructor
    simp only [Proposition.dual]
    rw [show {a⫠ ⊕ b⫠, a & b'} = (a & b') ::ₘ {a⫠ ⊕ b⫠} by grind]
    apply Proof.with
    · rw [show a ::ₘ {a⫠ ⊕ b⫠} = (a⫠ ⊕ b⫠) ::ₘ {a} by grind]
      apply Proof.oplus₁
      exact Proof.ax'
    · rw [show b' ::ₘ {a⫠ ⊕ b⫠} = (a⫠ ⊕ b⫠) ::ₘ {b'} by grind]
      apply Proof.oplus₂
      apply h₁.rwConclusion (by grind)
  case right =>
    constructor
    simp only [Proposition.dual]
    rw [show {a⫠ ⊕ b'⫠, a & b} = (a & b) ::ₘ {a⫠ ⊕ b'⫠} by grind]
    apply Proof.with
    · rw [show a ::ₘ {a⫠ ⊕ b'⫠} = (a⫠ ⊕ b'⫠) ::ₘ {a} by grind]
      apply Proof.oplus₁
      exact Proof.ax'
    · rw [show b ::ₘ {a⫠ ⊕ b'⫠} = (a⫠ ⊕ b'⫠) ::ₘ {b} by grind]
      apply Proof.oplus₂
      apply h₂.rwConclusion (by grind)

@[local grind .]
private lemma Proposition.equiv_bang {a a' : Proposition Atom} (h : a ≡ a') :
    !a ≡ !a' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain h₁ := h₁.some
  obtain h₂ := h₂.some
  constructor
  case left =>
    constructor
    simp only [Proposition.dual]
    rw [show {ʔa⫠, !a'} = (!a') ::ₘ {ʔa⫠} by grind]
    apply Proof.bang
    · simp [allQuest, Multiset.fold]
    · rw [show a' ::ₘ {ʔa⫠} = ʔa⫠ ::ₘ {a'} by grind]
      apply Proof.quest
      apply h₁.rwConclusion (by grind)
  case right =>
    constructor
    simp only [Proposition.dual]
    rw [show {ʔa'⫠, !a} = (!a) ::ₘ {ʔa'⫠} by grind]
    apply Proof.bang
    · simp [allQuest, Multiset.fold]
    · rw [show a ::ₘ {ʔa'⫠} = ʔa'⫠ ::ₘ {a} by grind]
      apply Proof.quest
      apply h₂.rwConclusion (by grind)

@[local grind .]
private lemma Proposition.equiv_quest {a a' : Proposition Atom} (h : a ≡ a') :
    ʔa ≡ ʔa' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain h₁ := h₁.some
  obtain h₂ := h₂.some
  constructor
  case left =>
    constructor
    simp only [Proposition.dual]
    apply Proof.bang
    · simp [allQuest, Multiset.fold]
    · rw [show a⫠ ::ₘ {ʔa'} = ʔa' ::ₘ {a⫠} by grind]
      apply Proof.quest
      apply h₁.rwConclusion (by grind)
  case right =>
    constructor
    simp only [Proposition.dual]
    apply Proof.bang
    · simp [allQuest, Multiset.fold]
    · rw [show a'⫠ ::ₘ {ʔa} = ʔa ::ₘ {a'⫠} by grind]
      apply Proof.quest
      apply h₂.rwConclusion (by grind)

instance : Congruence (Proposition Atom) Proposition.Equiv where
  elim :
      Covariant (Proposition.Context Atom) (Proposition Atom) (Proposition.Context.fill)
      Proposition.Equiv := by
    intro ctx a b hab
    induction ctx <;> grind

noncomputable instance : LogicalEquivalence (Proposition Atom) (Sequent Atom) Proof where
  eqv := Proposition.Equiv
  eqv_fill_valid {a b : Proposition Atom} (heqv : a.Equiv b)
      (c : HasHContext.Context (Sequent Atom) (Proposition Atom))
      (h : ⇓c<[a]) : ⇓c<[b] := by
    apply subst_eqv_head (chooseEquiv heqv) h

/-- Tensor is commutative. -/
@[scoped grind =]
def tensor_symm {a b : Proposition Atom} : a ⊗ b ≡⇓ b ⊗ a :=
  ⟨.parr <| show a⫠ ::ₘ b⫠ ::ₘ {b ⊗ a} = (b ⊗ a) ::ₘ {b⫠} + {a⫠} by grind ▸ .tensor .ax .ax,
   .parr <| show b⫠ ::ₘ a⫠ ::ₘ {a ⊗ b} = (a ⊗ b) ::ₘ {a⫠} + {b⫠} by grind ▸ .tensor .ax .ax⟩

-- TODO: the precedence on ⊗ notation is wrong
open scoped Multiset in
/-- ⊗ is associative. -/
@[scoped grind =]
def tensor_assoc {a b c : Proposition Atom} : a ⊗ (b ⊗ c) ≡⇓ (a ⊗ b) ⊗ c :=
  ⟨.parr <|
     Multiset.cons_swap .. ▸
     (.parr <|
      show b⫠ ::ₘ c⫠ ::ₘ a⫠ ::ₘ {(a ⊗ b) ⊗ c} = (((a ⊗ b) ⊗ c) ::ₘ ({a⫠} + {b⫠}) + {c⫠}) by grind ▸
      .tensor (.tensor .ax .ax) .ax),
   .parr <|
     .parr <|
     show a⫠ ::ₘ b⫠ ::ₘ c⫠ ::ₘ {a ⊗ (b ⊗ c)} = ((a ⊗ (b ⊗ c)) ::ₘ {a⫠} + ({b⫠} + {c⫠})) by grind ▸
     (.tensor .ax <| .tensor .ax .ax)⟩

instance {Γ : Sequent Atom} : Std.Symm (fun a b => Derivable ((a ⊗ b) ::ₘ Γ)) where
  symm _ _ h := Derivable.fromDerivation (subst_eqv_head tensor_symm (Derivable.toDerivation h))

/-- ⊕ is idempotent. -/
@[scoped grind =]
def oplus_idem {a : Proposition Atom} : a ⊕ a ≡⇓ a :=
  ⟨.with .ax' .ax',
   show ({a⫠, a ⊕ a} : Sequent Atom) = {a ⊕ a, a⫠} by grind ▸ .oplus₁ .ax⟩

/-- & is idempotent. -/
@[scoped grind =]
def with_idem {a : Proposition Atom} : a & a ≡⇓ a :=
  ⟨.oplus₁ .ax',
   show ({a⫠, a & a} : Sequent Atom) = {a & a, a⫠} by grind ▸ .with .ax .ax⟩

end Proposition

end LogicalEquiv

end CLL

end Cslib
