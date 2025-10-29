/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

-- TODO: Syntax elaboration conflicts 
-- import Cslib.Init
import Aesop
import Mathlib.Tactic.ApplyAt
import Mathlib.Order.Notation
import Mathlib.Order.Defs.Unbundled

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
def Proposition.Pos : Proposition Atom → Prop
  | atom _ => True
  | one => True
  | zero => True
  | tensor _ _ => True
  | oplus _ _ => True
  | bang _ => True
  | _ => False

/-- Negative propositions. -/
def Proposition.Neg : Proposition Atom → Prop
  | atomDual _ => True
  | bot => True
  | top => True
  | parr _ _ => True
  | .with _ _ => True
  | quest _ => True
  | _ => False

/-- Whether a `Proposition` is positive is decidable. -/
instance Proposition.pos_decidable (a : Proposition Atom) : Decidable a.Pos := by
  unfold Proposition.Pos
  split <;> infer_instance

/-- Whether a `Proposition` is negative is decidable. -/
instance Proposition.neg_decidable (a : Proposition Atom) : Decidable a.Neg := by
  unfold Proposition.Neg
  split <;> infer_instance

/-- Propositional duality. -/
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
theorem Proposition.dual.neq (a : Proposition Atom) : a ≠ a⫠ := by
  cases a <;> simp [Proposition.dual]

/-- Two propositions are equal iff their respective duals are equal. -/
@[grind =, simp]
theorem Proposition.dual_inj (a b : Proposition Atom) : a⫠ = b⫠ ↔ a = b := by
  refine ⟨fun h ↦ ?_, congrArg dual⟩
  induction a generalizing b <;> cases b
  all_goals aesop (add simp [Proposition.dual])

/-- Duality is an involution. -/
@[grind =, simp]
theorem Proposition.dual.involution (a : Proposition Atom) : a⫠⫠ = a := by
  induction a <;> simp_all [dual]

/-- Linear implication. -/
@[grind]
def Proposition.linImpl (a b : Proposition Atom) : Proposition Atom := a⫠ ⅋ b

@[inherit_doc] scoped infix:25 " ⊸ " => Proposition.linImpl

/-- A sequent in CLL is a list of propositions. -/
abbrev Sequent Atom := List (Proposition Atom)

-- TODO: This should become a Bool.
/-- Checks that all propositions in `Γ` are question marks. -/
def Sequent.AllQuest (Γ : Sequent Atom) :=
  ∀ a ∈ Γ, ∃ b, a = ʔb

open Proposition in
/-- A proof in the sequent calculus for classical linear logic. -/
inductive Proof : Sequent Atom → Type u where
  | ax : Proof [a, a⫠]
  | cut : Proof (a :: Γ) → Proof (a⫠ :: Δ) → Proof (Γ ++ Δ)
  | exchange : List.Perm Γ Δ → Proof Γ → Proof Δ
  | one : Proof [1]
  | bot : Proof Γ → Proof (⊥ :: Γ)
  | parr : Proof (a :: b :: Γ) → Proof ((a ⅋ b) :: Γ)
  | tensor : Proof (a :: Γ) → Proof (b :: Δ) → Proof ((a ⊗ b) :: (Γ ++ Δ))
  | oplus₁ : Proof (a :: Γ) → Proof ((a ⊕ b) :: Γ)
  | oplus₂ : Proof (b :: Γ) → Proof ((a ⊕ b) :: Γ)
  | with : Proof (a :: Γ) → Proof (b :: Γ) → Proof ((a & b) :: Γ)
  | top : Proof (⊤ :: Γ)
  | quest : Proof (a :: Γ) → Proof (ʔa :: Γ)
  | weaken : Proof Γ → Proof (ʔa :: Γ)
  | contract : Proof (ʔa :: ʔa :: Γ) → Proof (ʔa :: Γ)
  | bang {Γ : Sequent Atom} {a} : Γ.AllQuest → Proof (a :: Γ) → Proof ((!a) :: Γ)
  -- No rule for zero.

/-- A sequent is provable if there exists a proof that concludes it. -/
@[grind]
def Provable (Γ : Sequent Atom) := Nonempty (Proof Γ)

@[inherit_doc]
scoped notation "⇓" Γ:90 => Proof Γ

@[inherit_doc]
scoped notation "⊢" Γ:90 => Provable Γ

/-- Having a proof of Γ shows that it is provable. -/
theorem Provable.fromProof {Γ : Sequent Atom} (p : ⇓Γ) : ⊢Γ := ⟨p⟩

/-- Having a proof of Γ shows that it is provable. -/
@[grind]
noncomputable def Provable.toProof {Γ : Sequent Atom} (p : ⊢Γ) : ⇓Γ := Classical.choice p

@[grind]
instance : Coe (Proof Γ) (Provable Γ) where
  coe p := Provable.fromProof p

@[grind]
noncomputable instance : Coe (Provable Γ) (Proof Γ) where
  coe p := p.toProof

/-- The axiom, but where the order of propositions is reversed. -/
def Proof.ax' {a : Proposition Atom} : ⇓[a⫠, a] :=
  Proof.exchange (List.Perm.swap ..) Proof.ax

/-- Cut, but where the premises are reversed. -/
def Proof.cut' (p : ⇓(a⫠ :: Γ)) (q : ⇓(a :: Δ)) : ⇓(Γ ++ Δ) :=
  let r : ⇓(a⫠⫠ :: Δ) := by
    rw [← Proposition.dual.involution a] at q
    exact q
  p.cut r

/-- Inversion of the ⅋ rule. -/
def Proof.parr_inversion {a b} {Γ : Sequent Atom}
  (h : ⇓((a ⅋ b) :: Γ)) : ⇓(a :: b :: Γ) := by
  apply Proof.cut' (a := (a ⅋ b)) (Γ := [a, b]) (Δ := Γ)
  · apply Proof.tensor (Γ := [a]) <;> exact Proof.ax'
  · exact h

/-- Inversion of the ⊥ rule. -/
def Proof.bot_inversion {Γ : Sequent Atom} (h : ⇓(⊥ :: Γ)) : ⇓Γ := by
  apply Proof.cut' (a := ⊥) (Γ := []) (Δ := Γ)
  · exact Proof.one
  · exact h

/-- Inversion of the & rule, first component. -/
def Proof.with_inversion₁ {a b : Proposition Atom} {Γ : Sequent Atom}
    (h : ⇓((a & b) :: Γ)) : ⇓(a :: Γ) := by
  apply Proof.cut' (a := a & b) (Γ := [a]) (Δ := Γ)
  · exact Proof.oplus₁ Proof.ax'
  · exact h

/-- Inversion of the & rule, second component. -/
def Proof.with_inversion₂ {a b : Proposition Atom} {Γ : Sequent Atom}
    (h : ⇓((a & b) :: Γ)) : ⇓(b :: Γ) := by
  apply Proof.cut' (a := a & b) (Γ := [b]) (Δ := Γ)
  · exact Proof.oplus₂ Proof.ax'
  · exact h

section LogicalEquiv

/-! ## Logical equivalences -/

/-- Two propositions are equivalent if one implies the other and vice versa.
Proof-relevant version. -/
def Proposition.equiv (a b : Proposition Atom) := ⇓[a⫠, b] × ⇓[b⫠, a]

/-- Propositional equivalence, proof-irrelevant version (`Prop`). -/
def Proposition.Equiv (a b : Proposition Atom) := ⊢[a⫠, b] ∧ ⊢[b⫠, a]

/-- Conversion from proof-relevant to proof-irrelevant versions of propositional
equivalence. -/
theorem Proposition.equiv.toProp (h : Proposition.equiv a b) : Proposition.Equiv a b := by
  obtain ⟨p, q⟩ := h
  apply Provable.fromProof at p
  apply Provable.fromProof at q
  constructor <;> assumption

instance {a b : Proposition Atom} : Coe (a.equiv b) (a.Equiv b) where
  coe := Proposition.equiv.toProp

scoped infix:29 " ≡ " => Proposition.Equiv

namespace Proposition

def equiv.refl (a : Proposition Atom) : a.equiv a := by
  constructor <;> (
    apply Proof.exchange (List.Perm.swap ..)
    exact Proof.ax
  )

@[refl]
theorem Equiv.refl (a : Proposition Atom) : a ≡ a := equiv.refl a

@[symm]
theorem Equiv.symm {a b : Proposition Atom} (h : a ≡ b) : b ≡ a := ⟨h.2, h.1⟩

theorem Equiv.trans {a b c : Proposition Atom} (hab : a ≡ b) (hbc : b ≡ c) : a ≡ c :=
  ⟨
    Provable.fromProof (Proof.cut (Proof.exchange (List.Perm.swap ..) hab.1.toProof) hbc.1),
    Provable.fromProof (Proof.cut (Proof.exchange (List.Perm.swap ..) hbc.2.toProof) hab.2)
  ⟩

/-- The canonical equivalence relation for propositions. -/
def propositionSetoid : Setoid (Proposition Atom) :=
  ⟨Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

/- TODO: Proof-relevant logical equivalences.

Logical equivalences should have definitions of concrete proofs first, and then
have accompanying theorems derived through `Proposition.equiv.toProp`.
labels: logic
-/

theorem bang_top_eqv_one : (!⊤ : Proposition Atom) ≡ 1 := by
  constructor
  · apply Provable.fromProof
    apply Proof.weaken
    exact Proof.one
  · apply Provable.fromProof
    apply Proof.bot
    apply Proof.bang
    · intro _ _; contradiction
    exact Proof.top

theorem quest_zero_eqv_bot : (ʔ0 : Proposition Atom) ≡ ⊥ := by
  constructor
  · apply Provable.fromProof
    apply Proof.exchange (List.Perm.swap (bang top) bot [])
    apply Proof.bot
    apply Proof.bang
    · intro _ _; contradiction
    exact Proof.top
  · apply Provable.fromProof
    apply Proof.exchange (List.Perm.swap one (quest zero) [])
    apply Proof.weaken
    exact Proof.one

theorem tensor_zero_eqv_zero (a : Proposition Atom) : a ⊗ 0 ≡ 0 := by
  refine ⟨Provable.fromProof ?_, Provable.fromProof .top⟩
  apply Proof.parr
  apply Proof.exchange (List.Perm.swap a⫠ ⊤ [0])
  exact Proof.top

theorem parr_top_eqv_top (a : Proposition Atom) :
    a ⅋ ⊤ ≡ ⊤ := by
  constructor
  · apply Provable.fromProof
    apply Proof.exchange (List.Perm.swap (parr a top)⫠ top [])
    exact Proof.top
  · apply Provable.fromProof
    apply Proof.exchange (List.Perm.swap top⫠ (parr a top) [])
    apply Proof.parr
    apply Proof.exchange (List.Perm.swap a top [top⫠])
    exact Proof.top

theorem tensor_distrib_oplus (a b c : Proposition Atom) :
    a ⊗ (b ⊕ c) ≡ (a ⊗ b) ⊕ (a ⊗ c) := by
  constructor
  · apply Provable.fromProof
    apply Proof.parr
    apply Proof.exchange (List.Perm.swap a⫠ (.with b⫠ c⫠) _)
    apply Proof.with
    · apply Proof.exchange (List.reverse_perm _)
      apply Proof.oplus₁
      apply Proof.tensor (Γ := [a⫠]) <;> exact Proof.ax
    · apply Proof.exchange (List.reverse_perm _)
      apply Proof.oplus₂
      apply Proof.tensor (Γ := [a⫠]) <;> exact Proof.ax
  · apply Provable.fromProof
    apply Proof.with
    · apply Proof.parr
      apply Proof.exchange
        (List.Perm.trans (List.Perm.swap ..) (List.Perm.cons _ (List.Perm.swap ..)))
      apply Proof.tensor (Γ := [a⫠])
      · exact Proof.ax
      · apply Proof.oplus₁
        exact Proof.ax
    · apply Proof.parr
      apply Proof.exchange
        (List.Perm.trans (List.Perm.swap ..) (List.Perm.cons _ (List.Perm.swap ..)))
      apply Proof.tensor (Γ := [a⫠])
      · exact Proof.ax
      · apply Proof.oplus₂
        exact Proof.ax

/- TODO: Proof-relevant substitution principles for logical equivalence in CLL.

`subst_eqv_head` and `subst_eqv` should be defined using `Proposition.equiv` first, and then
have accompanying theorems for `Proposition.Equiv`.
labels: logic
-/
/-- The proposition at the head of a proof can be substituted by an equivalent
  proposition. -/
theorem subst_eqv_head {Γ : Sequent Atom} {a b : Proposition Atom} (heqv : a ≡ b) :
  ⊢(a :: Γ) → ⊢(b :: Γ) :=
  fun h => Proof.exchange (List.perm_append_singleton b Γ) (Proof.cut h heqv.left.toProof)

/-- Any proposition in a proof (regardless of its position) can be substituted by
  an equivalent proposition. -/
theorem subst_eqv {Γ Δ : Sequent Atom} {a b : Proposition Atom} (heqv : a ≡ b) :
  ⊢(Γ ++ [a] ++ Δ) → ⊢(Γ ++ [b] ++ Δ) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    intro h
    apply Provable.fromProof
    apply Proof.exchange (List.perm_middle.symm)
    apply Provable.toProof at h
    apply Proof.exchange (List.perm_middle) at h
    apply Provable.toProof
    apply subst_eqv_head heqv h

theorem tensor_symm {a b : Proposition Atom} : a ⊗ b ≡ b ⊗ a := by
  constructor
  · apply Provable.fromProof
    apply Proof.parr
    apply Proof.exchange (List.reverse_perm _)
    apply Proof.tensor (Γ := [b⫠]) <;> exact Proof.ax
  · apply Provable.fromProof
    apply Proof.parr
    apply Proof.exchange (List.reverse_perm _)
    apply Proof.tensor (Γ := [a⫠]) <;> exact Proof.ax

theorem tensor_assoc {a b c : Proposition Atom} : a ⊗ (b ⊗ c) ≡ (a ⊗ b) ⊗ c := by
  constructor
  · apply Provable.fromProof
    apply Proof.parr
    apply Proof.exchange (List.Perm.swap ..)
    apply Proof.parr
    apply Proof.exchange (List.Perm.swap ..)
    apply Proof.exchange (List.reverse_perm _)
    apply Proof.tensor (Γ := [a⫠, b⫠])
    · apply Proof.tensor (Γ := [a⫠]) <;> exact Proof.ax
    · exact Proof.ax
  · apply Provable.fromProof
    apply Proof.parr
    apply Proof.parr
    apply Proof.exchange (List.reverse_perm _)
    apply Proof.exchange (List.Perm.cons _ (List.reverse_perm _))
    apply Proof.tensor (Γ := [a⫠])
    · exact Proof.ax
    · apply Proof.tensor (Γ := [b⫠]) <;> exact Proof.ax

instance {Γ : Sequent Atom} : IsSymm (Proposition Atom) (fun a b => ⊢((a ⊗ b) :: Γ)) where
  symm := fun _ _ => subst_eqv_head tensor_symm

theorem oplus_idem {a : Proposition Atom} : a ⊕ a ≡ a := by
  constructor <;> apply Provable.fromProof
  · apply Proof.with <;> exact Proof.ax'
  · apply Proof.exchange (List.Perm.swap ..)
    apply Proof.oplus₁
    exact Proof.ax

theorem with_idem {a : Proposition Atom} : a & a ≡ a := by
  constructor <;> apply Provable.fromProof
  · apply Proof.oplus₁
    exact Proof.ax'
  · apply Proof.exchange (List.Perm.swap ..)
    apply Proof.with <;> exact Proof.ax

end Proposition

end LogicalEquiv

end CLL

end Cslib
