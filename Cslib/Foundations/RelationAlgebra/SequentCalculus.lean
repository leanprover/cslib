/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Basic
public import Cslib.Foundations.Logic.InferenceSystem.Defs

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

inductive Predicate (P : Type u) : Type u where
  | var (p : P)
  | one
  | sup (A B : Predicate P)
  | compl (A : Predicate P)
  | mul (A B : Predicate P)
  | star (A : Predicate P)

namespace Predicate

variable {P : Type u}

instance : One (Predicate P) := ⟨one⟩

instance : Max (Predicate P) := ⟨sup⟩

instance : Compl (Predicate P) := ⟨compl⟩

instance : Mul (Predicate P) := ⟨mul⟩

instance : Star (Predicate P) := ⟨star⟩

def eval {α : Type w} [NonAssocRelationAlgebra α] (v : P → α) : Predicate P → α
  | var p => v p
  | one => 1
  | sup A B => A.eval v ⊔ B.eval v
  | compl A => (A.eval v)ᶜ
  | mul A B => A.eval v * B.eval v
  | star A => Star.star (A.eval v)

end Predicate

namespace SequentCalculus

structure Formula (V : Type v) (P : Type u) where
  left : V
  pred : Predicate P
  right : V

abbrev Sequent (V : Type v) (P : Type u) := Set (Formula V P) × Set (Formula V P)

variable {V : Type v} {P : Type u}

inductive Proof (Ψ : Set (Sequent V P)) : Sequent V P → Type (max u v) where
  | hyp {S : Sequent V P} : S ∈ Ψ → Proof Ψ S
  -- Axiom
  | ax {Γ Δ : Set (Formula V P)} {φ : Formula V P} : φ ∈ Γ → φ ∈ Δ → Proof Ψ (Γ, Δ)
  -- Cut
  | cut {Γ Γ' Δ Δ' : Set (Formula V P)} {φ : Formula V P} :
      Proof Ψ (Γ, insert φ Δ) → Proof Ψ (insert φ Γ', Δ') → Proof Ψ (Γ ∪ Γ', Δ ∪ Δ')
  -- 1'|
  | oneLeft {Γ Δ : Set (Formula V P)} {x y z : V} {A : Predicate P} :
      Proof Ψ (insert ⟨x, A, y⟩ Γ, Δ) → Proof Ψ (insert ⟨x, A, z⟩ (insert ⟨z, 1, y⟩ Γ), Δ)
  -- |1'
  | oneRight {Γ Δ : Set (Formula V P)} {x : V} : ⟨x, 1, x⟩ ∈ Δ → Proof Ψ (Γ, Δ)
  -- +|
  | supLeft {Γ Γ' Δ Δ' : Set (Formula V P)} {x y : V} {A B : Predicate P} :
      Proof Ψ (insert ⟨x, A, y⟩ Γ, Δ) → Proof Ψ (insert ⟨x, B, y⟩ Γ', Δ') →
        Proof Ψ (insert ⟨x, A ⊔ B, y⟩ (Γ ∪ Γ'), Δ ∪ Δ')
  -- |+
  | supRight {Γ Δ : Set (Formula V P)} {x y : V} {A B : Predicate P} :
      Proof Ψ (Γ, insert ⟨x, A, y⟩ (insert ⟨x, B, y⟩ Δ)) → Proof Ψ (Γ, insert ⟨x, A ⊔ B, y⟩ Δ)
  -- ⁻|
  | complLeft {Γ Δ : Set (Formula V P)} {x y : V} {A : Predicate P} :
      Proof Ψ (Γ, insert ⟨x, A, y⟩ Δ) → Proof Ψ (insert ⟨x, Aᶜ, y⟩ Γ, Δ)
  -- |⁻
  | complRight {Γ Δ : Set (Formula V P)} {x y : V} {A : Predicate P} :
      Proof Ψ (insert ⟨x, A, y⟩ Γ, Δ) → Proof Ψ (Γ, insert ⟨x, Aᶜ, y⟩ Δ)
  -- ;| with the side condition "no y"
  | mulLeft {Γ Δ : Set (Formula V P)} {x y z : V} {A B : Predicate P} :
      y ≠ x → y ≠ z → (∀ φ ∈ Γ ∪ Δ, y ≠ φ.left ∧ y ≠ φ.right) →
        Proof Ψ (insert ⟨x, A, y⟩ (insert ⟨y, B, z⟩ Γ), Δ) → Proof Ψ (insert ⟨x, A * B, z⟩ Γ, Δ)
  -- |;
  | mulRight {Γ Γ' Δ Δ' : Set (Formula V P)} {x y z : V} {A B : Predicate P} :
      Proof Ψ (Γ, insert ⟨x, A, y⟩ Δ) → Proof Ψ (Γ', insert ⟨y, B, z⟩ Δ') →
        Proof Ψ (Γ ∪ Γ', insert ⟨x, A * B, z⟩ (Δ ∪ Δ'))
  -- ˘|
  | starLeft {Γ Δ : Set (Formula V P)} {x y : V} {A : Predicate P} :
      Proof Ψ (insert ⟨x, A, y⟩ Γ, Δ) → Proof Ψ (insert ⟨y, star A, x⟩ Γ, Δ)
  -- |˘
  | starRight {Γ Δ : Set (Formula V P)} {x y : V} {A : Predicate P} :
      Proof Ψ (Γ, insert ⟨x, A, y⟩ Δ) → Proof Ψ (Γ, insert ⟨y, star A, x⟩ Δ)

opaque SC (Ψ : Set (Sequent V P)) : Type := Empty

instance (Ψ : Set (Sequent V P)) : Logic.InferenceSystem (SC Ψ) (Sequent V P) where
  derivation := Proof Ψ

open Logic.InferenceSystem in
def Sound (α : Type w) [NonAssocRelationAlgebra α] (V : Type v) : Prop :=
  ∀ (A B : Predicate ℕ) (x y : V), x ≠ y →
    DerivableIn (SC (∅ : Set (Sequent V ℕ))) (({⟨x, A, y⟩}, {⟨x, B, y⟩}) : Sequent V ℕ) →
      ∀ v : ℕ → α, A.eval v ≤ B.eval v

end SequentCalculus

end Cslib.RelationAlgebra
