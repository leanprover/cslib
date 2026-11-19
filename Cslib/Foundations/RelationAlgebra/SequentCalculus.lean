/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.ModelTheory
public import Cslib.Foundations.Logic.InferenceSystem.Defs

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

open FirstOrder FirstOrder.RelationAlgebra

namespace SequentCalculus

structure Formula (V : Type v) (P : Type u) where
  left : V
  pred : Language.relationAlgebra.Term P
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
  | oneLeft {Γ Δ : Set (Formula V P)} {x y z : V} {A : Language.relationAlgebra.Term P} :
      Proof Ψ (insert ⟨x, A, y⟩ Γ, Δ) → Proof Ψ (insert ⟨x, A, z⟩ (insert ⟨z, 1, y⟩ Γ), Δ)
  -- |1'
  | oneRight {Γ Δ : Set (Formula V P)} {x : V} : ⟨x, 1, x⟩ ∈ Δ → Proof Ψ (Γ, Δ)
  -- +|
  | supLeft {Γ Γ' Δ Δ' : Set (Formula V P)} {x y : V} {A B : Language.relationAlgebra.Term P} :
      Proof Ψ (insert ⟨x, A, y⟩ Γ, Δ) → Proof Ψ (insert ⟨x, B, y⟩ Γ', Δ') →
        Proof Ψ (insert ⟨x, A ⊔ B, y⟩ (Γ ∪ Γ'), Δ ∪ Δ')
  -- |+
  | supRight {Γ Δ : Set (Formula V P)} {x y : V} {A B : Language.relationAlgebra.Term P} :
      Proof Ψ (Γ, insert ⟨x, A, y⟩ (insert ⟨x, B, y⟩ Δ)) → Proof Ψ (Γ, insert ⟨x, A ⊔ B, y⟩ Δ)
  -- ⁻|
  | complLeft {Γ Δ : Set (Formula V P)} {x y : V} {A : Language.relationAlgebra.Term P} :
      Proof Ψ (Γ, insert ⟨x, A, y⟩ Δ) → Proof Ψ (insert ⟨x, Aᶜ, y⟩ Γ, Δ)
  -- |⁻
  | complRight {Γ Δ : Set (Formula V P)} {x y : V} {A : Language.relationAlgebra.Term P} :
      Proof Ψ (insert ⟨x, A, y⟩ Γ, Δ) → Proof Ψ (Γ, insert ⟨x, Aᶜ, y⟩ Δ)
  -- ;| with the side condition "no y"
  | mulLeft {Γ Δ : Set (Formula V P)} {x y z : V} {A B : Language.relationAlgebra.Term P} :
      y ≠ x → y ≠ z → (∀ φ ∈ Γ ∪ Δ, y ≠ φ.left ∧ y ≠ φ.right) →
        Proof Ψ (insert ⟨x, A, y⟩ (insert ⟨y, B, z⟩ Γ), Δ) → Proof Ψ (insert ⟨x, A * B, z⟩ Γ, Δ)
  -- |;
  | mulRight {Γ Γ' Δ Δ' : Set (Formula V P)} {x y z : V} {A B : Language.relationAlgebra.Term P} :
      Proof Ψ (Γ, insert ⟨x, A, y⟩ Δ) → Proof Ψ (Γ', insert ⟨y, B, z⟩ Δ') →
        Proof Ψ (Γ ∪ Γ', insert ⟨x, A * B, z⟩ (Δ ∪ Δ'))
  -- ˘|
  | starLeft {Γ Δ : Set (Formula V P)} {x y : V} {A : Language.relationAlgebra.Term P} :
      Proof Ψ (insert ⟨x, A, y⟩ Γ, Δ) → Proof Ψ (insert ⟨y, star A, x⟩ Γ, Δ)
  -- |˘
  | starRight {Γ Δ : Set (Formula V P)} {x y : V} {A : Language.relationAlgebra.Term P} :
      Proof Ψ (Γ, insert ⟨x, A, y⟩ Δ) → Proof Ψ (Γ, insert ⟨y, star A, x⟩ Δ)

opaque SC (Ψ : Set (Sequent V P)) : Type := Empty

instance (Ψ : Set (Sequent V P)) : Logic.InferenceSystem (SC Ψ) (Sequent V P) where
  derivation := Proof Ψ

open Logic.InferenceSystem in
def Sound (α : Type w) [NonAssocRelationAlgebra α] [CompatibleRelationAlgebra α] (V : Type v) :
    Prop :=
  ∀ (A B : Language.relationAlgebra.Term ℕ) (x y : V), x ≠ y →
    DerivableIn (SC (∅ : Set (Sequent V ℕ))) (({⟨x, A, y⟩}, {⟨x, B, y⟩}) : Sequent V ℕ) →
      ∀ v : ℕ → α, A.realize v ≤ B.realize v

end SequentCalculus

end Cslib.RelationAlgebra
