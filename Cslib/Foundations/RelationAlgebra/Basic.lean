/- 
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Order.Atoms
public import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Relation algebras

-/

@[expose] public section

namespace Cslib

class RelationAlgebra (α : Type*) extends BooleanAlgebra α, Monoid α, StarMul α where
  sup_mul (a b c : α) : (a ⊔ b) * c = a * c ⊔ b * c
  star_sup (a b : α) : star (a ⊔ b) = star a ⊔ star b
  tarski (a b : α) : star a * (a * b)ᶜ ≤ bᶜ

namespace RelationAlgebra

variable (α : Type*) [RelationAlgebra α]

def Integral : Prop := IsAtom (1 : α)

def IdentityAtoms : Set α := {a : α | IsAtom a ∧ a ≤ 1}

def SymmetricAtoms : Set α := {a : α | IsAtom a ∧ a ≤ 1ᶜ ∧ star a = a}

def NonsymmetricAtoms : Set α := {a : α | IsAtom a ∧ a ≤ 1ᶜ ∧ star a ≠ a}

end RelationAlgebra

end Cslib
