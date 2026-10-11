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

A relation algebra in the sense of Tarski (not to be confused with a relational algebra) are an
extension of Boolean algebras that are designed to form an algebraic analysis of relations,
`α → α → Prop` in Lean. They have applications in computer science such as the theory of constraint
satisfaction as well as mathematical connections such as combinatorics.

## References

* [R. Maddux, *Relation Algebras*][Maddux2006]

-/

@[expose] public section

namespace Cslib

/-- The class of relation algebras. Note the notational differences from the literature. In addition
to inheriting Mathlib's notations for Boolean algebras, `star` is used for converse, and the monoid
reduct for composition uses multiplicative notation. -/
class RelationAlgebra (α : Type*) extends BooleanAlgebra α, Monoid α, StarMul α where
  sup_mul (a b c : α) : (a ⊔ b) * c = a * c ⊔ b * c
  star_sup (a b : α) : star (a ⊔ b) = star a ⊔ star b
  tarski (a b : α) : star a * (a * b)ᶜ ≤ bᶜ

namespace RelationAlgebra

variable (α : Type*) [RelationAlgebra α]

/-- A relation algebra is *integral* when its identity is an atom. -/
def Integral : Prop := IsAtom (1 : α)

/-- The set of identity atoms. -/
def IdentityAtoms : Set α := {a : α | IsAtom a ∧ a ≤ 1}

/-- The set of symmetric atoms. -/
def SymmetricAtoms : Set α := {a : α | IsAtom a ∧ a ≤ 1ᶜ ∧ star a = a}

/-- The set of nonsymmetric atoms. -/
def NonsymmetricAtoms : Set α := {a : α | IsAtom a ∧ a ≤ 1ᶜ ∧ star a ≠ a}

end RelationAlgebra

end Cslib
