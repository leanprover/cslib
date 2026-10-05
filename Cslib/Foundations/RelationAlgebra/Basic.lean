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
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Relation algebras

A relation algebra in the sense of Tarski combines a Boolean algebra with composition,
identity, and converse. We use `*`, `1`, and `star` for these three operations; in particular,
the identity `1` is distinct from the Boolean top `⊤` in general.

The additional axioms below are the distributivity laws and Tarski's law, using the order
form of the latter. See Definition 1 and (R10′) in Andréka, Givant, Jipsen, and Németi,
[On Tarski's axiomatic foundations of the calculus of relations](https://arxiv.org/abs/1604.04655).

The signature convention follows Jipsen's
[table of small relation algebras](https://www1.chapman.edu/~jipsen/gap/ramaddux.html):
`⟨i, j, k⟩` counts identity atoms, symmetric diversity atoms, and pairs of nonsymmetric atoms.
-/

@[expose] public section

namespace Cslib

/-- A relation algebra in the sense of Tarski. Multiplication is relational composition,
`1` is identity, and `star` is converse. -/
class RelationAlgebra (A : Type*) extends BooleanAlgebra A, Monoid A, StarMul A where
  /-- Composition distributes over joins in its left argument. -/
  sup_mul (a b c : A) : (a ⊔ b) * c = a * c ⊔ b * c
  /-- Converse preserves joins. -/
  star_sup (a b : A) : star (a ⊔ b) = star a ⊔ star b
  /-- Tarski's law, expressed as an inequality. -/
  tarski (a b : A) : star a * (a * b)ᶜ ≤ bᶜ

namespace RelationAlgebra

/-- A relation algebra is integral if its multiplicative identity is an atom. -/
def Integral (A : Type*) [RelationAlgebra A] : Prop :=
  IsAtom (1 : A)

/-- A finite relation algebra has signature `⟨i, j, k⟩` if it has `i` identity atoms,
`j` symmetric diversity atoms, and `2 * k` nonsymmetric diversity atoms.

Finiteness is required explicitly: merely counting atoms does not rule out an atomless part.
The parameter `k` counts converse pairs, rather than individual nonsymmetric atoms. -/
def HasSignature (A : Type*) [RelationAlgebra A] (i j k : ℕ) : Prop :=
  Finite A ∧
    Nat.card {a : A // IsAtom a ∧ a ≤ 1} = i ∧
    Nat.card {a : A // IsAtom a ∧ a ≤ (1 : A)ᶜ ∧ star a = a} = j ∧
    Nat.card {a : A // IsAtom a ∧ a ≤ (1 : A)ᶜ ∧ star a ≠ a} = 2 * k

end RelationAlgebra

end Cslib
