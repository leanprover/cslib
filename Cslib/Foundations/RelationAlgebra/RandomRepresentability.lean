/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IsoClass
public import Cslib.Foundations.RelationAlgebra.Language
public import Cslib.Foundations.RelationAlgebra.Representation
public import Mathlib.ModelTheory.Semantics
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Equations and random representability

Maddux's finite-equation theorem fixes a finite set of equations valid in every representable
relation algebra before taking the limit in the number of Boolean atoms. The Random
Representability Conjecture asks whether representable algebras themselves have density one.
Both statements give each isomorphism class equal weight.

## References

* Roger D. Maddux, *Finite integral relation algebras* (1985), Theorem 15, gives the
  finite-equation result for integral algebras. For the passage to all relation algebras see
  [James Koussas, *Finite Relation Algebras*](https://arxiv.org/abs/2202.01959),
  Proposition 13(2) and Corollary 23 of the preprint.
* Roger D. Maddux, *On the Future of RA* (2022), conjecture (2).
-/

@[expose] public section

namespace Cslib.RelationAlgebra

open FirstOrder.Language FirstOrder.RelationAlgebra

/-- A pair of relation-algebra terms with variables in `α`, asserted to be equal. -/
abbrev Equation (α : Type*) := relationAlgebra.Term α × relationAlgebra.Term α

variable {α : Type*}

/-- An algebra satisfies an equation if the terms agree at every assignment. -/
def Equation.Holds (e : Equation α) (A : Type*) [RelationAlgebra A] : Prop :=
  letI := compatibleRelationAlgebraOfRelationAlgebra A
  ∀ v : α → A, e.1.realize v = e.2.realize v

/-- An equation valid in every representable relation algebra, including infinite ones. -/
def Equation.ValidInRRA (e : Equation α) : Prop :=
  ∀ (A : Type*) [RelationAlgebra A], Representable A → e.Holds A

/-- Equations valid in the codomain of an embedding also hold in its domain. -/
theorem Equation.holds_of_injective {A B : Type*} [RelationAlgebra A] [RelationAlgebra B]
    (e : Equation α) (f : RelationAlgebraHom A B) (hf : Function.Injective f) (h : e.Holds B) :
    e.Holds A := by
  let _ := compatibleRelationAlgebraOfRelationAlgebra A
  let _ := compatibleRelationAlgebraOfRelationAlgebra B
  intro v
  apply hf
  simpa only [HomClass.realize_term] using h (f ∘ v)

namespace IsoClass

/-- Satisfaction of an equation by an isomorphism class with `n` atoms. -/
def Satisfies {n : ℕ} (q : ofAtoms n) (e : Equation α) : Prop :=
  Quotient.liftOn q (fun S => e.Holds (ComplexAlgebra S.val)) fun _ _ ⟨f⟩ =>
    propext ⟨e.holds_of_injective f.symm.toHom f.symm.toHom_injective,
      e.holds_of_injective f.toHom f.toHom_injective⟩

/-- Representability of an isomorphism class with `n` atoms, allowing infinite bases. -/
def IsRepresentable {n : ℕ} (q : ofAtoms n) : Prop :=
  Quotient.liftOn q (fun S => Representable (ComplexAlgebra S.val)) fun _ _ ⟨f⟩ =>
    propext f.representable_iff

open Filter
open scoped Topology

/-- For each fixed finite set of equations valid in RRA, the proportion of finite
relation-algebra isomorphism classes satisfying them all tends to one. -/
theorem_wanted tendsto_satisfying_div_all (E : Finset (Equation α)) (hE : ∀ e ∈ E, e.ValidInRRA) :
    Tendsto (fun n => (Nat.card {q : ofAtoms n // ∀ e ∈ E, Satisfies q e} : ℝ) /
      Nat.card (ofAtoms n)) atTop (𝓝 1)

/-- Maddux's Random Representability Conjecture. The proportion of representable isomorphism
classes among all finite relation algebras with `n` Boolean atoms tends to one. -/
theorem_wanted random_representability_conjecture :
    Tendsto (fun n => (Nat.card {q : ofAtoms n // IsRepresentable q} : ℝ) /
      Nat.card (ofAtoms n)) atTop (𝓝 1)

end IsoClass

end Cslib.RelationAlgebra
