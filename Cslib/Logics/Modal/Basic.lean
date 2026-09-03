/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Defs.Unbundled
public import Cslib.Foundations.Relation.Euclidean
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.Operators
public import Cslib.Foundations.Relation.Defs
public import Cslib.Foundations.Syntax.HasSubstitution

/-! # Modal Logic

Modal logic is a logic for reasoning about (possibly polyadic) relational structures, studying
**qualified** statements through the use of **modalities** (like necessity, possibility, knowledge,
belief, permission, etc.).

This module formalises general modal logic, parameterised over a signature of modal operators. A
signature is formalised as a polynomial functor (`PFunctor`), generalising the concept of modal
similarity types from the literature [Blackburn2001].

## Implementation notes

- Compared to [Blackburn2001], a triangle takes a map of arguments (from the argument type given
  by the polynomial functor to propositions), instead of a sequence of arguments.
- The use of `τ` to range over signatures of modal operators comes from the literature
  [Blackburn2001].

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
* The definitions of theory equivalence and the denotational semantics of worlds are inspired by
  the development of `Cslib.Logic.HML`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

/-- A modal proposition. -/
inductive Proposition (τ : PFunctor) Atom where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsehood. -/
  | false
  /-- Negation. -/
  | not (φ : Proposition τ Atom)
  /-- Disjunction. -/
  | or (φ₁ φ₂ : Proposition τ Atom)
  /-- Generalised possibility, or triangle. -/
  | triangle (op : τ.A) (φs : τ.B op → Proposition τ Atom)

/-- A map of propositions for the operator `op` in the polynomial functor `τ`. -/
abbrev PropositionMap τ op Atom := τ.B op → Proposition τ Atom

/-- Utility to coerce atoms into atomic propositions. -/
instance : Coe Atom (Proposition τ Atom) := ⟨.atom⟩

instance {τ : PFunctor} {Atom : Type*} : Bot (Proposition τ Atom) := ⟨.false⟩
instance {τ : PFunctor} {Atom : Type*} : HasNot (Proposition τ Atom) := ⟨.not⟩
instance {τ : PFunctor} {Atom : Type*} : HasOr (Proposition τ Atom) := ⟨Proposition.or⟩
instance {τ : PFunctor} {Atom : Type*} : HasTriangle (Proposition τ Atom) τ := ⟨.triangle⟩

@[scoped grind =]
lemma Proposition.false_def : (.false : Proposition (τ := τ) (Atom := Atom)) = ⊥ := rfl

@[scoped grind =]
lemma Proposition.not_def (φ : Proposition τ Atom) : φ.not = ¬φ := rfl

@[scoped grind =]
lemma Proposition.or_def (φ₁ φ₂ : Proposition τ Atom) : φ₁.or φ₂ = (φ₁ ∨ φ₂) := rfl

@[scoped grind =]
lemma Proposition.triangle_def {τ : PFunctor} (op : τ.A)
    (φs : τ.B op → Proposition τ Atom) : Proposition.triangle op φs = (Δ[op]φs) := rfl

/-- Conjunction. -/
def Proposition.and (φ₁ φ₂ : Proposition τ Atom) := ¬(¬φ₁ ∨ ¬φ₂)

instance {τ : PFunctor} {Atom : Type*} : HasAnd (Proposition τ Atom) := ⟨.and⟩

@[scoped grind =]
lemma Proposition.and_def (φ₁ φ₂ : Proposition τ Atom) : φ₁.and φ₂ = (φ₁ ∧ φ₂) := rfl

/-- Implication. -/
def Proposition.imp (φ₁ φ₂ : Proposition τ Atom) := ¬φ₁ ∨ φ₂

instance {τ : PFunctor} {Atom : Type*} : HasImp (Proposition τ Atom) := ⟨.imp⟩

@[scoped grind =]
lemma Proposition.imp_def (φ₁ φ₂ : Proposition τ Atom) : φ₁.imp φ₂ = (φ₁ → φ₂) := rfl

/-- Bi-implication. -/
def Proposition.iff (φ₁ φ₂ : Proposition τ Atom) := (φ₁ → φ₂) ∧ (φ₂ → φ₁)

instance {τ : PFunctor} {Atom : Type*} : HasIff (Proposition τ Atom) := ⟨.iff⟩

@[scoped grind =]
lemma Proposition.iff_def (φ₁ φ₂ : Proposition τ Atom) : φ₁.iff φ₂ = (φ₁ ↔ φ₂) := rfl

/-- Point-wise negation of a proposition map. -/
def PropositionMap.not (φs : PropositionMap τ op Atom) := fun i => ¬φs i

instance {τ : PFunctor} {op : τ.A} {Atom : Type*} : HasNot (PropositionMap τ op Atom) := ⟨.not⟩

@[simp, scoped grind =, modal =]
theorem PropositionMap.not_apply {φs : PropositionMap τ op Atom} (i : τ.B op) :
    (¬φs) i = ¬(φs i) := by simp [HasNot.not, PropositionMap.not]

/-- Point-wise conjunction of proposition maps. -/
def PropositionMap.and (φs₁ φs₂ : PropositionMap τ op Atom) := fun i => φs₁ i ∧ φs₂ i

instance {τ : PFunctor} {op : τ.A} {Atom : Type*} : HasAnd (PropositionMap τ op Atom) := ⟨.and⟩

@[scoped grind =, modal =]
theorem PropositionMap.and_apply (φs₁ φs₂ : PropositionMap τ op Atom) (i : τ.B op) :
    (φs₁ ∧ φs₂) i = (φs₁ i ∧ φs₂ i) := rfl

/-- Point-wise disjunction of proposition maps. -/
def PropositionMap.or (φs₁ φs₂ : PropositionMap τ op Atom) := fun i => φs₁ i ∨ φs₂ i

instance {τ : PFunctor} {op : τ.A} {Atom : Type*} : HasOr (PropositionMap τ op Atom) := ⟨.or⟩

/-- Point-wise implication of proposition maps. -/
def PropositionMap.imp (φs₁ φs₂ : PropositionMap τ op Atom) := fun i => φs₁ i → φs₂ i

instance {τ : PFunctor} {op : τ.A} {Atom : Type*} : HasImp (PropositionMap τ op Atom) := ⟨.imp⟩

/-- Point-wise bi-implication of proposition maps. -/
def PropositionMap.iff (φs₁ φs₂ : PropositionMap τ op Atom) := fun i => φs₁ i ↔ φs₂ i

instance {τ : PFunctor} {op : τ.A} {Atom : Type*} : HasIff (PropositionMap τ op Atom) := ⟨.iff⟩

@[simp, scoped grind =, modal =]
theorem PropositionMap.or_apply (φs ψs : PropositionMap τ op Atom) (i : τ.B op) :
    (φs ∨ ψs) i = (φs i ∨ ψs i) := rfl

@[simp, scoped grind =, modal =]
theorem PropositionMap.imp_apply (φs ψs : PropositionMap τ op Atom) (i : τ.B op) :
    (φs → ψs) i = (φs i → ψs i) := rfl

@[simp, scoped grind =, modal =]
theorem PropositionMap.iff_apply (φs ψs : PropositionMap τ op Atom) (i : τ.B op) :
    (φs ↔ ψs) i = (φs i ↔ ψs i) := rfl

/-- The constant proposition map, always returning the same proposition. -/
abbrev PropositionMap.const (φ : Proposition τ Atom) : PropositionMap τ op Atom :=
  fun _ => φ

/-- Generalised necessity, or nabla (∇), dual of triangle. -/
def Proposition.nabla {τ : PFunctor} (op : τ.A) (φs : τ.B op → Proposition τ Atom) :=
  ¬Δ[op]¬φs

instance {τ : PFunctor} {Atom : Type*} : HasNabla (Proposition τ Atom) τ := ⟨.nabla⟩

@[scoped grind =]
lemma Proposition.nabla_def {τ : PFunctor} (op : τ.A)
    (φs : τ.B op → Proposition τ Atom) : Proposition.nabla op φs = (∇[op]φs) := rfl

end Cslib.Logic.Modal
