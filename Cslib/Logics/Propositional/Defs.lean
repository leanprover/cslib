/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.Operators
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Order.TypeTags

/-! # Propositions and theories

## Main definitions

- `Proposition` : the type of propositions over a given type of atom.
- `IsIntuitionistic` : an inference system on `Proposition Atom` is intuitionistic if it
derives the principle of explosion.
- `IsClassical` : an inference is classical if it derives double negation elimination.
- `Proposition.subst` : replace `atom x` in a `A : Proposition Atom` with `f x`, for a function
  `f : Atom → Proposition Atom'`. This induces a monad structure on `Proposition`, with
  `pure := Proposition.atom`.

## Notation

We instantiate the notation classes `HasAnd`, `HasOr`, `HasImpl`, `HasNot`, `Bot` and `Top` for
`Proposition Atom` to give access to, respectively, the notations `∧, ∨, →`, `¬`, `⊥` and `⊤` for
propositional connectives.

## References

* [J. Avigad, *Mathematical Logic and Computation*][Avigad2022]
-/

@[expose] public section

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace Cslib.Logic.PL

/-- Propositions. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Falsum. -/
  | falsum
  /-- Conjunction -/
  | and (a b : Proposition Atom)
  /-- Disjunction -/
  | or (a b : Proposition Atom)
  /-- Implication -/
  | imp (a b : Proposition Atom)
deriving DecidableEq

instance instBotProposition : Bot (Proposition Atom) := ⟨.falsum⟩
/-- We view negation as a defined connective ~A := A → ⊥ -/
abbrev Proposition.neg : Proposition Atom → Proposition Atom := (Proposition.imp · ⊥)

/-- A fixed choice of a derivable proposition (of course any two are equivalent). -/
abbrev Proposition.verum : Proposition Atom := imp ⊥ ⊥

instance instTopProposition : Top (Proposition Atom) := ⟨.verum⟩

instance : HasAnd (Proposition Atom) := ⟨.and⟩
instance : HasOr (Proposition Atom) := ⟨.or⟩
instance : HasImp (Proposition Atom) := ⟨.imp⟩
instance : HasNot (Proposition Atom) := ⟨.neg⟩

omit [DecidableEq Atom] in
@[grind =]
lemma not_eq (A : Proposition Atom) : (A → ⊥) = ¬ A := rfl

/-- Substitute each atom in a proposition for a proposition, possibly changing the atomic
language. -/
def Proposition.subst {Atom Atom' : Type*} (f : Atom → Proposition Atom') :
    Proposition Atom → Proposition Atom'
  | atom x => f x
  | falsum => falsum
  | and A B => (A.subst f) ∧ (B.subst f)
  | or A B => (A.subst f) ∨ (B.subst f)
  | imp A B => (A.subst f) → (B.subst f)

-- This is probably a lawful monad, but that doesn't seem to be important.
instance : Monad Proposition where
  pure := .atom
  bind A f := A.subst f

/-- The empty collection of axioms corresponds to intuitionistic propositional logic. -/
abbrev IPL (Atom : Type u) : Set (Proposition Atom) := ∅

/-- Classical logic adds double negation elimination. -/
abbrev CPL (Atom : Type u) : Set (Proposition Atom) := {¬¬A → A | A : Proposition Atom}

omit [DecidableEq Atom] in
lemma dne_mem_cpl (A : Proposition Atom) : (¬¬A → A) ∈ CPL Atom := ⟨A, rfl⟩

open InferenceSystem

/-- An inference system is intuitionistic if it derives ex falso quodlibet. TODO: this should be
generalised outside the `PL` scope. -/
@[scoped grind]
class IsIntuitionistic (Atom : Type u) (S : Type*) [InferenceSystem S (Proposition Atom)] where
  /-- The principle of explosion (ex falso quolibet). -/
  derBotImp (A : Proposition Atom) : S⇓(⊥ → A)

/-- An inference system is classical if it validates double-negation elimination. TODO: this should
be generalised outside the `PL` scope. -/
@[scoped grind]
class IsClassical (Atom : Type u) (S : Type*) [InferenceSystem S (Proposition Atom)] where
  /-- Double-negation elimination. -/
  dne (A : Proposition Atom) : S⇓(¬¬A → A)

end Cslib.Logic.PL
