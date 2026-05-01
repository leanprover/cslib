/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Order.TypeTags

/-! # Propositions and theories

## Main definitions

- `Proposition` : the type of propositions over a given type of atom. This type has a `Bot`
instance whenever `Atom` does, and a `Top` whenever `Atom` is inhabited.
- `Theory` : set of `Proposition`.
- `IsIntuitionistic` : a theory is intuitionistic if it contains the principle of explosion.
- `IsClassical` : an intuitionistic theory is classical if it further contains double negation
elimination.
- `Proposition.subst` : replace `atom x` in a `A : Proposition Atom` with `f x`, for a function
  `f : Atom → Proposition Atom'`. This induces a monad structure on `Proposition`, with
  `pure := Proposition.atom`. `Theory` is a functor, by mapping each proposition `A ∈ T` to
  `f <$> A`.
- `Theory.intuitionisticCompletion` : the freely generated intuitionistic theory extending a given
theory.

## Notation

We introduce notation for the logical connectives: `⊥ ⊤ ∧ ∨ → ¬` for, respectively, falsum, verum,
conjunction, disjunction, implication and negation.
-/

@[expose] public section

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace Cslib.Logic.PL

/-- Propositions. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Conjunction -/
  | and (a b : Proposition Atom)
  /-- Disjunction -/
  | or (a b : Proposition Atom)
  /-- Implication -/
  | impl (a b : Proposition Atom)
deriving DecidableEq, BEq

instance instBotProposition [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩
instance instInhabitedOfBot [Bot Atom] : Inhabited Atom := ⟨⊥⟩

/-- We view negation as a defined connective ~A := A → ⊥ -/
abbrev Proposition.neg [Bot Atom] : Proposition Atom → Proposition Atom := (Proposition.impl · ⊥)

/-- A fixed choice of a derivable proposition (of course any two are equivalent). -/
abbrev Proposition.top [Inhabited Atom] : Proposition Atom := impl (.atom default) (.atom default)

instance instTopProposition [Inhabited Atom] : Top (Proposition Atom) := ⟨.top⟩

example [Bot Atom] : (⊤ : Proposition Atom) = Proposition.impl ⊥ ⊥ := rfl

@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or
@[inherit_doc] scoped infix:30 " → " => Proposition.impl
@[inherit_doc] scoped prefix:40 " ¬ " => Proposition.neg

/-- Substitute each atom in a proposition for a proposition, possibly changing the atomic
language. -/
def Proposition.subst {Atom Atom' : Type u} (f : Atom → Proposition Atom') :
    Proposition Atom → Proposition Atom'
  | atom x => f x
  | and A B => (A.subst f) ∧ (B.subst f)
  | or A B => (A.subst f) ∨ (B.subst f)
  | impl A B => (A.subst f) → (B.subst f)

-- This is probably a lawful monad, but that doesn't seem to be important.
instance : Monad Proposition where
  pure := .atom
  bind A f := A.subst f

/-- Theories are arbitrary sets of propositions. -/
abbrev Theory (Atom) := Set (Proposition Atom)

namespace Theory

/-- Extend a substitution from `Proposition` to `Theory`. -/
protected def subst {Atom Atom' : Type u} (T : Theory Atom) (f : Atom → Proposition Atom') :
    Theory Atom' := T.image (· >>= f)

instance : Functor Theory where
  map f := Set.image (f <$> ·)

/-- The empty theory corresponds to minimal propositional logic. -/
abbrev MPL (Atom : Type u) : Theory (Atom) := ∅

/-- Intuitionistic propositional logic adds the principle of explosion (ex falso quodlibet). -/
abbrev IPL (Atom : Type u) [Bot Atom] : Theory Atom := {⊥ → A | A : Proposition Atom}

omit [DecidableEq Atom] in
lemma efq_mem_ipl [Bot Atom] (A : Proposition Atom) : (⊥ → A) ∈ IPL Atom := ⟨A, rfl⟩

/-- Attach a bottom element to a theory `T`, and the principle of explosion for that bottom. -/
@[reducible]
def intuitionisticCompletion (T : Theory Atom) : Theory (WithBot Atom) :=
  (WithBot.some <$> T) ∪ IPL (WithBot Atom)

/-- Classical logic further adds double negation elimination. -/
abbrev CPL (Atom : Type u) [Bot Atom] : Theory Atom := {¬¬A → A | A : Proposition Atom}

omit [DecidableEq Atom] in
lemma dne_mem_cpl [Bot Atom] (A : Proposition Atom) : (¬¬A → A) ∈ CPL Atom := ⟨A, rfl⟩

open InferenceSystem

/-- An inference system is intuitionistic if it derives ex falso quodlibet. -/
@[scoped grind]
class IsIntuitionistic (Atom : Type u) [Bot Atom] (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  efq (A : Proposition Atom) : S⇓(⊥ → A)

/-- An inference system is classical if it validates double-negation elimination. -/
@[scoped grind]
class IsClassical (Atom : Type u) [Bot Atom] (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  dne (A : Proposition Atom) : S⇓(¬¬A → A)

end Cslib.Logic.PL.Theory
