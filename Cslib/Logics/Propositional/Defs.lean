/-
Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.TypeTags

/-! # Propositions and theories

## Main definitions

- `Proposition` : the type of propositions over a given type of atom. Primitives are `atom`,
  `bot` (falsum), `imp` (implication), `and` (conjunction), and `or` (disjunction). Negation
  (`neg`), verum (`top`), and biconditional (`iff`) are derived connectives (`abbrev`s). This
  follows the natural deduction tradition ([Avigad2022]) in which `neg A` abbreviates `A → ⊥`
  rather than being taken as primitive.
- `Theory` : set of `Proposition`.
- `IsClassical` : an inference system is classical if it further derives double negation
  elimination.
- `Proposition.subst` : replace `atom x` in a `A : Proposition Atom` with `f x`, for a function
  `f : Atom → Proposition Atom'`. This induces a monad structure on `Proposition`, with
  `pure := Proposition.atom`. `Theory` is a functor, by mapping each proposition `A ∈ T` to
  `f <$> A`.

## Notation

We introduce notation for the logical connectives: `⊥ ⊤ ∧ ∨ → ¬` for, respectively, falsum, verum,
conjunction, disjunction, implication and negation.

## References

* [J. Avigad, *Mathematical Logic and Computation*][Avigad2022]
-/

@[expose] public section

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace Cslib.Logic.PL

/-- Propositions. Primitives are atoms, falsum, implication, conjunction, and disjunction. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Falsum / bottom -/
  | bot
  /-- Implication -/
  | imp (a b : Proposition Atom)
  /-- Conjunction -/
  | and (a b : Proposition Atom)
  /-- Disjunction -/
  | or (a b : Proposition Atom)
deriving DecidableEq, BEq

/-- Negation as a derived connective: ¬A := A → ⊥ -/
abbrev Proposition.neg : Proposition Atom → Proposition Atom := (Proposition.imp · .bot)

/-- Verum / top as a derived connective: ⊤ := ⊥ → ⊥ -/
abbrev Proposition.top : Proposition Atom := .imp .bot .bot

/-- Biconditional as a derived connective: A ↔ B := (A → B) ∧ (B → A) -/
abbrev Proposition.iff (A B : Proposition Atom) : Proposition Atom :=
  (A.imp B).and (B.imp A)

instance : Bot (Proposition Atom) := ⟨.bot⟩
instance : Top (Proposition Atom) := ⟨.top⟩

@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or
@[inherit_doc] scoped infix:30 " → " => Proposition.imp
@[inherit_doc] scoped infix:20 " ↔ " => Proposition.iff
@[inherit_doc] scoped prefix:40 " ¬ " => Proposition.neg

/-- Substitute each atom in a proposition for a proposition, possibly changing the atomic
language. -/
def Proposition.subst {Atom Atom' : Type u} (f : Atom → Proposition Atom') :
    Proposition Atom → Proposition Atom'
  | atom x => f x
  | bot => .bot
  | imp A B => .imp (A.subst f) (B.subst f)
  | and A B => .and (A.subst f) (B.subst f)
  | or A B => .or (A.subst f) (B.subst f)

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

/-- Intuitionistic propositional logic: the base theory. Ex falso quodlibet is a primitive
inference rule (see `Derivation.efq`), so no explosion axioms are needed. -/
abbrev IPL : Theory Atom := ∅

/-- Classical logic further adds double negation elimination. -/
abbrev CPL : Theory Atom :=
  Set.range (fun (A : Proposition Atom) ↦ ¬¬A → A)

omit [DecidableEq Atom] in
lemma dne_mem_cpl (A : Proposition Atom) : (¬¬A → A) ∈ CPL (Atom := Atom) := ⟨A, rfl⟩

open InferenceSystem

/-- An inference system is classical if it validates double-negation elimination. TODO: this should
be generalised outside the `PL` scope, once we have typeclasses to express that a type possesses an
implication connective. -/
@[scoped grind]
class IsClassical (Atom : Type u) (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  /-- Double-negation elimination. -/
  dne (A : Proposition Atom) : S⇓(¬¬A → A)

end Cslib.Logic.PL.Theory
