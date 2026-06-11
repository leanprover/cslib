/-
Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.TypeTags

/-! # Propositions and theories

## Main definitions

- `Proposition` : the type of propositions over a given type of atom. Primitives are `atom`,
  `bot` (falsum), and `imp` (implication). Conjunction, disjunction, negation, and verum are
  derived connectives following the Lukasiewicz convention.
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

/-- Propositions. Primitives are atoms, falsum, and implication. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Falsum / bottom -/
  | bot
  /-- Implication -/
  | imp (a b : Proposition Atom)
deriving DecidableEq, BEq

/-- Negation as a derived connective: ¬A := A → ⊥ -/
abbrev Proposition.neg : Proposition Atom → Proposition Atom := (Proposition.imp · .bot)

/-- Verum / top as a derived connective: ⊤ := ⊥ → ⊥ -/
abbrev Proposition.top : Proposition Atom := .imp .bot .bot

/-- Disjunction as a derived connective: A ∨ B := ¬A → B -/
abbrev Proposition.or (A B : Proposition Atom) : Proposition Atom :=
  .imp (.imp A .bot) B

/-- Conjunction as a derived connective: A ∧ B := ¬(A → ¬B) -/
abbrev Proposition.and (A B : Proposition Atom) : Proposition Atom :=
  .imp (.imp A (.imp B .bot)) .bot

/-- Biconditional as a derived connective: A ↔ B := (A → B) ∧ (B → A) -/
abbrev Proposition.iff (A B : Proposition Atom) : Proposition Atom :=
  (A.imp B).and (B.imp A)

instance : Bot (Proposition Atom) := ⟨.bot⟩
instance : Top (Proposition Atom) := ⟨.top⟩

@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or
@[inherit_doc] scoped infix:30 " → " => Proposition.imp
@[inherit_doc] scoped prefix:40 " ¬ " => Proposition.neg

/-- Register `Proposition` as an instance of `PropositionalConnectives`. -/
instance : PropositionalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp

/-- Substitute each atom in a proposition for a proposition, possibly changing the atomic
language. -/
def Proposition.subst {Atom Atom' : Type u} (f : Atom → Proposition Atom') :
    Proposition Atom → Proposition Atom'
  | atom x => f x
  | bot => .bot
  | imp A B => .imp (A.subst f) (B.subst f)

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
abbrev MPL : Theory (Atom) := ∅

/-- Intuitionistic propositional logic adds the principle of explosion (ex falso quodlibet). -/
abbrev IPL : Theory Atom :=
  Set.range (Proposition.imp ⊥ ·)

/-- Classical logic further adds double negation elimination. -/
abbrev CPL : Theory Atom :=
  Set.range (fun (A : Proposition Atom) ↦ ¬¬A → A)

/-- A theory is intuitionistic if it validates ex falso quodlibet. -/
@[scoped grind]
class IsIntuitionistic (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ → A) ∈ T

omit [DecidableEq Atom] in
@[scoped grind =]
theorem isIntuitionisticIff (T : Theory Atom) : IsIntuitionistic T ↔ IPL ⊆ T := by grind

/-- A theory is classical if it validates double-negation elimination. -/
@[scoped grind]
class IsClassical (T : Theory Atom) where
  dne (A : Proposition Atom) : (¬¬A → A) ∈ T

omit [DecidableEq Atom] in
@[scoped grind =]
theorem isClassicalIff (T : Theory Atom) : IsClassical T ↔ CPL ⊆ T := by grind

instance instIsIntuitionisticIPL : IsIntuitionistic (Atom := Atom) IPL where
  efq A := Set.mem_range.mpr ⟨A, rfl⟩

instance instIsClassicalCPL : IsClassical (Atom := Atom) CPL where
  dne A := Set.mem_range.mpr ⟨A, rfl⟩

omit [DecidableEq Atom] in
@[scoped grind →]
theorem instIsIntuitionisticExtention {T T' : Theory Atom} [IsIntuitionistic T]
    (h : T ⊆ T') : IsIntuitionistic T' := by grind

omit [DecidableEq Atom] in
@[scoped grind →]
theorem instIsClassicalExtention {T T' : Theory Atom} [IsClassical T] (h : T ⊆ T') :
    IsClassical T' := by grind

/-- Attach a bottom element to a theory `T`, and the principle of explosion for that bottom. -/
@[reducible]
def intuitionisticCompletion (T : Theory Atom) : Theory (WithBot Atom) :=
  (WithBot.some <$> T) ∪ IPL

instance instIsIntuitionisticIntuitionisticCompletion (T : Theory Atom) :
    IsIntuitionistic T.intuitionisticCompletion := by grind

end Cslib.Logic.PL.Theory
