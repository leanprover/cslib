/-
Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Order.TypeTags

/-! # Propositions and theories

## Main definitions

- `Proposition` : the type of propositions over a given type of atom. Primitives are `atom`,
  `bot` (falsum), `imp` (implication), `and` (conjunction), and `or` (disjunction), following
  the standard five-primitive signature of Gentzen/Prawitz/Troelstra-van Dalen. Negation (`neg`),
  verum (`top`), and biconditional (`iff`) are derived connectives (`abbrev`s) rather than
  constructors.
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

## Design: Five Primitives

Upstream used four constructors `{atom, and, or, impl}` with a `Bot` typeclass constraint
to simulate falsum. This PR changes to five primitives `{atom, bot, imp, and, or}` with derived
negation and verum, for the following reasons:

1. **Minimal logic requires primitive `bot`**: Johansson's minimal logic (1937, [Johansson1937])
   is the standard basis for proof-relevant propositional logic. Minimal logic requires a
   distinguishable bottom formula; without it, one obtains only the *positive fragment* (no
   negation at all). The `[Bot Atom]` constraint approach simulates bottom via an atomic formula,
   which conflates the logical bottom with atomic data.

2. **Uniform negation**: With primitive `bot`, negation `¬A := A → ⊥` is uniformly available
   without typeclass constraints. The old `[Bot Atom]` approach required `Inhabited Atom` for
   `top` and `Bot Atom` for `neg`, producing a constraint proliferation.

3. **Standard notation**: The constructor name `impl` is non-standard; Gentzen (1935,
   [Gentzen1935]) and Prawitz (1965, [Prawitz1965]) both write the connective as `⊃` or `→`.
   We rename to `imp` for clarity and alignment with the broader logic literature.

4. **Functional completeness**: Adding `bot` as a primitive makes `{bot, imp, and, or}` the
   standard five-primitive basis studied in [TroelstraVanDalen1988] Chapter 2 and
   [Church1956] §24. This resolves the objection (CSLib PR #635) that the four-primitive
   `{and, or, impl}` set is not functionally complete for classical logic (it lacks the
   ability to express unsatisfiable formulas).

## Notation

We introduce notation for the logical connectives: `⊥ ⊤ ∧ ∨ → ↔ ¬` for, respectively, falsum,
verum, conjunction, disjunction, implication, biconditional, and negation.

## Architecture

Two proof systems are defined for this propositional language:

- **Layer 1 — Natural Deduction** (`NaturalDeduction/Basic.lean`): a `Theory.Derivation` inductive
  with 10 primitive constructors. Logic strength is controlled by the theory parameter: `MPL`
  (Johansson's minimal logic, [Johansson1937]), `IPL` (intuitionistic), and `CPL` (classical).

- **Layer 2 — Hilbert System** (`ProofSystem/`): an axiom predicate hierarchy with sequent
  derivability and a Hilbert-style proof-theoretic treatment (future PR).

## References

* [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
* [G. Gentzen, *Untersuchungen über das logische Schließen*][Gentzen1935]
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
* [A. S. Troelstra, D. van Dalen,
  *Constructivism in Mathematics: An Introduction*][TroelstraVanDalen1988]
* [A. Church, *Introduction to Mathematical Logic*][Church1956]
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Chapter 1
-/

@[expose] public section

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace Cslib.Logic.PL

/-- Propositions. Primitives are atoms, falsum, implication, conjunction, and disjunction. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Falsum / bottom — a primitive, not an atomic formula encoding of bottom. Making `bot`
      primitive is required by Johansson's minimal logic ([Johansson1937]); without it, the
      type only captures the positive fragment. -/
  | bot
  /-- Implication -/
  | imp (a b : Proposition Atom)
  /-- Conjunction -/
  | and (a b : Proposition Atom)
  /-- Disjunction -/
  | or (a b : Proposition Atom)
deriving DecidableEq, BEq

/-- Negation as a derived connective: `¬A := A → ⊥`. Valid in minimal, intuitionistic, and
classical logic alike. -/
abbrev Proposition.neg : Proposition Atom → Proposition Atom := (Proposition.imp · .bot)

/-- Verum as a derived connective: `⊤ := ⊥ → ⊥`. Derivable in minimal logic. -/
abbrev Proposition.top : Proposition Atom := .imp .bot .bot

/-- Biconditional as a derived connective: `A ↔ B := (A → B) ∧ (B → A)`. -/
abbrev Proposition.iff (A B : Proposition Atom) : Proposition Atom :=
  (A.imp B).and (B.imp A)

instance : Bot (Proposition Atom) := ⟨.bot⟩
instance : Top (Proposition Atom) := ⟨.top⟩

@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or
@[inherit_doc] scoped infix:30 " → " => Proposition.imp
@[inherit_doc] scoped infix:20 " ↔ " => Proposition.iff
@[inherit_doc] scoped prefix:40 " ¬ " => Proposition.neg

/-- Register `Proposition` as an instance of `PropositionalConnectives`. -/
instance : PropositionalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp

/-- Register `HasAnd` instance for `Proposition`. -/
instance : HasAnd (Proposition Atom) where
  and := .and

/-- Register `HasOr` instance for `Proposition`. -/
instance : HasOr (Proposition Atom) where
  or := .or

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
