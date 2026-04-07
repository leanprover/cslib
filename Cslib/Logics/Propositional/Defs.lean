/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Order.TypeTags

@[expose] public section

/-! # Propositions and theories

## Main definitions

- `Proposition` : the type of propositions over a given type of atom. This type has a `Bot`
instance whenever `Atom` does, and a `Top` whenever `Atom` is inhabited.
- `Theory` : set of `Proposition`.
- `IsIntuitionistic` : a theory is intuitionistic if it contains the principle of explosion.
- `IsClassical` : an intuitionistic theory is classical if it further contains double negation
elimination.
- `Proposition.map`, `Theory.map` : a map between `Atom` types extends to a map between
propositions and theories.
- `Theory.intuitionisticCompletion` : the freely generated intuitionistic theory extending a given
theory.

## Notation

We introduce notation for the logical connectives: `⊥ ⊤ ⋏ ⋎ ⟶ ~` for, respectively, falsum, verum,
conjunction, disjunction, implication and negation.
-/

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

/-- A function on atoms induces a function on propositions. -/
def Proposition.map {Atom Atom' : Type u} (f : Atom → Atom') : Proposition Atom → Proposition Atom'
  | atom x => atom (f x)
  | and A B => (A.map f) ∧ (B.map f)
  | or A B => (A.map f) ∨ (B.map f)
  | impl A B => (A.map f) → (B.map f)

instance : Functor Proposition where
  map := Proposition.map

/-- Theories are arbitrary sets of propositions. -/
abbrev Theory (Atom) := Set (Proposition Atom)

namespace Theory

instance : Functor Theory where
  map f := Set.image (Proposition.map f)

/-- The empty theory corresponds to minimal propositional logic. -/
abbrev MPL : Theory (Atom) := ∅

/-- Intuitionistic propositional logic adds the principle of explosion (ex falso quodlibet). -/
abbrev IPL [Bot Atom] : Theory Atom :=
  Set.range (⊥ → ·)

/-- Classical logic further adds double negation elimination. -/
abbrev CPL [Bot Atom] : Theory Atom :=
  Set.range (fun (A : Proposition Atom) ↦ ¬¬A → A)

/-- A theory is intuitionistic if it validates ex falso quodlibet. -/
@[scoped grind]
class IsIntuitionistic [Bot Atom] (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ → A) ∈ T

omit [DecidableEq Atom] in
@[scoped grind =]
theorem isIntuitionisticIff [Bot Atom] (T : Theory Atom) : IsIntuitionistic T ↔ IPL ⊆ T := by grind

/-- A theory is classical if it validates double-negation elimination. -/
@[scoped grind]
class IsClassical [Bot Atom] (T : Theory Atom) where
  dne (A : Proposition Atom) : (¬¬A → A) ∈ T

omit [DecidableEq Atom] in
@[scoped grind =]
theorem isClassicalIff [Bot Atom] (T : Theory Atom) : IsClassical T ↔ CPL ⊆ T := by grind

instance instIsIntuitionisticIPL [Bot Atom] : IsIntuitionistic (Atom := Atom) IPL where
  efq A := Set.mem_range.mpr ⟨A, rfl⟩

instance instIsClassicalCPL [Bot Atom] : IsClassical (Atom := Atom) CPL where
  dne A := Set.mem_range.mpr ⟨A, rfl⟩

omit [DecidableEq Atom] in
@[scoped grind →]
theorem instIsIntuitionisticExtention [Bot Atom] {T T' : Theory Atom} [IsIntuitionistic T]
    (h : T ⊆ T') : IsIntuitionistic T' := by grind

omit [DecidableEq Atom] in
@[scoped grind →]
theorem instIsClassicalExtention [Bot Atom] {T T' : Theory Atom} [IsClassical T] (h : T ⊆ T') :
    IsClassical T' := by grind

/-- Attach a bottom element to a theory `T`, and the principle of explosion for that bottom. -/
@[reducible]
def intuitionisticCompletion (T : Theory Atom) : Theory (WithBot Atom) :=
  (WithBot.some <$> T) ∪ IPL

instance instIsIntuitionisticIntuitionisticCompletion (T : Theory Atom) :
    IsIntuitionistic T.intuitionisticCompletion := by grind

end Cslib.Logic.PL.Theory
