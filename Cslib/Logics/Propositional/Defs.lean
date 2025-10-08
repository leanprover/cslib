/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Set.Image
import Mathlib.Order.TypeTags

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

namespace PL

/-- Propositions. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Conjunction -/
  | conj (a b : Proposition Atom)
  /-- Disjunction -/
  | disj (a b : Proposition Atom)
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

@[inherit_doc] scoped infix:35 " ⋏ " => Proposition.conj
@[inherit_doc] scoped infix:35 " ⋎ " => Proposition.disj
@[inherit_doc] scoped infix:30 " ⟶ " => Proposition.impl
@[inherit_doc] scoped prefix:40 " ~ " => Proposition.neg

/-- A function on atoms induces a function on propositions. -/
def Proposition.map {Atom Atom' : Type u} (f : Atom → Atom') : Proposition Atom → Proposition Atom'
  | atom x => atom (f x)
  | conj A B => conj (A.map f) (B.map f)
  | disj A B => disj (A.map f) (B.map f)
  | impl A B => impl (A.map f) (B.map f)

instance {Atom Atom' : Type u} : FunLike (Atom → Atom') (Proposition Atom) (Proposition Atom') where
  coe := Proposition.map
  coe_injective' f f' h := by
    ext x
    have : (Proposition.atom x).map f = (Proposition.atom x).map f' :=
      congrFun h (Proposition.atom x)
    grind [Proposition.map]

/-- Theories are arbitrary sets of propositions. -/
abbrev Theory (Atom) := Set (Proposition Atom)

/-- Extend `Proposition.map` to theories. -/
def Theory.map {Atom Atom' : Type u} (f : Atom → Atom') : Theory Atom → Theory Atom' :=
  Set.image (Proposition.map f)

instance {Atom Atom' : Type u} : FunLike (Atom → Atom') (Theory Atom) (Theory Atom') where
  coe := Theory.map
  coe_injective' f f' h := by
    ext x
    have : Theory.map f {(Proposition.atom x)} = Theory.map f' {(Proposition.atom x)} :=
      congrFun h {(Proposition.atom x)}
    simpa [Theory.map, Proposition.map] using this

/-- The base theory is minimal propositional logic. -/
abbrev MPL (Atom) : Theory (Atom) := ∅

/-- Intuitionistic propositional logic adds the principle of explosion (ex falso quodlibet). -/
abbrev IPL [Bot Atom] : Theory Atom :=
  Set.range (⊥ ⟶ ·)

/-- Classical logic further adds double negation elimination. -/
abbrev CPL [Bot Atom] : Theory Atom :=
  IPL ∪ Set.range (fun (A : Proposition Atom) ↦ ~~A ⟶ A)

@[grind]
class IsIntuitionistic [Bot Atom] (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ ⟶ A) ∈ T

@[grind]
class IsClassical [Bot Atom] (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ ⟶ A) ∈ T
  dne (A : Proposition Atom) : (~~A ⟶ A) ∈ T

instance instIsIntuitionisticIPL [Bot Atom] : IsIntuitionistic (Atom := Atom) IPL where
  efq A := Set.mem_range.mpr ⟨A, rfl⟩

instance instIsClassicalCPL [Bot Atom] : IsClassical (Atom := Atom) CPL where
  efq A := Set.mem_union_left _ <| Set.mem_range.mpr ⟨A, rfl⟩
  dne A := Set.mem_union_right _ <| Set.mem_range.mpr ⟨A, rfl⟩

omit [DecidableEq Atom] in
theorem instIsIntuitionisticExtention [Bot Atom] {T T' : Theory Atom} [IsIntuitionistic T]
    (h : T ⊆ T') : IsIntuitionistic T' := by grind

omit [DecidableEq Atom] in
theorem instIsClassicalExtention [Bot Atom] {T T' : Theory Atom} [IsClassical T] (h : T ⊆ T') :
    IsClassical T' := by grind

/-- Attach a bottom element to a theory `T`, and the principle of explosion for that bottom. -/
@[reducible]
def Theory.intuitionisticCompletion (T : Theory Atom) : Theory (WithBot Atom) :=
  T.map (WithBot.some) ∪ IPL

instance instIsIntuitionisticIntuitionisticCompletion (T : Theory Atom) :
    IsIntuitionistic T.intuitionisticCompletion := by grind

end PL
