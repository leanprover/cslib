/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Logic.Relation
public import Mathlib.Order.Basic

/-! # Relations: Definitions

## References

* [*Term Rewriting and All That*][Baader1998]
* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

namespace Relation

@[nolint defsWithUnderscore]
instance (r : α → α → Prop) (s : Set α) : CoeDep (α → α → Prop) r (s → s → Prop) where
  coe a b := r a b

/-- The empty (heterogeneous) relation, which always returns `False`. -/
@[nolint unusedArguments]
def emptyHRelation {α : Sort u} {β : Sort v} (_ : α) (_ : β) := False

/-- Domain of a relation. -/
def dom (r : α → β → Prop) : Set α := {a | ∃ b, r a b}

/-- Codomain of a relation, aka range. -/
def cod (r : α → β → Prop) : Set β := {b | ∃ a, r a b}

/-- The join of the reflexive transitive closure. This is not named in Mathlib, but see
  `#loogle Relation.Join (Relation.ReflTransGen ?r)` -/
abbrev MJoin (r : α → α → Prop) := Join (ReflTransGen r)

/-- The relation `r` 'up to' the relation `s`. -/
def UpTo (r s : α → α → Prop) : α → α → Prop := Comp s (Comp r s)

/-- A relation `r` is (right) Euclidean if `r a b` and `r a c` guarantee `r b c`. -/
class RightEuclidean (r : α → α → Prop) where
  rightEuclidean : r a b → r a c → r b c

/-- A relation `r` is (left) Euclidean if `r a c` and `r b c` guarantee `r a b`. -/
class LeftEuclidean (r : α → α → Prop) where
  leftEuclidean {a b c} : r a c → r b c → r a b

/-- A relation has the diamond property when all reductions with a common origin are joinable -/
abbrev Diamond (r : α → α → Prop) := ∀ {a b c : α}, r a b → r a c → Join r b c

/-- A relation is confluent when its reflexive transitive closure has the diamond property. -/
abbrev Confluent (r : α → α → Prop) := Diamond (ReflTransGen r)

/-- A relation is semi-confluent when single and multiple steps with common origin
  are multi-joinable. -/
abbrev SemiConfluent (r : α → α → Prop) :=
  ∀ {x y₁ y₂}, ReflTransGen r x y₂ → r x y₁ → Join (ReflTransGen r) y₁ y₂

/-- A relation has the Church Rosser property when equivalence implies multi-joinability. -/
abbrev ChurchRosser (r : α → α → Prop) := ∀ {x y}, EqvGen r x y → Join (ReflTransGen r) x y

/-- An element is reducible with respect to a relation if there is a value it is related to. -/
abbrev Reducible (r : α → α → Prop) (x : α) : Prop := ∃ y, r x y

/-- A relation `r` is serial if every element is `Reducible`, i.e. `Relator.LeftTotal`. -/
class Serial (r : α → α → Prop) where
  serial : Relator.LeftTotal r

/-- An element is normal if it is not reducible. -/
abbrev Normal (r : α → α → Prop) (x : α) : Prop := ¬ Reducible r x

/-- An element is normalizable if it is related to a normal element. -/
abbrev Normalizable (r : α → α → Prop) (x : α) : Prop :=
  ∃ n, ReflTransGen r x n ∧ Normal r n

/-- A relation is normalizing when every element is normalizable. -/
abbrev Normalizing (r : α → α → Prop) : Prop :=
  ∀ x, Normalizable r x

/-- An element `x` is `SN` (for strongly-normalising) for a relation `r` if it is accesible under
the inverse of `r`. -/
abbrev SN (r : α → α → Prop) := Acc (fun a b => r b a)

/-- A relation is terminating when the inverse of its transitive closure is well-founded.
  Note that this is also called Noetherian or strongly normalizing in the literature. -/
abbrev Terminating (r : α → α → Prop) := WellFounded (fun a b => r b a)

/-- A relation is convergent when it is both confluent and terminating. -/
abbrev Convergent (r : α → α → Prop) := Confluent r ∧ Terminating r

/-- A relation is locally confluent when all reductions with a common origin are multi-joinable -/
abbrev LocallyConfluent (r : α → α → Prop) :=
  ∀ {a b c : α}, r a b → r a c → Join (ReflTransGen r) b c

/-- A relation is strongly confluent when single steps are reflexive- and multi-joinable. -/
abbrev StronglyConfluent (r : α → α → Prop) :=
  ∀ {x y₁ y₂}, r x y₁ → r x y₂ → ∃ z, ReflGen r y₁ z ∧ ReflTransGen r y₂ z

/-- Generalization of `Confluent` to two relations. -/
def Commute (r₁ r₂ : α → α → Prop) := ∀ {x y₁ y₂},
  ReflTransGen r₁ x y₁ → ReflTransGen r₂ x y₂ → ∃ z, ReflTransGen r₂ y₁ z ∧ ReflTransGen r₁ y₂ z

/-- Generalization of `StronglyConfluent` to two relations. -/
def StronglyCommute (r₁ r₂ : α → α → Prop) :=
  ∀ {x y₁ y₂}, r₁ x y₁ → r₂ x y₂ → ∃ z, ReflGen r₂ y₁ z ∧ ReflTransGen r₁ y₂ z

/-- Generalization of `Diamond` to two relations. -/
def DiamondCommute (r₁ r₂ : α → α → Prop) :=
  ∀ {x y₁ y₂}, r₁ x y₁ → r₂ x y₂ → ∃ z, r₂ y₁ z ∧ r₁ y₂ z

/-- A pair of subrelations lifts to transitivity on the relation. -/
@[implicit_reducible]
def transLeftRight (s s' r : α → α → Prop) [IsTrans α r] (h : s ≤ r) (h' : s' ≤ r) :
    Trans s s' r where
  trans hab hbc := _root_.trans (h _ _ hab) (h' _ _ hbc)

/-- A subrelation lifts to transitivity on the left of the relation. -/
@[implicit_reducible]
def transLeft (s r : α → α → Prop) [IsTrans α r] (h : s ≤ r) : Trans s r r where
  trans hab hbc := _root_.trans (h _ _ hab) hbc

/-- A subrelation lifts to transitivity on the right of the relation. -/
@[implicit_reducible]
def transRight (s r : α → α → Prop) [IsTrans α r] (h : s ≤ r) : Trans r s r where
  trans hab hbc := _root_.trans hab (h _ _ hbc)

end Relation
