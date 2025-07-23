/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

import Mathlib.Logic.Relation

/-! # Relations -/

universe u v

section Relation

/-- Union of two relations. -/
def Relation.union (r s : α → β → Prop) : α → β → Prop :=
  fun x y => r x y ∨ s x y

instance {α : Type u} {β : Type v} : Union (α → β → Prop) where
  union := Relation.union

/-- Inverse of a relation. -/
def Relation.inv (r : α → β → Prop) : β → α → Prop := flip r

/-- The relation `r` 'up to' the relation `s`. -/
def Relation.upTo (r s : α → α → Prop) : α → α → Prop := Relation.Comp s (Relation.Comp r s)

/-- The identity relation. -/
inductive Relation.Id : α → α → Prop where
| id {x : α} : Id x x

/-- A relation has the diamond property when all reductions with a common origin are joinable -/
abbrev Diamond (R : α → α → Prop) := ∀ {A B C : α}, R A B → R A C → (∃ D, R B D ∧ R C D)

/-- A relation is confluent when its reflexive transitive closure has the diamond property. -/
abbrev Confluence (R : α → α → Prop) := Diamond (Relation.ReflTransGen R)

/-- Extending a multistep reduction by a single step preserves multi-joinability. -/
lemma Relation.ReflTransGen.diamond_extend (h : Diamond R) :
  Relation.ReflTransGen R A B →
  R A C →
  ∃ D, Relation.ReflTransGen R B D ∧ Relation.ReflTransGen R C D := by
  intros AB _
  revert C
  induction AB using Relation.ReflTransGen.head_induction_on <;> intros C AC
  case refl => exact ⟨C, ⟨single AC, by rfl⟩⟩
  case head A'_C' _ ih =>
    obtain ⟨D, ⟨CD, C'_D⟩⟩ := h AC A'_C'
    obtain ⟨D', ⟨B_D', D_D'⟩⟩ := ih C'_D
    exact ⟨D', ⟨B_D', head CD D_D'⟩⟩

/-- The diamond property implies confluence. -/
theorem Relation.ReflTransGen.diamond_confluence (h : Diamond R) : Confluence R := by
  intros A B C AB BC
  revert C
  induction AB using Relation.ReflTransGen.head_induction_on <;> intros C BC
  case refl => exists C
  case head _ _ A'_C' _ ih =>
    obtain ⟨D, ⟨CD, C'_D⟩⟩ := diamond_extend h BC A'_C'
    obtain ⟨D', ⟨B_D', D_D'⟩⟩ := ih C'_D
    exact ⟨D', ⟨B_D', trans CD D_D'⟩⟩

-- not sure why this doesn't compile as an "instance" but oh well
def trans_of_subrelation {α : Type _} (s s' r : α → α → Prop) (hr : Transitive r)
    (h : ∀ a b : α, s a b → r a b) (h' : ∀ a b : α, s' a b → r a b) : Trans s s' r where
  trans := by
    intro a b c hab hbc
    replace hab := h _ _ hab
    replace hbc := h' _ _ hbc
    exact hr hab hbc

def trans_of_subrelation_left {α : Type _} (s r : α → α → Prop) (hr : Transitive r)
    (h : ∀ a b : α, s a b → r a b) : Trans s r r where
  trans := by
    intro a b c hab hbc
    replace hab := h _ _ hab
    exact hr hab hbc

def trans_of_subrelation_right {α : Type _} (s r : α → α → Prop) (hr : Transitive r)
    (h : ∀ a b : α, s a b → r a b) : Trans r s r where
  trans := by
    intro a b c hab hbc
    replace hbc := h _ _ hbc
    exact hr hab hbc

/-- This is a straightforward but useful specialisation of a more general result in
`Mathlib.Logic.Relation`. -/
theorem church_rosser_of_diamond {α : Type _} {r : α → α → Prop}
    (h : ∀ a b c, r a b → r a c → Relation.Join r b c) :
    Equivalence (Relation.Join (Relation.ReflTransGen r)) := by
  apply Relation.equivalence_join_reflTransGen
  intro a b c hab hac
  let ⟨d, hd⟩ := h a b c hab hac
  use d
  constructor
  . exact Relation.ReflGen.single hd.1
  . exact Relation.ReflTransGen.single hd.2

end Relation
