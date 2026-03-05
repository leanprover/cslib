/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.HML.Basic
public import Cslib.Foundations.Logic.LogicalEquivalence

@[expose] public section

/-! # Logical Equivalence in HML

This module defines logical equivalence for HML propositions and instantiates `LogicalEquivalence`.
-/

namespace Cslib.Logic.HML

/-- Logical equivalence for HML propositions. -/
def Proposition.Equiv {State : Type u} {Label : Type v} (a b : Proposition Label) : Prop :=
  ∀ lts : LTS State Label, a.denotation lts = b.denotation lts

@[scoped grind =]
theorem Proposition.equiv_def {State : Type u} {Label : Type v} (a b : Proposition Label) :
    Equiv (State := State) a b ↔
    (∀ lts : LTS State Label, a.denotation lts = b.denotation lts) := by rfl

/-- Propositional contexts. -/
inductive Proposition.Context (Label : Type u) : Type u where
  | hole
  | andL (c : Context Label) (φ : Proposition Label)
  | andR (φ : Proposition Label) (c : Context Label)
  | orL (c : Context Label) (φ : Proposition Label)
  | orR (φ : Proposition Label) (c : Context Label)
  | diamond (μ : Label) (c : Context Label)
  | box (μ : Label) (c : Context Label)

/-- Replaces a hole in a propositional context with a proposition. -/
@[scoped grind =]
def Proposition.Context.fill (c : Context Label) (φ : Proposition Label) :=
  match c with
  | hole => φ
  | andL c φ' => (c.fill φ).and φ'
  | andR φ' c => φ'.and (c.fill φ)
  | orL c φ' => (c.fill φ).or φ'
  | orR φ' c => φ'.or (c.fill φ)
  | diamond μ c => .diamond μ (c.fill φ)
  | box μ c => .box μ (c.fill φ)

instance : HasContext (Proposition Label) := ⟨Proposition.Context Label, Proposition.Context.fill⟩

open scoped Proposition Proposition.Context

instance : IsEquiv (Proposition Label) (Proposition.Equiv (State := State) (Label := Label)) where
  refl := by grind
  symm := by grind
  trans := by grind

instance {State : Type u} {Label : Type v} :
    Congruence (Proposition Label) (Proposition.Equiv (State := State) (Label := Label)) where
  elim :
      Covariant (Proposition.Context Label) (Proposition Label) (Proposition.Context.fill)
      Proposition.Equiv := by
    intro ctx a b hab lts
    specialize hab lts
    induction ctx
      <;> simp only [Proposition.Context.fill, Proposition.denotation]
      <;> grind

/-- Bundled version of a judgement for `Satisfy`. -/
structure Satisfies.Judgement (State : Type u) (Label : Type v) where
  lts : LTS State Label
  state : State
  φ : Proposition Label

/-- `Satisfies` variant using bundled judgements. -/
def Satisfies.Bundled (j : Satisfies.Judgement State Label) := Satisfies j.lts j.state j.φ

@[scoped grind =]
theorem Satisfies.bundled_char : Satisfies.Bundled j ↔ Satisfies j.lts j.state j.φ := by rfl

/-- Judgemental contexts. -/
structure Satisfies.Context (State : Type u) (Label : Type v) where
  lts : LTS State Label
  state : State

/-- Fills a judgemental context with a proposition. -/
def Satisfies.Context.fill (c : Satisfies.Context State Label) (φ : Proposition Label) :
    Satisfies.Judgement State Label where
  lts := c.lts
  state := c.state
  φ := φ

instance judgementalContext :
    HasHContext (Satisfies.Judgement State Label) (Proposition Label) :=
  ⟨Satisfies.Context State Label, Satisfies.Context.fill⟩

instance : LogicalEquivalence
    (Proposition Label) (Satisfies.Judgement State Label) (Satisfies.Bundled) where
  eqv := Proposition.Equiv
  eqv_fill_valid {a b : Proposition Label} (heqv : a.Equiv (State := State) b)
      (c : HasHContext.Context (Satisfies.Judgement State Label) (Proposition Label))
      (h : Satisfies.Bundled c<[a]) : Satisfies.Bundled c<[b] := by
    simp only [Satisfies.bundled_char, HasHContext.fill, Satisfies.Context.fill]
    simp only [Satisfies.bundled_char, HasHContext.fill, Satisfies.Context.fill] at h
    grind

end Cslib.Logic.HML
