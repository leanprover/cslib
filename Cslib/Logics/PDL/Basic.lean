/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger, Fabrizio Montesi
-/

module

public import Mathlib.Logic.Equiv.Defs
public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Foundations.Logic.Operators
public import Cslib.Foundations.Semantics.Frame.LTS
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Logics.Modal.Basic
public import Cslib.Logics.Modal.Semantics

/-! # Syntax of Propositional Dynamic Logic (PDL) -/

@[expose] public section

namespace Cslib.Logic.Modal.PDL

open PFunctor

universe u v

variable {Label : Type u}

/-! ## Syntax -/

inductive Shape where
  | action (name : Label)
  | test
  | seq (a b : Shape)
  | union (a b : Shape)
  | star (a : Shape)

def Tests : @Shape Label → Type
  | .action _ => Empty
  | .test => Unit
  | .seq a b => Tests a ⊕ Tests b
  | .union a b => Tests a ⊕ Tests b
  | .star a => Tests a

abbrev signature : PFunctor :=
  ⟨@Shape Label, fun a => Tests a ⊕ Unit⟩

variable {Atom : Type v}

abbrev Formula := Cslib.Logic.Modal.Proposition (@signature Label) Atom

structure Program where
  shape : @Shape Label
  tests : Tests shape → @Formula Label Atom

def action (name : Label) : @Program Label Atom :=
  ⟨.action name, Empty.elim⟩

def test (ψ : @Formula Label Atom) : @Program Label Atom :=
  ⟨.test, fun _ => ψ⟩

def seq (a b : @Program Label Atom) : @Program Label Atom :=
  ⟨.seq a.shape b.shape, Sum.elim a.tests b.tests⟩

def union (a b : @Program Label Atom) : @Program Label Atom :=
  ⟨.union a.shape b.shape, Sum.elim a.tests b.tests⟩

def star (a : @Program Label Atom) : @Program Label Atom :=
  ⟨.star a.shape, a.tests⟩

def diamond (a : @Program Label Atom) (φ : @Formula Label Atom) : @Formula Label Atom :=
  .triangle a.shape (Sum.elim a.tests (fun _ => φ))

instance : HasDynamicDiamond (@Formula Label Atom) (@Program Label Atom) := ⟨diamond⟩

/-- Box as the dual of the diamond (only the target is negated, not the tests). -/
def box (a : @Program Label Atom) (φ : @Formula Label Atom) : @Formula Label Atom :=
  ¬ diamond a (¬ φ)

instance : HasDynamicBox (@Formula Label Atom) (@Program Label Atom) := ⟨box⟩

/-! ## Example and Notation -/

-- ⟨(?p ; a)*⟩q
def exampleFormula : @Formula Nat Nat :=
  diamond (star (seq (test (.atom 0)) (action 0))) (.atom 1)

notation "?'" ψ:arg => test ψ
notation a:(arg-1) ";'" b:(arg-1) => seq a b
notation a:(arg-1) "∪" b:(arg-1) => union a b
notation a:(arg-1) "*" => star a

instance : OfNat (@Program Nat Atom) k := ⟨action k⟩
instance : OfNat (@Formula Label Nat) k := ⟨.atom k⟩
-- above not needed with this:
instance : Coe Nat (@Program Nat Atom) := ⟨fun k => action k⟩
instance : Coe Nat (@Formula Label Nat) := ⟨fun k => .atom k⟩

def sameExampleFormula (p q : Nat) (a : Nat) : @Formula Nat Nat :=
  d⟨ (?' p ;' a)*⟩ q

/-! ## Formulas as Unary-PFunctor Propositions -/

open Cslib.Logic.Modal in
/-- View a PDL formula over the unary signature with one modality per program. -/
def Formula.toUnary :
    @Formula Label Atom → Proposition (PFunctor.mkUnary (@Program Label Atom)) Atom
  | .atom p => .atom p
  | .false => .false
  | .not φ => .not (toUnary φ)
  | .or φ ψ => .or (toUnary φ) (toUnary ψ)
  | .triangle s φs => .triangle ⟨s, φs ∘ Sum.inl⟩ (fun _ => toUnary (φs (.inr ())))

end Cslib.Logic.Modal.PDL
