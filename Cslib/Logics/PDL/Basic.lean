/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger, Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Foundations.Logic.Operators
public import Cslib.Logics.Modal.Basic

/-! # Syntax of Propositional Dynamic Logic (PDL)

We define a PDL `Program` as a shape plus a map from its test positions to formulas.
This avoids a mutual or nested inductive, an allows us to define a `PFunctor` that
we can use as the `signature` to define `Formula` via `Cslib.Logic.Modal.Proposition`.
-/

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
  deriving DecidableEq, Repr

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

/-! ## Notation -/

scoped notation "?'" ψ:arg => test ψ

infixr:70 ";'" => seq

infixl:65 "∪" => union

postfix:max "*" => star

scoped instance : Coe Nat (@Program Nat Atom) := ⟨fun k => action k⟩

end Cslib.Logic.Modal.PDL
