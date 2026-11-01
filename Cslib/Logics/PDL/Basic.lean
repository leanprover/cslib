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

PDL is about the behaviour of programs and originates from [FischerLadner1979].
It extends Hennessy-Milner Logic from `Cslib.Logics.HML.Basic` with a `test`
operator and three ways to combine programs: `seq`, `union` and `star`.

We define a PDL `Program` as a `Shape` plus a map from its test positions to formulas.
This avoids a mutual or nested inductive, and allows us to define a `PFunctor` that
we can use as the `signature` to define `Formula` via `Cslib.Logic.Modal.Proposition`.
This is inspired by the "pre" placeholders [Koole2026] uses for dynamic algebras.

## References

* [Michael J. Fischer and Richard E. Ladner,
  *Propositional Dynamic Logic of Regular Programs*][FischerLadner1979]
* [D. Harel, D. Kozen and J. Tiuryn, *Dynamic Logic*][HarelKozenTiuryn2000]
* [E. Koole, *Extending Interpolation to PDL with Frame Conditions*][Koole2026]
* The code is also inspired by [lean4-pdl](https://github.com/m4lvin/lean4-pdl).

-/

@[expose] public section

namespace Cslib.Logic.Modal.PDL

universe u v

variable (Label : Type u)

/-! ## Syntax -/

inductive Shape where
  | action (name : Label)
  | test
  | seq (a b : Shape)
  | union (a b : Shape)
  | star (a : Shape)
  deriving DecidableEq, Repr

def Tests {Label} : Shape Label → Type
  | .action _ => Empty
  | .test => Unit
  | .seq a b => Tests a ⊕ Tests b
  | .union a b => Tests a ⊕ Tests b
  | .star a => Tests a

abbrev signature : PFunctor :=
  ⟨Shape Label, fun a => Tests a ⊕ Unit⟩

variable (Atom : Type v)

abbrev Formula := Cslib.Logic.Modal.Proposition (signature Label) Atom

/-- A PDL program, internally represented by a `Shape` and a function
that maps the `Tests` positions in the shape to actual Formulas. -/
structure Program where
  shape : Shape Label
  tests : Tests shape → Formula Label Atom

variable {Label Atom}

/-- An atomic program. -/
def action (name : Label) : Program Label Atom :=
  ⟨.action name, Empty.elim⟩

/-- Test program. -/
def test (ψ : Formula Label Atom) : Program Label Atom :=
  ⟨.test, fun _ => ψ⟩

/-- Sequential composition of programs. -/
def seq (a b : Program Label Atom) : Program Label Atom :=
  ⟨.seq a.shape b.shape, Sum.elim a.tests b.tests⟩

/-- Non-deterministic choice between two programs. -/
def union (a b : Program Label Atom) : Program Label Atom :=
  ⟨.union a.shape b.shape, Sum.elim a.tests b.tests⟩

/-- Kleene star to iterate a program any number of times (including 0). -/
def star (a : Program Label Atom) : Program Label Atom :=
  ⟨.star a.shape, a.tests⟩

/-- PDL diamond modality: after some execution of `a` we reach a state satisfying `φ`. -/
def diamond (a : Program Label Atom) (φ : Formula Label Atom) : Formula Label Atom :=
  .triangle a.shape (Sum.elim a.tests (fun _ => φ))

instance : HasDynamicDiamond (Formula Label Atom) (Program Label Atom) := ⟨diamond⟩

/-- The dual of `diamond`. After any execution of `a` we reach a state satisfying `φ`. -/
def box (a : Program Label Atom) (φ : Formula Label Atom) : Formula Label Atom :=
  ¬ diamond a (¬ φ)

instance : HasDynamicBox (Formula Label Atom) (Program Label Atom) := ⟨box⟩

@[scoped grind =]
theorem diamond_def : diamond a φ = d⟨a⟩φ := rfl

@[scoped grind =]
theorem box_def : box a φ = d[a]φ := rfl

/-! ## Notation -/

scoped notation "?' " ψ:arg => test ψ

scoped infixr:70 " ;' " => seq

instance : Union (Program Label Atom) := ⟨union⟩

scoped postfix:max "*" => star

/-! ## TODO: Induction Principles? -/

-- Can we have a principle with two motives, one for `Formula` and one for `Program` here?
-- Should be as nicely usable as the mutual inductions in lean4-pdl.

end Cslib.Logic.Modal.PDL
