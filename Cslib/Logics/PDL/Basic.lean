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

/-! ## Induction Principles

Because `Program` and `Formula` are not defined as a mutual inductive type, we provide
induction principles with two motives, one for `Formula` and one for `Program`, that look as
if they were. The modal case for formulas is `d⟨a⟩φ` instead of `Proposition.triangle`.
Both `Formula.induction` and `Program.induction` take the same hypotheses and can be used via
`induction φ using Formula.induction (motive_2 := ...)` and
`induction a using Program.induction (motive_1 := ...)`, respectively.
The other motive must be given explicitly, because `induction` only infers the main one.
-/

/-- Helper for `Formula.induction` and `Program.induction`: induction on the shape of a program,
given that the motive for formulas holds for all its tests. -/
theorem Program.induction_shape
    {motive_1 : Formula Label Atom → Prop} {motive_2 : Program Label Atom → Prop}
    (action : ∀ n, motive_2 (PDL.action n))
    (test : ∀ ψ, motive_1 ψ → motive_2 (PDL.test ψ))
    (seq : ∀ a b, motive_2 a → motive_2 b → motive_2 (PDL.seq a b))
    (union : ∀ a b, motive_2 a → motive_2 b → motive_2 (PDL.union a b))
    (star : ∀ a, motive_2 a → motive_2 (PDL.star a))
    (s : Shape Label) (ts : Tests s → Formula Label Atom) (ih : ∀ t, motive_1 (ts t)) :
    motive_2 ⟨s, ts⟩ := by
  induction s with
  | action n =>
    have : ts = Empty.elim := funext (fun t => t.elim)
    subst this
    exact action n
  | test => exact test (ts ()) (ih ())
  | seq a b iha ihb =>
    have h := seq _ _ (iha (ts ∘ .inl) (fun t => ih _)) (ihb (ts ∘ .inr) (fun t => ih _))
    rwa [show ts = Sum.elim (ts ∘ .inl) (ts ∘ .inr) from funext fun x => by rcases x <;> rfl]
  | union a b iha ihb =>
    have h := union _ _ (iha (ts ∘ .inl) (fun t => ih _)) (ihb (ts ∘ .inr) (fun t => ih _))
    rwa [show ts = Sum.elim (ts ∘ .inl) (ts ∘ .inr) from funext fun x => by rcases x <;> rfl]
  | star a iha => exact star _ (iha ts ih)

/-- Induction principle for PDL formulas, with a second motive for programs. -/
@[elab_as_elim]
theorem Formula.induction
    {motive_1 : Formula Label Atom → Prop} {motive_2 : Program Label Atom → Prop}
    (atom : ∀ p : Atom, motive_1 (.atom p))
    (false : motive_1 ⊥)
    (not : ∀ φ, motive_1 φ → motive_1 (¬φ))
    (or : ∀ φ ψ, motive_1 φ → motive_1 ψ → motive_1 (φ ∨ ψ))
    (diamond : ∀ a φ, motive_2 a → motive_1 φ → motive_1 (d⟨a⟩φ))
    (action : ∀ n, motive_2 (PDL.action n))
    (test : ∀ ψ, motive_1 ψ → motive_2 (PDL.test ψ))
    (seq : ∀ a b, motive_2 a → motive_2 b → motive_2 (PDL.seq a b))
    (union : ∀ a b, motive_2 a → motive_2 b → motive_2 (PDL.union a b))
    (star : ∀ a, motive_2 a → motive_2 (PDL.star a))
    (φ : Formula Label Atom) : motive_1 φ := by
  induction φ with
  | atom p => exact atom p
  | false => exact false
  | not φ ih => exact not φ ih
  | or φ ψ ihφ ihψ => exact or φ ψ ihφ ihψ
  | triangle op φs ih =>
    have h : φs = Sum.elim (φs ∘ .inl) (fun _ => φs (.inr ())) := by
      funext x
      rcases x with _ | ⟨⟩ <;> rfl
    rw [h]
    exact diamond ⟨op, φs ∘ .inl⟩ _
      (Program.induction_shape action test seq union star op _ (fun t => ih (.inl t)))
      (ih (.inr ()))

/-- Induction principle for PDL programs, with a second motive for formulas. -/
@[elab_as_elim]
theorem Program.induction
    {motive_1 : Formula Label Atom → Prop} {motive_2 : Program Label Atom → Prop}
    (atom : ∀ p : Atom, motive_1 (.atom p))
    (false : motive_1 ⊥)
    (not : ∀ φ, motive_1 φ → motive_1 (¬φ))
    (or : ∀ φ ψ, motive_1 φ → motive_1 ψ → motive_1 (φ ∨ ψ))
    (diamond : ∀ a φ, motive_2 a → motive_1 φ → motive_1 (d⟨a⟩φ))
    (action : ∀ n, motive_2 (PDL.action n))
    (test : ∀ ψ, motive_1 ψ → motive_2 (PDL.test ψ))
    (seq : ∀ a b, motive_2 a → motive_2 b → motive_2 (PDL.seq a b))
    (union : ∀ a b, motive_2 a → motive_2 b → motive_2 (PDL.union a b))
    (star : ∀ a, motive_2 a → motive_2 (PDL.star a))
    (a : Program Label Atom) : motive_2 a :=
  Program.induction_shape action test seq union star a.shape a.tests fun t =>
    Formula.induction atom false not or diamond action test seq union star (a.tests t)

end Cslib.Logic.Modal.PDL
