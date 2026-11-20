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

NOTES:

- The `Cslib.Logic.Modal.Proposition.nabla` should *not* be used for `Formula` here,
  because via `PropositionMap.not` it negates the formulas at *all* argument positions.
  Then `[?p]q` would become `¬⟨?¬p⟩¬q` whereas we want it to be `¬⟨?p⟩¬q`, where the
  formula in the test position is not negated but stays as it is.

  Instead, we define our own box operator in `Cslib.Logic.Modal.PDL.box`.

## References

* [Michael J. Fischer and Richard E. Ladner,
  *Propositional Dynamic Logic of Regular Programs*][FischerLadner1979]
* [D. Harel, D. Kozen and J. Tiuryn, *Dynamic Logic*][HarelKozenTiuryn2000]
* [E. Koole, *Extending Interpolation to PDL with Frame Conditions*][Koole2026]
* The code is also inspired by [lean4-pdl](https://github.com/m4lvin/lean4-pdl).

-/

@[expose] public section

namespace Cslib.Logic.Modal.PDL

universe u v w

variable (Label : Type u)

/-! ## Syntax -/

/-- The shape of a PDL program, where test formulas are not yet provided. -/
inductive Shape where
  | action (name : Label)
  | test
  | seq (a b : Shape)
  | union (a b : Shape)
  | star (a : Shape)
  deriving DecidableEq, Repr

/-- As many copies of `Unit` as there are test in the given `Shape`. -/
def Tests {Label} : Shape Label → Type
  | .action _ => Empty
  | .test => Unit
  | .seq a b => Tests a ⊕ Tests b
  | .union a b => Tests a ⊕ Tests b
  | .star a => Tests a

/-- The modal signature for PDL. -/
abbrev signature : PFunctor :=
  ⟨Shape Label, fun a => Tests a ⊕ Unit⟩

variable (Atom : Type v)

/-- Formulas of Propositional Dynamic Logic. Note that this is defined via `Shape` and `Tests`.
If you want mutual recursion, use `Formula.induction` and `Program.induction`. -/
abbrev Formula := Cslib.Logic.Modal.Proposition (signature Label) Atom

/-- A PDL program, internally represented by a `Shape` and a function
that maps the `Tests` positions in the shape to actual Formulas. -/
structure Program where
  /-- The shape of the program, including `Shape.test`-placeholders -/
  shape : Shape Label
  /-- The actual test formulas, one for each placeholder. -/
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

/-- Notation for the test operator `Program.test`. -/
scoped notation "?' " ψ:arg => test ψ

/-- Notation for sequential composition `Program.seq`. -/
scoped infixr:70 " ;' " => seq

/-- Notation for non-deterministic choice `Program.seq`. -/
instance : Union (Program Label Atom) := ⟨union⟩

/-- Notation for the iteration operator `Program.star`. -/
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
given that we already have the formula motive for all test formulas. -/
def Program.inductionOnShape
    {motive_1 : Formula Label Atom → Sort w} {motive_2 : Program Label Atom → Sort w}
    (action : ∀ n, motive_2 (PDL.action n))
    (test : ∀ ψ, motive_1 ψ → motive_2 (PDL.test ψ))
    (seq : ∀ a b, motive_2 a → motive_2 b → motive_2 (PDL.seq a b))
    (union : ∀ a b, motive_2 a → motive_2 b → motive_2 (PDL.union a b))
    (star : ∀ a, motive_2 a → motive_2 (PDL.star a))
    (s : Shape Label) (ts : Tests s → Formula Label Atom) (ih : ∀ t, motive_1 (ts t)) :
    motive_2 ⟨s, ts⟩ :=
  match s with
  | .action n => by
    have : ts = Empty.elim := funext (fun t => t.elim)
    subst this
    exact action n
  | .test => test (ts ()) (ih ())
  | .seq a b  => by
    let iha := Program.inductionOnShape action test seq union star a
    let ihb := Program.inductionOnShape action test seq union star b
    have h := seq _ _ (iha (ts ∘ .inl) (fun t => ih _)) (ihb (ts ∘ .inr) (fun t => ih _))
    rwa [show ts = Sum.elim (ts ∘ .inl) (ts ∘ .inr) from funext fun x => by rcases x <;> rfl]
  | .union a b => by
    let iha := Program.inductionOnShape action test seq union star a
    let ihb := Program.inductionOnShape action test seq union star b
    have h := union _ _ (iha (ts ∘ .inl) (fun t => ih _)) (ihb (ts ∘ .inr) (fun t => ih _))
    rwa [show ts = Sum.elim (ts ∘ .inl) (ts ∘ .inr) from funext fun x => by rcases x <;> rfl]
  | .star a =>
    let iha := Program.inductionOnShape action test seq union star a
    star _ (iha ts ih)

/-- Induction principle for PDL formulas, with a second motive for programs. -/
@[elab_as_elim]
def Formula.induction
    {motive_1 : Formula Label Atom → Sort w} {motive_2 : Program Label Atom → Sort w}
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
    (φ : Formula Label Atom) : motive_1 φ :=
  match φ with
  | .atom p => atom p
  | .false => false
  | .not φ =>
      let ih := Formula.induction atom false not or diamond action test seq union star φ
      not φ ih
  | .or φ ψ =>
      let ihφ := Formula.induction atom false not or diamond action test seq union star φ
      let ihψ := Formula.induction atom false not or diamond action test seq union star ψ
      or φ ψ ihφ ihψ
  | .triangle op φs => by
      let ih := fun i =>
        Formula.induction atom false not or diamond action test seq union star (φs i)
      have h : φs = Sum.elim (φs ∘ .inl) (fun _ => φs (.inr ())) := by
        funext x
        rcases x with _ | ⟨⟩ <;> rfl
      rw [h]
      exact diamond ⟨op, φs ∘ .inl⟩ _
        (Program.inductionOnShape action test seq union star op _ (fun t => ih (.inl t)))
        (ih (.inr ()))

/-- Induction principle for PDL programs, with a second motive for formulas. -/
@[elab_as_elim]
def Program.induction
    {motive_1 : Formula Label Atom → Sort w} {motive_2 : Program Label Atom → Sort w}
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
  Program.inductionOnShape action test seq union star a.shape a.tests fun t =>
    Formula.induction atom false not or diamond action test seq union star (a.tests t)

end Cslib.Logic.Modal.PDL
