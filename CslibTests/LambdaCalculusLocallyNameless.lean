/-
Copyright (c) 2026 Alex Korbonits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Korbonits
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

/-! # Tests for locally nameless capture-avoiding substitution

Concrete tests for the definitions of variable opening, closing, and substitution on
locally nameless λ-terms. The metatheory in
`Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties` establishes the
expected laws, but consistent mistakes in the definitions could still satisfy them;
these tests pin the definitions down on concrete terms with known results, in the
spirit of <https://github.com/sweirich/lambda-n-ways>.
-/

namespace CslibTests.LambdaCalculusLocallyNameless

open Cslib LambdaCalculus.LocallyNameless.Untyped Term

/-- λ-terms with natural number free variables. -/
abbrev T := Term ℕ

/- Named free variables. Bare numeric literals as operands of `^` and `^*` leave the
`HPow` interpretation of `^` open and make those terms ambiguous, so we bind names. -/
def x : ℕ := 0
def y : ℕ := 1
def z : ℕ := 2
def w : ℕ := 3

/-! ## Variable opening

Opening replaces the targeted de Bruijn index, leaves free variables alone, and
increments the target when passing under a binder. -/

example : (bvar 0 : T) ^ fvar x = fvar x := rfl

example : (fvar y : T) ^ fvar x = fvar y := rfl

-- `bvar 0` under the inner `abs` refers to that binder and must not be opened
example : (abs (bvar 0) : T) ^ fvar x = abs (bvar 0) := rfl

-- `bvar 1` under one `abs` refers to the outermost binding and must be opened
example : (abs (bvar 1) : T) ^ fvar x = abs (fvar x) := rfl

example : (app (bvar 0) (abs (bvar 1)) : T) ^ fvar x = app (fvar x) (abs (fvar x)) := rfl

-- opening at an explicit index
example : (abs (bvar 2) : T)⟦1 ↝ fvar x⟧ = abs (fvar x) := rfl

/-! ## Variable closing

Closing abstracts a free variable to the targeted de Bruijn index, incrementing the
index when passing under a binder. -/

example : ((fvar x : T) ^* x) = bvar 0 := rfl

example : ((fvar y : T) ^* x) = fvar y := rfl

example : (abs (fvar x) : T) ^* x = abs (bvar 1) := rfl

example : (app (fvar x) (abs (fvar x)) : T) ^* x = app (bvar 0) (abs (bvar 1)) := rfl

-- locally nameless terms are canonical: closing α-variants gives syntactically equal terms
example : ((app (fvar y) (fvar y) : T) ^* y) = ((app (fvar z) (fvar z) : T) ^* z) := rfl

/-! ## Substitution

Substitution replaces free variables only, and goes under binders without adjusting
indices (substituends are locally closed, so capture is impossible by construction). -/

example : (fvar x : T)[x := (abs (bvar 0) : T)] = abs (bvar 0) := rfl

example : (fvar y : T)[x := (abs (bvar 0) : T)] = fvar y := rfl

-- substitution never touches bound variables, even with a clashing index
example : (bvar 0 : T)[x := fvar y] = bvar 0 := rfl

-- substitution reaches under binders
example : (abs (app (bvar 0) (fvar y)) : T)[y := fvar z] = abs (app (bvar 0) (fvar z)) := rfl

/- TAPL, section 5.3.4: `(λy. x y)[x := y z]` requires renaming the binder in a named
representation. Locally namelessly, the binder has no name to clash with. -/
example : (abs (app (fvar x) (bvar 0)) : T)[x := app (fvar y) (fvar z)] =
    abs (app (app (fvar y) (fvar z)) (bvar 0)) := rfl

/-! ## Interaction of opening, closing, and substitution

Concrete instances of `open_lc`, `open_close_var`, `close_open`, and `subst_intro`. -/

/-- A locally closed sample term `λ. (0 y) (λ. 0 1)` with free variable `y`. -/
def sample : T := abs (app (app (bvar 0) (fvar y)) (abs (app (bvar 0) (bvar 1))))

/-- The body of `sample`, with a dangling `bvar 0`. -/
def sampleBody : T := app (app (bvar 0) (fvar y)) (abs (app (bvar 0) (bvar 1)))

-- `open_lc`: opening a locally closed term is the identity
example : sample ^ fvar w = sample := rfl

-- `open_close_var`: open a body with a fresh variable, then close over it
example : (sampleBody ^ fvar w) ^* w = sampleBody := rfl

-- `close_open`: close a locally closed term over a free variable, then open with it
example : ((sample ^* y) ^ fvar y) = sample := rfl

-- `subst_intro`: opening to a fresh variable followed by substitution is opening
example : (sampleBody ^ fvar w)[w := app (fvar y) (fvar z)] =
    sampleBody ^ app (fvar y) (fvar z) := rfl

/-! ## Normalization of Church numerals

A fuel-bounded normal-order normalizer, defined here for testing only. Normalizing
Church arithmetic exercises substitution under many nested binders; Church
predecessor in particular is a classic detector of capture bugs. -/

/-- Fuel-bounded normal-order normalization. -/
def nf (fuel : ℕ) (t : T) : T :=
  match fuel, t with
  | 0, t => t
  | _ + 1, bvar i => bvar i
  | _ + 1, fvar x => fvar x
  | fuel + 1, Term.abs m =>
    let x := HasFresh.fresh m.fv
    abs ((nf fuel (m ^ fvar x)) ^* x)
  | fuel + 1, app m n =>
    match nf fuel m with
    | Term.abs m' => nf fuel (m' ^ n)
    | m' => app m' (nf fuel n)

/-- Church numeral `λf. λx. f (f (... x))`. -/
def church (n : ℕ) : T := abs (abs (go n))
where go : ℕ → T
  | 0 => bvar 0
  | n + 1 => app (bvar 1) (go n)

/-- Church addition `λm n f x. m f (n f x)`. -/
def cadd : T :=
  abs (abs (abs (abs (app (app (bvar 3) (bvar 1)) (app (app (bvar 2) (bvar 1)) (bvar 0))))))

/-- Church multiplication `λm n f. m (n f)`. -/
def cmul : T := abs (abs (abs (app (bvar 2) (app (bvar 1) (bvar 0)))))

/-- Church predecessor `λn f x. n (λg h. h (g f)) (λu. x) (λu. u)`. -/
def cpred : T :=
  abs (abs (abs (app
    (app (app (bvar 2) (abs (abs (app (bvar 0) (app (bvar 1) (bvar 3))))))
      (abs (bvar 1)))
    (abs (bvar 0)))))

section
set_option maxRecDepth 10000

example : nf 20 (app (app cadd (church 2)) (church 2)) = church 4 := by rfl

example : nf 20 (app (app cmul (church 2)) (church 3)) = church 6 := by rfl

example : nf 20 (app cpred (church 3)) = church 2 := by rfl

example : nf 20 (app cpred (church 0)) = church 0 := by rfl

end

end CslibTests.LambdaCalculusLocallyNameless
