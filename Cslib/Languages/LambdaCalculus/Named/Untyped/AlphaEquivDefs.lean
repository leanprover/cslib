/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic

/-! # Definitions of α-equivalence

Different definitions of α-equivalence

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012]

## Notation

Following the paper, we use the following correspondence between the paper's abstract syntax
and the λ-calculus terms:

| Paper         | Lean                |
|---------------|---------------------|
| `a`           | `Term.var x`        |
| `P(E₁, E₂)`   | `Term.app m1 m2`    |
| `B([a]E)`     | `Term.abs x m`      |
| `(z a) · E`   | `m.swap x z`        |
| `E{a'/a}`     | `m.subst a (var a')`|

TODO move this into Basic or original `AlphaEquiv` here

-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped.Term

/-- The action of the transposition `(x y)` on a term: simultaneously swaps all occurrences
    of `x` and `y`. Corresponds to `(x y) · E` in the paper.

    This action is also refered to as permutation
-/
def swap (m : Term Var) (x y : Var) : Term Var :=
  match m with
  | var z => var (if z = x then y else if z = y then x else z)
  | abs z m' => abs (if z = x then y else if z = y then x else z) (m'.swap x y)
  | app n1 n2 => app (n1.swap x y) (n2.swap x y)

-- TODO '#' operator possible in Lean like in paper?
-- TODO stay closer to paper notation or already existing Basic.lean?

/-- `∼p#` (Definition 3.2): α-equivalence via permutation with freshness side condition.
-/
inductive AlphaEquivPFresh : Term Var → Term Var → Prop where
  | var {x : Var} : AlphaEquivPFresh (var x) (var x)
  /-- The only difference to `AlphaEquiv` using the weaker freshness `#` condition instead of
      no occurence. Thus using the `swap` operation rather than `rename`.
  -/
  | abs {y x1 x2 : Var} {m1 m2 : Term Var} : y ∉ ({x1, x2} : Finset Var) ∪ m1.fv ∪ m2.fv →
    AlphaEquivPFresh (m1.swap x1 y) (m2.swap x2 y) → AlphaEquivPFresh (abs x1 m1) (abs x2 m2)
  | app {m1 n1 m2 n2 : Term Var} : AlphaEquivPFresh m1 n1 → AlphaEquivPFresh m2 n2 →
    AlphaEquivPFresh (app m1 m2) (app n1 n2)

/-- `∼¹p` (Definition 3.3): α-equivalence via permutation with non-occurrence restricted
    to the bodies only.

    This definition is analogous to the definition of α-equivalence for λ-expressions in
    [Gabbay1999a] (Theorem 2.1, page 216).
-/
inductive AlphaEquivP1 : Term Var → Term Var → Prop where
  | var {x : Var} : AlphaEquivP1 (var x) (var x)
  /-- Only difference to `AlphaEquiv` : non-occurrence condition is only on `m1, m2`,
      not on `x1, x2`.

      When `y ∉ vars(m)`, the operations `rename` and `swap` coincide, so we use `rename` here
      as in the original `AlphaEquiv`.
      -/
  | abs {y x1 x2 m1 m2} : y ∉ m1.vars ∪ m2.vars →
    AlphaEquivP1 (m1.rename x1 y) (m2.rename x2 y) → AlphaEquivP1 (abs x1 m1) (abs x2 m2)
  | app {m1 n1 m2 n2 : Term Var} : AlphaEquivP1 m1 n1 → AlphaEquivP1 m2 n2 →
    AlphaEquivP1 (app m1 m2) (app n1 n2)

/-- `∼r` (Definition 3.4): α-equivalence via the traditional renaming axiom with
    non-occurrence side condition.

   This definition is analogous to the definition of α-equivalence for λ-expressions most commonly
   found in the literature, and certainly in most standard textbooks. One of the first formal
   presentations is in [Church1941] and the same, though rather less formal approach is taken by
   [Barendregt1985] (Definition 2.1.11, page 26).
-/
inductive AlphaEquivR : Term Var → Term Var → Prop where
  | refl {m : Term Var} : AlphaEquivR m m
  | symm {m1 m2 : Term Var} : AlphaEquivR m1 m2 → AlphaEquivR m2 m1
  | trans {m1 m2 m3 : Term Var} : AlphaEquivR m1 m2 → AlphaEquivR m2 m3 → AlphaEquivR m1 m3
  | app {m1 n1 m2 n2 : Term Var} : AlphaEquivR m1 n1 → AlphaEquivR m2 n2 →
    AlphaEquivR (app m1 m2) (app n1 n2)
  /-- Body congruence under the same binder: `m ∼r m'` implies `λ x. m ∼r λ x. m'`. -/
  | abs_congr {x : Var} {m m' : Term Var} :
    AlphaEquivR m m' →
    AlphaEquivR (abs x m) (abs x m')
  /-- Renaming axiom (α-conversion):

      Here `m[x := var x']` is capture-avoiding substitution
      (the paper's `E{a'/a}`). -/
  | alpha {x x' : Var} {m : Term Var} : x' ∉ ({x} : Finset Var) ∪ m.vars →
    AlphaEquivR (abs x m) (abs x' (m.subst x (var x')))

/-- `∼r#` (Definition 3.5): α-equivalence via the renaming axiom with freshness
    side condition.

    Same as `∼r` (Definition 3.4), but the renaming axiom uses a freshness side condition
    (`a' ∉ {a} ∪ fv(E)`) instead of a non-occurrence condition (`a' ∉ {a} ∪ vars(E)`).

    This is analogous to the definition of α-equivalence for λ-expressions one finds in
    [Hindley1988] (Section 1B, page 9)
-/
inductive AlphaEquivRFresh : Term Var → Term Var → Prop where
  | refl {m : Term Var} : AlphaEquivRFresh m m
  | symm {m1 m2 : Term Var} : AlphaEquivRFresh m1 m2 → AlphaEquivRFresh m2 m1
  | trans {m1 m2 m3 : Term Var} : AlphaEquivRFresh m1 m2 → AlphaEquivRFresh m2 m3 →
    AlphaEquivRFresh m1 m3
  | app {m1 m1' m2 m2' : Term Var} :
    AlphaEquivRFresh m1 m1' → AlphaEquivRFresh m2 m2' →
    AlphaEquivRFresh (app m1 m2) (app m1' m2')
  /-- Body congruence under the same binder. -/
  | abs_congr {x : Var} {m m' : Term Var} :
    AlphaEquivRFresh m m' →
    AlphaEquivRFresh (abs x m) (abs x m')
  /-- Renaming axiom with freshness: given `x' ∉ {x} ∪ fv(m)`,
      `λ x. m ∼r# λ x'. m[x := var x']`. -/
  | alpha {x x' : Var} {m : Term Var} :
    x' ∉ ({x} : Finset Var) ∪ m.fv →
    AlphaEquivRFresh (abs x m) (abs x' (m.subst x (var x')))

end LambdaCalculus.Named.Untyped.Term

end Cslib
