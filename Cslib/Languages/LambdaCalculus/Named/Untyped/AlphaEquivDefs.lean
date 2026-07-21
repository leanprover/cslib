/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic

/-! # Definitions of α-equivalence

Five definitions of α-equivalence from [Crole2012], each capturing the same equivalence
relation on expressions:

* `∼p`  (Definition 3.1): Permutation-based with non-occurrence side condition (`AlphaEquiv`)
* `∼p#` (Definition 3.2): Permutation-based with freshness side condition (`AlphaEquivPFresh`)
* `∼¹p` (Definition 3.3): Permutation-based with non-occurrence on bodies only (`AlphaEquivP1`)
* `∼r`  (Definition 3.4): Traditional renaming axiom with non-occurrence (`AlphaEquivR`)
* `∼r#` (Definition 3.5): Renaming axiom with freshness (`AlphaEquivRFresh`)

The first three definitions use the notion of *atom swapping* (transposition), introduced in
[Gabbay2002] (Section 2, page 3), as a primitive operation for defining α-equivalence. The
key observation from [Gabbay2002] is that α-equivalence can be defined using the notion of
atom swapping in lieu of the traditional renaming/substitution approach.

The last two definitions use the traditional capture-avoiding substitution (renaming) axiom.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012]
* [M. Gabbay and A. Pitts, *A New Approach to Abstract Syntax with Variable Binding*][Gabbay2002]

## Notation

Following the paper [Crole2012], we use the following correspondence between the paper's
abstract syntax and the λ-calculus terms:

| Paper         | Lean                |
|---------------|---------------------|
| `a`           | `Term.var x`        |
| `P(E₁, E₂)`   | `Term.app m1 m2`    |
| `B([a]E)`     | `Term.abs x m`      |
| `(z a) · E`   | `m.swap x z`        |
| `E{a'/a}`     | `m.subst a (var a')`|
| `π · E`       | `m.permute π`       |

-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped.Term


/-- The action `π · E` of a permutation on a term, as used in [Crole2012].

Since some lemmas in section 6 are proven for general permutations, we have to introduce
this notion here aswell and derive the special case using `swap` accordingly.
-/
def permute (m : Term Var) (π : Equiv.Perm Var) : Term Var :=
  match m with
  | var x => var (π x)
  | abs x m => abs (π x) (m.permute π)
  | app m n => app (m.permute π) (n.permute π)

/-- The action of the transposition `(x y)` on a term: simultaneously swaps all occurrences
of `x` and `y`. Corresponds to `(x y) · E` in [Crole2012] (Section 2).

`swap` is is one special case of a permutation: the transposition that exchanges exactly two atoms
a and b and fixes everything else.
-/
def swap (m : Term Var) (x y : Var) : Term Var := m.permute (Equiv.swap x y)

/-- **Definition 3.2** [Crole2012]: `∼p#` - α-equivalence via permutation with freshness
side condition.

The rule `pi#` uses the freshness condition `z # a, b, E, E'`
(i.e., `z ∉ fv(E) ∪ fv(E') ∪ {a, b}`) instead of the non-occurrence condition
`z ∉ vars(E) ∪ vars(E') ∪ {a, b}` used in Definition 3.1 (`AlphaEquiv`).
-/
inductive AlphaEquivPFresh : Term Var → Term Var → Prop where
  | var {x : Var} : AlphaEquivPFresh (var x) (var x)
  | abs {y x1 x2 : Var} {m1 m2 : Term Var} :
    y ∉ ({x1, x2} : Finset Var) ∪ m1.fv ∪ m2.fv →
    AlphaEquivPFresh (m1.swap x1 y) (m2.swap x2 y) →
    AlphaEquivPFresh (abs x1 m1) (abs x2 m2)
  | app {m1 n1 m2 n2 : Term Var} :
    AlphaEquivPFresh m1 n1 → AlphaEquivPFresh m2 n2 →
    AlphaEquivPFresh (app m1 m2) (app n1 n2)

/-- **Definition 3.3** [Crole2012]: `∼¹p` - α-equivalence via permutation with non-occurrence
restricted to the bodies only.

This definition is analogous to the definition of α-equivalence for λ-expressions in
[Gabbay1999a] (Theorem 2.1, page 216). The notation `∼¹p` arises from three variants `∼ⁱp`
of `∼p` considered in Proposition 4.3 of [Crole2012].
-/
inductive AlphaEquivP1 : Term Var → Term Var → Prop where
  | var {x : Var} : AlphaEquivP1 (var x) (var x)
  | abs {y x1 x2 m1 m2} :
    y ∉ m1.vars ∪ m2.vars →
    AlphaEquivP1 (m1.rename x1 y) (m2.rename x2 y) →
    AlphaEquivP1 (abs x1 m1) (abs x2 m2)
  | app {m1 n1 m2 n2 : Term Var} :
    AlphaEquivP1 m1 n1 → AlphaEquivP1 m2 n2 →
    AlphaEquivP1 (app m1 m2) (app n1 n2)

/-- **Definition 3.4** [Crole2012]: `∼r` - α-equivalence via the traditional renaming axiom
with non-occurrence side condition.

This definition is analogous to the definition of α-equivalence for λ-expressions most commonly
found in the literature. One of the first formal presentations is in [Church1941] and the same,
though rather less formal approach is taken by [Barendregt1985] (Definition 2.1.11).
-/
inductive AlphaEquivR : Term Var → Term Var → Prop where
  | refl {m : Term Var} : AlphaEquivR m m
  | symm {m1 m2 : Term Var} : AlphaEquivR m1 m2 → AlphaEquivR m2 m1
  | trans {m1 m2 m3 : Term Var} : AlphaEquivR m1 m2 → AlphaEquivR m2 m3 → AlphaEquivR m1 m3
  | app {m1 n1 m2 n2 : Term Var} :
    AlphaEquivR m1 n1 → AlphaEquivR m2 n2 →
    AlphaEquivR (app m1 m2) (app n1 n2)
  | abs_congr {x : Var} {m m' : Term Var} :
    AlphaEquivR m m' →
    AlphaEquivR (abs x m) (abs x m')
  | alpha {x x' : Var} {m : Term Var} :
    x' ∉ ({x} : Finset Var) ∪ m.vars →
    AlphaEquivR (abs x m) (abs x' (m.subst x (var x')))

/-- **Definition 3.5** [Crole2012]: `∼r#` - α-equivalence via the renaming axiom with
freshness side condition.

Same as `∼r` (Definition 3.4), but the renaming axiom uses a freshness side condition
(`a' ∉ {a} ∪ fv(E)`) instead of a non-occurrence condition (`a' ∉ {a} ∪ vars(E)`).

This is analogous to the definition of α-equivalence for λ-expressions one finds in
[Hindley1988] (Section 1B, page 9).
-/
inductive AlphaEquivRFresh : Term Var → Term Var → Prop where
  | refl {m : Term Var} : AlphaEquivRFresh m m
  | symm {m1 m2 : Term Var} :
    AlphaEquivRFresh m1 m2 → AlphaEquivRFresh m2 m1
  | trans {m1 m2 m3 : Term Var} :
    AlphaEquivRFresh m1 m2 → AlphaEquivRFresh m2 m3 →
    AlphaEquivRFresh m1 m3
  | app {m1 m1' m2 m2' : Term Var} :
    AlphaEquivRFresh m1 m1' → AlphaEquivRFresh m2 m2' →
    AlphaEquivRFresh (app m1 m2) (app m1' m2')
  | abs_congr {x : Var} {m m' : Term Var} :
    AlphaEquivRFresh m m' →
    AlphaEquivRFresh (abs x m) (abs x m')
  | alpha {x x' : Var} {m : Term Var} :
    x' ∉ ({x} : Finset Var) ∪ m.fv →
    AlphaEquivRFresh (abs x m) (abs x' (m.subst x (var x')))

end LambdaCalculus.Named.Untyped.Term

end Cslib
