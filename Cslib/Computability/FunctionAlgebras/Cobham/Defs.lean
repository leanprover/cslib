/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Cslib.Init
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Cobham's function algebra

This file defines Cobham's machine-independent characterization
of the polynomial-time computable functions
[Cobham, *The intrinsic computational difficulty of functions*][Cobham1965],
as a model of computation on strings `List Symbol` over an arbitrary alphabet `Symbol`:
the smallest class of functions `(Fin n → List Symbol) → List Symbol` containing
the projections, the empty string, the symbol successors, and the smash functions,
and closed under composition and limited recursion on notation.

The algebra is presented as a syntax `Cobham Symbol n` of terms denoting `n`-ary string functions,
with semantics given by `Cobham.eval`.
Cobham's side condition on recursion — that the recursively defined
function be length-bounded by another function of the class — is not part of the syntax:
it is the structural predicate `Cobham.Limited`,
and `CobhamFP` collects the unary functions denoted by limited terms.

The functions are multi-arity (indexed by `Fin n` argument vectors) because limited
recursion on notation inherently produces functions of higher arity.

## Main definitions

- `Cslib.Cobham` — the terms of Cobham's function algebra over an alphabet `Symbol`
- `Cslib.Cobham.recNotation` — the recursion-on-notation combinator on string functions
- `Cslib.Cobham.eval` — the string function denoted by a term
- `Cslib.Cobham.Limited` — the side condition that every recursion in a term is bounded
  by its bounding term
- `Cslib.CobhamFP` — the unary string functions denoted by limited terms

## Design notes

We work over strings of arbitrary `Symbol` type, rather than binary natural numbers.

The bound in `Cobham.boundedRec` follows Cobham's original formulation: the recursively
defined function must be length-bounded by another function of the class
(rather than by an external polynomial).
Together with `smash` and the successors this realizes exactly the polynomial length bounds,
which is what makes the class no larger than the polynomial-time computable functions.

## TODO

* Prove the limited Cobham functions are exactly the polynomial-time computable functions.

## References

* [A. Cobham, *The intrinsic computational difficulty of functions*][Cobham1965]
-/

@[expose] public section

universe u

namespace Cslib

variable {Symbol : Type u}

/-- **Terms of Cobham's function algebra** over the alphabet `Symbol`. A term of type
`Cobham Symbol n` denotes an `n`-ary function on strings `List Symbol` (see
`Cobham.eval`): the projections, the empty string, the symbol successors `x ↦ a :: x`,
and the smash functions, closed under composition and recursion on notation.

In `boundedRec base step bound`, Cobham's side condition that the recursion be
length-bounded by `bound` is not enforced by the syntax; it is the predicate
`Cobham.Limited`. -/
inductive Cobham (Symbol : Type u) : ℕ → Type u
  /-- The `i`-th projection. -/
  | proj {n : ℕ} (i : Fin n) : Cobham Symbol n
  /-- The empty-string constant (at every arity). -/
  | empty {n : ℕ} : Cobham Symbol n
  /-- The successor `x ↦ a :: x` for the symbol `a`. -/
  | cons (a : Symbol) : Cobham Symbol 1
  /-- The smash function returning a list of `a` of length |x₀| * |x₁|. -/
  | smash (a : Symbol) : Cobham Symbol 2
  /-- Composition of an `m`-ary term with `m` terms of arity `n`. -/
  | comp {m n : ℕ} (f : Cobham Symbol m) (gs : Fin m → Cobham Symbol n) : Cobham Symbol n
  /-- Limited recursion on notation on the first argument, with the given base case, a
  step `step a` for each symbol `a`, and the given bounding term. -/
  | boundedRec {n : ℕ} (base : Cobham Symbol n) (step : Symbol → Cobham Symbol (n + 2))
      (bound : Cobham Symbol (n + 1)) : Cobham Symbol (n + 1)

namespace Cobham

/-- **Recursion on notation**: the string analogue of primitive recursion, recursing on
the symbol structure of the first argument.

`recNotation base step v x` computes `base v` when `x` is empty, and on `a :: x` applies the
step function `step a` selected by the symbol `a` to the argument vector consisting of the
tail `x`, the recursive value on the tail, and the parameters `v`. -/
def recNotation {n : ℕ} (base : (Fin n → List Symbol) → List Symbol)
    (step : Symbol → (Fin (n + 2) → List Symbol) → List Symbol) (v : Fin n → List Symbol) :
    List Symbol → List Symbol
  | [] => base v
  | a :: x => step a (Fin.cons x (Fin.cons (recNotation base step v x) v))

@[simp] theorem recNotation_nil {n : ℕ} (base : (Fin n → List Symbol) → List Symbol)
    (step : Symbol → (Fin (n + 2) → List Symbol) → List Symbol) (v : Fin n → List Symbol) :
    recNotation base step v [] = base v := rfl

@[simp] theorem recNotation_cons {n : ℕ} (base : (Fin n → List Symbol) → List Symbol)
    (step : Symbol → (Fin (n + 2) → List Symbol) → List Symbol) (v : Fin n → List Symbol)
    (a : Symbol) (x : List Symbol) :
    recNotation base step v (a :: x) =
      step a (Fin.cons x (Fin.cons (recNotation base step v x) v)) := rfl

/-- The string function denoted by a term. The bounding term of a `boundedRec` plays no
role in evaluation; it is checked by `Cobham.Limited`. -/
def eval {n : ℕ} (t : Cobham Symbol n) (v : Fin n → List Symbol) : List Symbol :=
  match t with
  | proj i => v i
  | empty => []
  | cons a => a :: v 0
  | smash a => List.replicate ((v 0).length * (v 1).length) a
  | comp f gs => f.eval fun i => (gs i).eval v
  | boundedRec base step _ =>
      recNotation base.eval (fun a => (step a).eval) (Fin.tail v) (v 0)

@[simp] theorem eval_proj {n : ℕ} (i : Fin n) (v : Fin n → List Symbol) :
    (proj i).eval v = v i := rfl

@[simp] theorem eval_empty {n : ℕ} (v : Fin n → List Symbol) :
    empty.eval v = [] := rfl

@[simp] theorem eval_cons (a : Symbol) (v : Fin 1 → List Symbol) :
    (cons a).eval v = a :: v 0 := rfl

@[simp] theorem eval_smash (a : Symbol) (v : Fin 2 → List Symbol) :
    (smash a).eval v = List.replicate ((v 0).length * (v 1).length) a := rfl

@[simp] theorem eval_comp {m n : ℕ} (f : Cobham Symbol m) (gs : Fin m → Cobham Symbol n)
    (v : Fin n → List Symbol) : (comp f gs).eval v = f.eval fun i => (gs i).eval v := rfl

@[simp] theorem eval_boundedRec {n : ℕ} (base : Cobham Symbol n)
    (step : Symbol → Cobham Symbol (n + 2)) (bound : Cobham Symbol (n + 1))
    (v : Fin (n + 1) → List Symbol) :
    (boundedRec base step bound).eval v =
      recNotation base.eval (fun a => (step a).eval) (Fin.tail v) (v 0) := rfl

/-- A term is **limited** when every recursion in it is limited in Cobham's sense: the
result of each `boundedRec base step bound` is length-bounded, uniformly in the arguments,
by `bound`. -/
def Limited {n : ℕ} : Cobham Symbol n → Prop
  | proj _ => True
  | empty => True
  | cons _ => True
  | smash _ => True
  | comp f gs => f.Limited ∧ ∀ i, (gs i).Limited
  | boundedRec base step bound =>
      base.Limited ∧ (∀ a, (step a).Limited) ∧ bound.Limited ∧
        ∀ v x, (recNotation base.eval (fun a => (step a).eval) v x).length ≤
          (bound.eval (Fin.cons x v)).length

@[simp] theorem limited_proj {n : ℕ} (i : Fin n) : (proj i : Cobham Symbol n).Limited := trivial

@[simp] theorem limited_empty {n : ℕ} : (empty : Cobham Symbol n).Limited := trivial

@[simp] theorem limited_cons (a : Symbol) : (cons a).Limited := trivial

@[simp] theorem limited_smash (a : Symbol) : (smash a).Limited := trivial

@[simp] theorem limited_comp {m n : ℕ} (f : Cobham Symbol m) (gs : Fin m → Cobham Symbol n) :
    (comp f gs).Limited ↔ f.Limited ∧ ∀ i, (gs i).Limited := Iff.rfl

@[simp] theorem limited_boundedRec {n : ℕ} (base : Cobham Symbol n)
    (step : Symbol → Cobham Symbol (n + 2)) (bound : Cobham Symbol (n + 1)) :
    (boundedRec base step bound).Limited ↔
      base.Limited ∧ (∀ a, (step a).Limited) ∧ bound.Limited ∧
        ∀ v x, (recNotation base.eval (fun a => (step a).eval) v x).length ≤
          (bound.eval (Fin.cons x v)).length := Iff.rfl

end Cobham

/-- The unary fragment of Cobham's function algebra over `Symbol`: the string functions
denoted by limited unary terms. By Cobham's theorem [Cobham1965], this machine-independent
class is exactly the polynomial-time computable functions. -/
def CobhamFP (Symbol : Type u) : Set (List Symbol → List Symbol) :=
  {f | ∃ c : Cobham Symbol 1, c.Limited ∧ ∀ x, c.eval (fun _ => x) = f x}

end Cslib
