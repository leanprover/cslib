/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sum

/-! # QueryTree: Decision Trees for Query Complexity Lower Bounds

`QueryTree Q R α` is a free monad specialized to a single query type: queries take
input `Q` and return `R`, with final results of type `α`. It reifies a monad-generic
algorithm's query pattern as an explicit decision tree.

## Motivation

The upper-bound framework (`UpperBound`) uses parametricity: a monad-generic algorithm
is specialized to `TimeM` (tick-counting monad) to count queries. This doesn't work
for lower bounds because a noncomputable algorithm could detect `TimeM` and cheat
(e.g., `if h : m = TimeM then <reset ticks> else ...`).

Instead, we specialize the algorithm to `QueryTree Q R`, which *is* the decision tree.
The tree structure directly records every query the algorithm makes, regardless of whether
the algorithm is computable. Combinatorial arguments on the tree (leaf counting, depth
bounds) then yield lower bounds.

## Design

`QueryTree Q R` is isomorphic to `FreeM (fun _ => Q)` restricted to operations returning `R`,
but is defined as a dedicated inductive to avoid universe issues with `FreeM`'s existential
`ι` parameter (which would require producing values of arbitrary types during evaluation).

Note that the graph-theoretic depth of the tree can be strictly larger than
`sup_oracle queriesOn oracle`, because the same query may appear at the root and inside a
subtree, and a single oracle must give consistent answers.

## OracleQueryTree

`OracleQueryTree Q R oracle` is a type alias for `QueryTree Q R` that bakes a fixed oracle
into the type. This allows a `WPMonad` instance where `wp t = pure (t.eval oracle)`,
connecting `QueryTree` evaluation to the Hoare-triple framework used by `IsMonadicSort`.

## Main Definitions

- `QueryTree Q R α` — the decision tree type
- `QueryTree.ask` — the canonical single-query tree
- `QueryTree.eval` — evaluate with a specific oracle
- `QueryTree.queriesOn` — count queries along an oracle-determined path
- `OracleQueryTree Q R oracle` — type alias with `WPMonad` instance
-/

open Std.Do Cslib.Query

public section

namespace Cslib.Query

/-- A decision tree over queries of type `Q → R`, with results of type `α`.

This is the free monad specialized to a single fixed-type operation, used to reify
monad-generic algorithms as explicit trees for query complexity lower bounds. -/
inductive QueryTree (Q : Type) (R : Type) (α : Type) where
  /-- A completed computation returning value `a`. -/
  | pure (a : α) : QueryTree Q R α
  /-- A query node: asks query `q`, then continues based on the response. -/
  | query (q : Q) (cont : R → QueryTree Q R α) : QueryTree Q R α

namespace QueryTree

variable {Q R α β γ : Type}

/-- Lift a single query into the tree. -/
@[expose] def ask (q : Q) : QueryTree Q R R := .query q .pure

/-- Monadic bind for query trees. -/
@[expose] protected def bind : QueryTree Q R α → (α → QueryTree Q R β) → QueryTree Q R β
  | .pure a, f => f a
  | .query q cont, f => .query q (fun r => (cont r).bind f)

/-- Functorial map for query trees. -/
@[expose] protected def map (f : α → β) : QueryTree Q R α → QueryTree Q R β
  | .pure a => .pure (f a)
  | .query q cont => .query q (fun r => (cont r).map f)

protected theorem bind_pure : ∀ (x : QueryTree Q R α), x.bind .pure = x
  | .pure _ => rfl
  | .query _ cont => by simp [QueryTree.bind, QueryTree.bind_pure]

protected theorem bind_assoc :
    ∀ (x : QueryTree Q R α) (f : α → QueryTree Q R β) (g : β → QueryTree Q R γ),
      (x.bind f).bind g = x.bind (fun a => (f a).bind g)
  | .pure _, _, _ => rfl
  | .query _ cont, f, g => by simp [QueryTree.bind, QueryTree.bind_assoc]

protected theorem bind_pure_comp (f : α → β) :
    ∀ (x : QueryTree Q R α), x.bind (.pure ∘ f) = x.map f
  | .pure _ => rfl
  | .query _ cont => by simp [QueryTree.bind, QueryTree.map, QueryTree.bind_pure_comp]

protected theorem id_map : ∀ (x : QueryTree Q R α), x.map id = x
  | .pure _ => rfl
  | .query _ cont => by simp [QueryTree.map, QueryTree.id_map]

instance : Monad (QueryTree Q R) where
  pure := .pure
  bind := .bind

instance : LawfulMonad (QueryTree Q R) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := QueryTree.bind_pure)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := QueryTree.bind_assoc)

-- Core operations

/-- Evaluate a query tree with a specific oracle, returning the final result. -/
@[expose] def eval (oracle : Q → R) : QueryTree Q R α → α
  | .pure a => a
  | .query q cont => eval oracle (cont (oracle q))

/-- Count the number of queries along the path determined by `oracle`. -/
@[expose] def queriesOn (oracle : Q → R) : QueryTree Q R α → Nat
  | .pure _ => 0
  | .query q cont => 1 + queriesOn oracle (cont (oracle q))

-- Simp lemmas

@[simp] theorem eval_pure' (oracle : Q → R) (a : α) :
    (QueryTree.pure a : QueryTree Q R α).eval oracle = a := rfl

@[simp] theorem eval_query (oracle : Q → R) (q : Q) (cont : R → QueryTree Q R α) :
    (QueryTree.query q cont).eval oracle = (cont (oracle q)).eval oracle := rfl

@[simp] theorem eval_bind (oracle : Q → R) (t : QueryTree Q R α) (f : α → QueryTree Q R β) :
    (t.bind f).eval oracle = (f (t.eval oracle)).eval oracle := by
  induction t with
  | pure a => rfl
  | query q cont ih => exact ih (oracle q)

@[simp] theorem queriesOn_pure' (oracle : Q → R) (a : α) :
    (QueryTree.pure a : QueryTree Q R α).queriesOn oracle = 0 := rfl

@[simp] theorem queriesOn_query (oracle : Q → R) (q : Q) (cont : R → QueryTree Q R α) :
    (QueryTree.query q cont).queriesOn oracle = 1 + (cont (oracle q)).queriesOn oracle := rfl

/-- Queries of `t.bind f` = queries of `t` + queries of the continuation. -/
@[simp] theorem queriesOn_bind (oracle : Q → R) (t : QueryTree Q R α) (f : α → QueryTree Q R β) :
    (t.bind f).queriesOn oracle =
      t.queriesOn oracle + (f (t.eval oracle)).queriesOn oracle := by
  induction t with
  | pure a => simp [QueryTree.bind, queriesOn, eval]
  | query q cont ih => simp only [QueryTree.bind, queriesOn_query, eval_query, ih (oracle q)]; omega

@[simp] theorem queriesOn_ask (oracle : Q → R) (q : Q) :
    (ask q : QueryTree Q R R).queriesOn oracle = 1 := rfl

@[simp] theorem eval_ask (oracle : Q → R) (q : Q) :
    (ask q : QueryTree Q R R).eval oracle = oracle q := rfl


end QueryTree

-- ## OracleQueryTree: WPMonad instance for QueryTree with a fixed oracle

/-- `OracleQueryTree Q R oracle` is `QueryTree Q R` with a fixed oracle baked into the type,
    enabling a `WPMonad` instance where `wp t = pure (t.eval oracle)`. -/
@[nolint unusedArguments]
abbrev OracleQueryTree (Q R : Type) (_oracle : Q → R) := QueryTree Q R

namespace OracleQueryTree

variable {Q R : Type} {oracle : Q → R}

instance instWP : WP (OracleQueryTree Q R oracle) .pure where
  wp t := pure (t.eval oracle)

instance instWPMonad : WPMonad (OracleQueryTree Q R oracle) .pure where
  wp_pure a := by simp [wp, QueryTree.eval]
  wp_bind x f := by
    simp only [wp]
    congr 1
    exact QueryTree.eval_bind oracle x f

@[simp] theorem wp_eq (t : OracleQueryTree Q R oracle α) :
    instWP.wp t = pure (t.eval oracle) := rfl

end OracleQueryTree

end Cslib.Query

end -- public section
