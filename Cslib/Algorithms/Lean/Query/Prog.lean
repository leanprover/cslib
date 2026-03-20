/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Graf, Shreyas Srinivas
-/
module

public import Cslib.Foundations.Control.Monad.Free

/-! # Prog: Programs as Free Monads over Query Types

`Prog Q α` is an alias for `FreeM Q α`, representing a program that makes queries of type `Q`
and returns a result of type `α`. A query type `Q : Type → Type` maps each query to its
response type.

The key operations are:
- `Prog.eval oracle p`: evaluate `p` by answering each query using `oracle`
- `Prog.queriesOn oracle p`: count the queries along the oracle-determined path

Because the oracle is supplied *after* the program produces its query plan (the `Prog` tree),
a sound implementation of `prog` has no way to "guess" what the oracle would respond.
This is the foundation of the anti-cheating guarantee for both upper and lower bounds.

This provides an alternative to the `TimeM`-based cost analysis in
`Cslib.Algorithms.Lean.MergeSort`: here query counting is structural (derived from the
`Prog` tree) rather than annotation-based.
-/

open Cslib

public section

namespace Cslib.Query

/-- A program that makes queries of type `Q` and returns a result of type `α`.
    This is `FreeM Q α`, the free monad over the query type. -/
abbrev Prog (Q : Type → Type) (α : Type) := FreeM Q α

namespace Prog

variable {Q : Type → Type} {α β : Type}

/-- Evaluate a program by answering each query using `oracle`. -/
@[expose] def eval (oracle : {ι : Type} → Q ι → ι) : Prog Q α → α
  | .pure a => a
  | .liftBind op cont => eval oracle (cont (oracle op))

/-- Count the number of queries along the path determined by `oracle`. -/
@[expose] def queriesOn (oracle : {ι : Type} → Q ι → ι) : Prog Q α → Nat
  | .pure _ => 0
  | .liftBind op cont => 1 + queriesOn oracle (cont (oracle op))

-- Simp lemmas for eval

@[simp] theorem eval_pure (oracle : {ι : Type} → Q ι → ι) (a : α) :
    eval oracle (.pure a : Prog Q α) = a := rfl

@[simp] theorem eval_liftBind (oracle : {ι : Type} → Q ι → ι)
    {ι : Type} (op : Q ι) (cont : ι → Prog Q α) :
    eval oracle (.liftBind op cont) = eval oracle (cont (oracle op)) := rfl

@[simp] theorem eval_bind (oracle : {ι : Type} → Q ι → ι)
    (t : Prog Q α) (f : α → Prog Q β) :
    eval oracle (t.bind f) = eval oracle (f (eval oracle t)) := by
  induction t with
  | pure a => rfl
  | liftBind op cont ih => exact ih (oracle op)

-- Simp lemmas for queriesOn

@[simp] theorem queriesOn_pure (oracle : {ι : Type} → Q ι → ι) (a : α) :
    queriesOn oracle (.pure a : Prog Q α) = 0 := rfl

@[simp] theorem queriesOn_liftBind (oracle : {ι : Type} → Q ι → ι)
    {ι : Type} (op : Q ι) (cont : ι → Prog Q α) :
    queriesOn oracle (.liftBind op cont) = 1 + queriesOn oracle (cont (oracle op)) := rfl

@[simp] theorem queriesOn_bind (oracle : {ι : Type} → Q ι → ι)
    (t : Prog Q α) (f : α → Prog Q β) :
    queriesOn oracle (t.bind f) =
      queriesOn oracle t + queriesOn oracle (f (eval oracle t)) := by
  induction t with
  | pure a => simp [FreeM.bind]
  | liftBind op cont ih =>
    simp only [FreeM.bind, queriesOn_liftBind, eval_liftBind, ih (oracle op)]
    omega

/-- Weighted query cost: each query has a cost given by `weight`. -/
@[expose] def cost (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → Nat) : Prog Q α → Nat
  | .pure _ => 0
  | .liftBind op cont => weight op + cost oracle weight (cont (oracle op))

-- Simp lemmas for cost

@[simp] theorem cost_pure (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → Nat) (a : α) :
    cost oracle weight (.pure a : Prog Q α) = 0 := rfl

@[simp] theorem cost_liftBind (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → Nat) {ι : Type} (op : Q ι) (cont : ι → Prog Q α) :
    cost oracle weight (.liftBind op cont) =
      weight op + cost oracle weight (cont (oracle op)) := rfl

@[simp] theorem cost_bind (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → Nat) (t : Prog Q α) (f : α → Prog Q β) :
    cost oracle weight (t.bind f) =
      cost oracle weight t + cost oracle weight (f (eval oracle t)) := by
  induction t with
  | pure a => simp [FreeM.bind]
  | liftBind op cont ih =>
    simp only [FreeM.bind, cost_liftBind, eval_liftBind, ih (oracle op)]
    omega

theorem queriesOn_eq_cost_one (oracle : {ι : Type} → Q ι → ι) (p : Prog Q α) :
    queriesOn oracle p = cost oracle (fun _ => 1) p := by
  induction p with
  | pure a => rfl
  | liftBind op cont ih => simp [ih (oracle op)]

end Prog

end Cslib.Query

end -- public section
