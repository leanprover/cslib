/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Kim Morrison, Shreyas Srinivas
-/
module

public import Cslib.Foundations.Control.Monad.Free

/-! # FreeM: query/cost interpreters

This file adds query-complexity interpreters to `FreeM F α`, where the type constructor
`F : Type → Type` represents a query type mapping each query to its response type.

The key operations are:
- `FreeM.eval oracle p`: evaluate `p` by answering each query using `oracle`
- `FreeM.queriesOn oracle p`: count queries along the oracle-determined path
- `FreeM.cost oracle weight p`: weighted query cost

Because the oracle is supplied *after* the program produces its query plan (the `FreeM` tree),
a sound implementation has no way to "guess" what the oracle would respond. This is the
foundation of the anti-cheating guarantee for both upper and lower bounds.

This provides an alternative to the `TimeM`-based cost analysis in
`Cslib.Algorithms.Lean.MergeSort`: here query counting is structural (derived from the
`FreeM` tree) rather than annotation-based.
-/

public section

namespace Cslib.FreeM

variable {F : Type → Type} {α β : Type}

/-- Evaluate a program by answering each query using `oracle`. -/
@[expose] def eval (oracle : {ι : Type} → F ι → ι) : FreeM F α → α
  | .pure a => a
  | .liftBind op cont => eval oracle (cont (oracle op))

/-- Count the number of queries along the path determined by `oracle`. -/
@[expose] def queriesOn (oracle : {ι : Type} → F ι → ι) : FreeM F α → Nat
  | .pure _ => 0
  | .liftBind op cont => 1 + queriesOn oracle (cont (oracle op))

-- Simp lemmas for eval

@[simp] theorem eval_pure (oracle : {ι : Type} → F ι → ι) (a : α) :
    eval oracle (.pure a : FreeM F α) = a := rfl

@[simp] theorem eval_liftBind (oracle : {ι : Type} → F ι → ι)
    {ι : Type} (op : F ι) (cont : ι → FreeM F α) :
    eval oracle (.liftBind op cont) = eval oracle (cont (oracle op)) := rfl

@[simp] theorem eval_bind (oracle : {ι : Type} → F ι → ι)
    (t : FreeM F α) (f : α → FreeM F β) :
    eval oracle (t.bind f) = eval oracle (f (eval oracle t)) := by
  induction t with
  | pure a => rfl
  | liftBind op cont ih => exact ih (oracle op)

-- Simp lemmas for queriesOn

@[simp] theorem queriesOn_pure (oracle : {ι : Type} → F ι → ι) (a : α) :
    queriesOn oracle (.pure a : FreeM F α) = 0 := rfl

@[simp] theorem queriesOn_liftBind (oracle : {ι : Type} → F ι → ι)
    {ι : Type} (op : F ι) (cont : ι → FreeM F α) :
    queriesOn oracle (.liftBind op cont) = 1 + queriesOn oracle (cont (oracle op)) := rfl

@[simp] theorem queriesOn_bind (oracle : {ι : Type} → F ι → ι)
    (t : FreeM F α) (f : α → FreeM F β) :
    queriesOn oracle (t.bind f) =
      queriesOn oracle t + queriesOn oracle (f (eval oracle t)) := by
  induction t with
  | pure a => simp [FreeM.bind]
  | liftBind op cont ih =>
    simp only [FreeM.bind, queriesOn_liftBind, eval_liftBind, ih (oracle op)]
    omega

/-- Weighted query cost: each query has a cost given by `weight`. -/
@[expose] def cost (oracle : {ι : Type} → F ι → ι)
    (weight : {ι : Type} → F ι → Nat) : FreeM F α → Nat
  | .pure _ => 0
  | .liftBind op cont => weight op + cost oracle weight (cont (oracle op))

-- Simp lemmas for cost

@[simp] theorem cost_pure (oracle : {ι : Type} → F ι → ι)
    (weight : {ι : Type} → F ι → Nat) (a : α) :
    cost oracle weight (.pure a : FreeM F α) = 0 := rfl

@[simp] theorem cost_liftBind (oracle : {ι : Type} → F ι → ι)
    (weight : {ι : Type} → F ι → Nat) {ι : Type} (op : F ι) (cont : ι → FreeM F α) :
    cost oracle weight (.liftBind op cont) =
      weight op + cost oracle weight (cont (oracle op)) := rfl

@[simp] theorem cost_bind (oracle : {ι : Type} → F ι → ι)
    (weight : {ι : Type} → F ι → Nat) (t : FreeM F α) (f : α → FreeM F β) :
    cost oracle weight (t.bind f) =
      cost oracle weight t + cost oracle weight (f (eval oracle t)) := by
  induction t with
  | pure a => simp [FreeM.bind]
  | liftBind op cont ih =>
    simp only [FreeM.bind, cost_liftBind, eval_liftBind, ih (oracle op)]
    omega

theorem queriesOn_eq_cost_one (oracle : {ι : Type} → F ι → ι) (p : FreeM F α) :
    queriesOn oracle p = cost oracle (fun _ => 1) p := by
  induction p with
  | pure a => rfl
  | liftBind op cont ih => simp [ih (oracle op)]

end Cslib.FreeM

end -- public section
