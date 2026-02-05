/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai, Eric Wieser
-/

module

import Cslib.Init

@[expose] public section

/-!

# TimeM: Time Complexity Monad
`TimeM α` represents a computation that produces a value of type `α` and tracks its time cost.

## Design Principles
1. **Pure inputs, timed outputs**: Functions take plain values and return `TimeM` results
2. **Time annotations are trusted**: The `time` field is NOT verified against actual cost.
   You must manually ensure annotations match the algorithm's complexity in your cost model.
3. **Separation of concerns**: Prove correctness properties on `.ret`, prove complexity on `.time`

## Cost Model
**Document your cost model explicitly** Decide and be consistent about:
- **What costs 1 unit?** (comparison, arithmetic operation, etc.)
- **What is free?** (variable lookup, pattern matching, etc.)
- **Recursive calls:** Do you charge for the call itself?

## Notation
- **`✓`** : A tick of time, see `tick`.
- **`⟪tm⟫`** : Extract the pure value from a `TimeM` computation (notation for `tm.ret`)

## References

See [Danielsson2008] for the discussion.
-/
namespace Cslib.Algorithms.Lean

/-- A monad for tracking time complexity of computations.
`TimeM α` represents a computation that returns a value of type `α`
and accumulates a time cost (represented as a natural number). -/
@[ext]
structure TimeM (α : Type*) where
  /-- The return value of the computation -/
  ret : α
  /-- The accumulated time cost of the computation -/
  time : ℕ

namespace TimeM

/-- Lifts a pure value into a `TimeM` computation with zero time cost.

Prefer to use `pure` instead of `TimeM.pure`. -/
protected def pure {α} (a : α) : TimeM α :=
  ⟨a, 0⟩

/-- Sequentially composes two `TimeM` computations, summing their time costs.

Prefer to use the `>>=` notation. -/
protected def bind {α β} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance : Monad TimeM where
  pure := TimeM.pure
  bind := TimeM.bind

@[simp, grind =] theorem ret_pure {α} (a : α) : (pure a : TimeM α).ret = a := rfl
@[simp, grind =] theorem ret_bind {α β} (m : TimeM α) (f : α → TimeM β) :
    (m >>= f).ret = (f m.ret).ret := rfl
@[simp, grind =] theorem ret_map {α β} (f : α → β) (x : TimeM α) : (f <$> x).ret = f x.ret := rfl
@[simp] theorem ret_seqRight {α} (x y : TimeM α) : (x *> y).ret = y.ret := rfl
@[simp] theorem ret_seqLeft {α} (x y : TimeM α) : (x <* y).ret = x.ret := rfl
@[simp] theorem ret_seq {α β} (f : TimeM (α → β)) (x : TimeM α) : (f <*> x).ret = f.ret x.ret := rfl

@[simp, grind =] theorem time_bind {α β} (m : TimeM α) (f : α → TimeM β) :
    (m >>= f).time = m.time + (f m.ret).time := rfl
@[simp, grind =] theorem time_pure {α} (a : α) : (pure a : TimeM α).time = 0 := rfl
@[simp, grind =] theorem time_map {α β} (f : α → β) (x : TimeM α) : (f <$> x).time = x.time := rfl
@[simp] theorem time_seqRight {α} (x y : TimeM α) : (x *> y).time = x.time + y.time := rfl
@[simp] theorem time_seqLeft {α} (x y : TimeM α) : (x <* y).time = x.time + y.time := rfl
@[simp] theorem time_seq {α β} (f : TimeM (α → β)) (x : TimeM α) :
    (f <*> x).time = f.time + x.time := rfl


instance : LawfulMonad TimeM := .mk'
  (id_map := fun x => rfl)
  (pure_bind := fun _ _ => by ext <;> simp)
  (bind_assoc := fun _ _ _ => by ext <;> simp [Nat.add_assoc])

/-- Creates a `TimeM` computation with a time cost.
The time cost defaults to 1 if not provided. -/
def tick (c : ℕ := 1) : TimeM PUnit := ⟨.unit, c⟩

@[simp, grind =] theorem ret_tick (c : ℕ) : (tick c).ret = () := rfl
@[simp, grind =] theorem time_tick (c : ℕ) : (tick c).time = c := rfl

/-- `✓[c] x` adds `c` ticks, then executes `x`. -/
macro "✓[" c:term "]" body:doElem : doElem => `(doElem| do TimeM.tick $c; $body:doElem)

/-- `✓ x` is a shorthand for `✓[1] x`, which adds one tick and executes `x`. -/
macro "✓" body:doElem : doElem => `(doElem| ✓[1] $body)

/-- Notation for extracting the return value from a `TimeM` computation: `⟪tm⟫` -/
scoped notation:max "⟪" tm "⟫" => (TimeM.ret tm)

end TimeM
end Cslib.Algorithms.Lean
