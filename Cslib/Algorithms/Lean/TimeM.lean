/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
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
structure TimeM (α : Type*) where
  /-- The return value of the computation -/
  ret : α
  /-- The accumulated time cost of the computation -/
  time : ℕ

namespace TimeM

/-- Lifts a pure value into a `TimeM` computation with zero time cost. -/
@[scoped grind =]
def pure {α} (a : α) : TimeM α :=
  ⟨a, 0⟩

/-- Sequentially composes two `TimeM` computations, summing their time costs. -/
@[scoped grind =]
def bind {α β} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance : Monad TimeM where
  pure := pure
  bind := bind

/-- Creates a `TimeM` computation with a specified value and time cost.
The time cost defaults to 1 if not provided. -/
@[simp, grind =] def tick {α : Type*} (a : α) (c : ℕ := 1) : TimeM α := ⟨a, c⟩

/-- Notation for `tick` with explicit time cost: `✓ a, c` -/
scoped notation "✓" a:arg ", " c:arg => tick a c

/-- Notation for `tick` with default time cost of 1: `✓ a` -/
scoped notation "✓" a:arg => tick a

/-- Notation for extracting the return value from a `TimeM` computation: `⟪tm⟫` -/
scoped notation:max "⟪" tm "⟫" => (TimeM.ret tm)

/-- A unit computation with time cost 1. -/
def tickUnit : TimeM Unit :=
  ✓ ()

@[simp] theorem time_of_pure {α} (a : α) : (pure a).time = 0 := rfl

@[simp] theorem time_of_bind {α β} (m : TimeM α) (f : α → TimeM β) :
 (TimeM.bind m f).time = m.time + (f m.ret).time := rfl

@[simp] theorem time_of_tick {α} (a : α) (c : ℕ) : (tick a c).time = c := rfl

@[simp] theorem ret_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (TimeM.bind m f).ret = (f m.ret).ret := rfl

-- this allow us to simplify the chain of monadic compositions
attribute [simp] Bind.bind Pure.pure TimeM.pure TimeM.bind

end TimeM
end Cslib.Algorithms.Lean
