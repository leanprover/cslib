/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai, Eric Wieser
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.Defs


@[expose] public section

/-!

# TimeM: Time Complexity Monad
`TimeM T α` represents a computation that produces a value of type `α` and tracks its time cost.

`T` is usually instantiated as `ℕ` to count operations, but can be instantiated as `ℝ` to count
actual wall time, or as more complex types in order to model more general costs.

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
`TimeM T α` represents a computation that returns a value of type `α`
and accumulates a time cost (represented as a type `T`, typically `ℕ`). -/
@[ext]
structure TimeM (T : Type*) (α : Type*) where
  /-- The return value of the computation -/
  ret : α
  /-- The accumulated time cost of the computation -/
  time : T

namespace TimeM

/-- Lifts a pure value into a `TimeM` computation with zero time cost.

Prefer to use `pure` instead of `TimeM.pure`. -/
protected def pure [Zero T] {α} (a : α) : TimeM T α :=
  ⟨a, 0⟩

instance [Zero T] : Pure (TimeM T) where
  pure := TimeM.pure

/-- Sequentially composes two `TimeM` computations, summing their time costs.

Prefer to use the `>>=` notation. -/
protected def bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) : TimeM T β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance [Add T] : Bind (TimeM T) where
  bind := TimeM.bind

instance : Functor (TimeM T) where
  map f x := ⟨f x.ret, x.time⟩

instance [Add T] : Seq (TimeM T) where
  seq f x := ⟨f.ret (x ()).ret, f.time + (x ()).time⟩

instance [Add T] : SeqLeft (TimeM T) where
  seqLeft x y := ⟨x.ret, x.time + (y ()).time⟩

instance [Add T] : SeqRight (TimeM T) where
  seqRight x y := ⟨(y ()).ret, x.time + (y ()).time⟩

instance [AddZero T] : Monad (TimeM T) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight

@[simp, grind =] theorem ret_pure {α} [Zero T] (a : α) : (pure a : TimeM T α).ret = a := rfl
@[simp, grind =] theorem ret_bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) :
    (m >>= f).ret = (f m.ret).ret := rfl
@[simp, grind =] theorem ret_map {α β} (f : α → β) (x : TimeM T α) : (f <$> x).ret = f x.ret := rfl
@[simp] theorem ret_seqRight {α} (x : TimeM T α) (y : Unit → TimeM T β) [Add T] :
    (SeqRight.seqRight x y).ret = (y ()).ret := rfl
@[simp] theorem ret_seqLeft {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqLeft.seqLeft x y).ret = x.ret := rfl
@[simp] theorem ret_seq {α β} [Add T] (f : TimeM T (α → β)) (x : Unit → TimeM T α) :
    (Seq.seq f x).ret = f.ret (x ()).ret := rfl

@[simp, grind =] theorem time_bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) :
    (m >>= f).time = m.time + (f m.ret).time := rfl
@[simp, grind =] theorem time_pure {α} [Zero T] (a : α) : (pure a : TimeM T α).time = 0 := rfl
@[simp, grind =] theorem time_map {α β} (f : α → β) (x : TimeM T α) : (f <$> x).time = x.time := rfl
@[simp] theorem time_seqRight {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqRight.seqRight x y).time = x.time + (y ()).time := rfl
@[simp] theorem time_seqLeft {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqLeft.seqLeft x y).time = x.time + (y ()).time := rfl
@[simp] theorem time_seq {α β} [Add T] (f : TimeM T (α → β)) (x : Unit → TimeM T α) :
    (Seq.seq f x).time = f.time + (x ()).time := rfl

/-- `TimeM` is lawful so long as addition in the cost is associative and absorbs zero. -/
instance [AddMonoid T] : LawfulMonad (TimeM T) := .mk'
  (id_map := fun x => rfl)
  (pure_bind := fun _ _ => by ext <;> simp)
  (bind_assoc := fun _ _ _ => by ext <;> simp [add_assoc])
  (seqLeft_eq := fun _ _ => by ext <;> simp)
  (bind_pure_comp := fun _ _ => by ext <;> simp)

/-- Creates a `TimeM` computation with a time cost. -/
def tick (c : T) : TimeM T PUnit := ⟨.unit, c⟩

@[simp, grind =] theorem ret_tick (c : T) : (tick c).ret = () := rfl
@[simp, grind =] theorem time_tick (c : T) : (tick c).time = c := rfl

/-- `✓[c] x` adds `c` ticks, then executes `x`. -/
macro "✓[" c:term "]" body:doElem : doElem => `(doElem| do TimeM.tick $c; $body:doElem)

/-- `✓ x` is a shorthand for `✓[1] x`, which adds one tick and executes `x`. -/
macro "✓" body:doElem : doElem => `(doElem| ✓[1] $body)

/-- Notation for extracting the return value from a `TimeM` computation: `⟪tm⟫` -/
scoped notation:max "⟪" tm "⟫" => (TimeM.ret tm)

end TimeM
end Cslib.Algorithms.Lean
