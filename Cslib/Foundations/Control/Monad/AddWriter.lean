/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai, Eric Wieser
-/

module

public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Mathlib.Algebra.Group.Defs

/-!

# AddWriter: Additive Writer Monad
`AddWriter T α` represents a computation that produces a value of type `α` and tracks its cost.

`T` can be instantiated with AddCommMonoid types to count costs in types of varying complexity.

## Notation
- **`✓`** : A call to tell, see `tell`.
- **`⟪tm⟫`** : Extract the pure value from an `AddWriter` computation (notation for `tm.ret`).

## Notes on Authorship and Terminology
This file was authored by Sorrachai Yingchareonthawornchai in the CSLib repository.
It was named the Time monad `TimeM`. The standard name for this concept is the Writer Monad.
Since Lean/Mathlib makes a distinction between additive and multiplicative algebraic structures,
and Mathlib already contains a Writer monad, we call this structure `AddWriter`.

## References
1. [Elementary explanation of writer monads](https://williamyaoh.com/posts/2020-07-26-deriving-writer-monad.html)
2. [Danielsson2008] on lightweight monadic verification of time complexity.
-/


@[expose] public section

namespace Cslib

/-- A monad for tracking log complexity of computations.
`AddWriter T α` represents a computation that returns a value of type `α`
and accumulates a log cost (represented as a type `T`, typically `ℕ`). -/
@[ext]
structure AddWriter (w : Type*) (α : Type*) where
  /-- The return value of the computation -/
  ret : α
  /-- The accumulated tell cost of the computation -/
  tell : w

namespace AddWriter

/-- Lifts a pure value into a `AddWriter` computation with zero tell cost.

Prefer to use `pure` instead of `AddWriter.pure`. -/
protected def pure [Zero T] {α} (a : α) : AddWriter T α :=
  ⟨a, 0⟩

instance [Zero T] : Pure (AddWriter T) where
  pure := AddWriter.pure

/-- Sequentially composes two `AddWriter` computations, summing their log costs.

Prefer to use the `>>=` notation. -/
protected def bind {α β} [Add T] (m : AddWriter T α) (f : α → AddWriter T β) : AddWriter T β :=
  let r := f m.ret
  ⟨r.ret, m.tell + r.tell⟩

instance [Add T] : Bind (AddWriter T) where
  bind := AddWriter.bind

instance : Functor (AddWriter T) where
  map f x := ⟨f x.ret, x.tell⟩

instance [Add T] : Seq (AddWriter T) where
  seq f x := ⟨f.ret (x ()).ret, f.tell + (x ()).tell⟩

instance [Add T] : SeqLeft (AddWriter T) where
  seqLeft x y := ⟨x.ret, x.tell + (y ()).tell⟩

instance [Add T] : SeqRight (AddWriter T) where
  seqRight x y := ⟨(y ()).ret, x.tell + (y ()).tell⟩

instance [AddZero T] : Monad (AddWriter T) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight

@[simp, grind =] theorem ret_pure {α} [Zero T] (a : α) : (pure a : AddWriter T α).ret = a := rfl

@[simp, grind =] theorem ret_bind {α β} [Add T] (m : AddWriter T α) (f : α → AddWriter T β) :
    (m >>= f).ret = (f m.ret).ret := rfl

@[simp, grind =] theorem ret_map {α β} (f : α → β) (x : AddWriter T α) : (f <$> x).ret = f x.ret :=
  rfl

@[simp] theorem ret_seqRight {α} (x : AddWriter T α) (y : Unit → AddWriter T β) [Add T] :
    (SeqRight.seqRight x y).ret = (y ()).ret := rfl

@[simp] theorem ret_seqLeft {α} [Add T] (x : AddWriter T α) (y : Unit → AddWriter T β) :
    (SeqLeft.seqLeft x y).ret = x.ret := rfl

@[simp] theorem ret_seq {α β} [Add T] (f : AddWriter T (α → β)) (x : Unit → AddWriter T α) :
    (Seq.seq f x).ret = f.ret (x ()).ret := rfl

/-- Extracting the return value preserves monadic operations. -/
theorem isMonadHom_pure_ret [AddZero T] : IsMonadHom (AddWriter T) Id (fun x => pure x.ret) where
  map_map _ _ := rfl
  map_mapConst _ _ := rfl
  map_pure _ := rfl
  map_seq _ _ := rfl
  map_seqLeft _ _ := rfl
  map_seqRight _ _ := rfl
  map_bind _ _ := rfl

@[simp, grind =] theorem tell_bind {α β} [Add T] (m : AddWriter T α) (f : α → AddWriter T β) :
    (m >>= f).tell = m.tell + (f m.ret).tell := rfl

@[simp, grind =] theorem tell_pure {α} [Zero T] (a : α) : (pure a : AddWriter T α).tell = 0 := rfl

@[simp, grind =] theorem tell_map {α β} (f : α → β) (x : AddWriter T α) : (f <$> x).tell = x.tell :=
  rfl
@[simp] theorem tell_seqRight {α} [Add T] (x : AddWriter T α) (y : Unit → AddWriter T β) :
    (SeqRight.seqRight x y).tell = x.tell + (y ()).tell := rfl

@[simp] theorem tell_seqLeft {α} [Add T] (x : AddWriter T α) (y : Unit → AddWriter T β) :
    (SeqLeft.seqLeft x y).tell = x.tell + (y ()).tell := rfl

@[simp] theorem tell_seq {α β} [Add T] (f : AddWriter T (α → β)) (x : Unit → AddWriter T α) :
    (Seq.seq f x).tell = f.tell + (x ()).tell := rfl

/-- `AddWriter` is lawful so long as addition in the cost is associative and absorbs zero. -/
instance [AddMonoid T] : LawfulMonad (AddWriter T) := .mk'
  (id_map := fun x => rfl)
  (pure_bind := fun _ _ => by ext <;> simp)
  (bind_assoc := fun _ _ _ => by ext <;> simp [add_assoc])
  (seqLeft_eq := fun _ _ => by ext <;> simp)
  (bind_pure_comp := fun _ _ => by ext <;> simp)

end AddWriter
end Cslib
