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
`AddWriter w α` represents a writer monad computation that
produces a value of type `α` and tracks its log of type `w`.

## References
1. [Monads for Functional Programming, Philip Wadler][wadler1995monads]
2. [Root-Balanced Tree, Isabelle Archive of Formal Proofs, Nipkow 2018][Nipkow2018]
-/


@[expose] public section

namespace Cslib

/-- A monad for tracking log complexity of computations.
`AddWriter w α` represents a computation that returns a value of type `α`
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
protected def pure [Zero w] {α} (a : α) : AddWriter w α :=
  ⟨a, 0⟩

instance [Zero w] : Pure (AddWriter w) where
  pure := AddWriter.pure

/-- Sequentially composes two `AddWriter` computations, summing their log costs.

Prefer to use the `>>=` notation. -/
protected def bind {α β} [Add w] (m : AddWriter w α) (f : α → AddWriter w β) : AddWriter w β :=
  let r := f m.ret
  ⟨r.ret, m.tell + r.tell⟩

instance [Add w] : Bind (AddWriter w) where
  bind := AddWriter.bind

instance : Functor (AddWriter w) where
  map f x := ⟨f x.ret, x.tell⟩

instance [Add w] : Seq (AddWriter w) where
  seq f x := ⟨f.ret (x ()).ret, f.tell + (x ()).tell⟩

instance [Add w] : SeqLeft (AddWriter w) where
  seqLeft x y := ⟨x.ret, x.tell + (y ()).tell⟩

instance [Add w] : SeqRight (AddWriter w) where
  seqRight x y := ⟨(y ()).ret, x.tell + (y ()).tell⟩

instance [AddZero w] : Monad (AddWriter w) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight

@[simp, grind =] theorem ret_pure {α} [Zero w] (a : α) : (pure a : AddWriter w α).ret = a := rfl

@[simp, grind =] theorem ret_bind {α β} [Add w] (m : AddWriter w α) (f : α → AddWriter w β) :
    (m >>= f).ret = (f m.ret).ret := rfl

@[simp, grind =] theorem ret_map {α β} (f : α → β) (x : AddWriter w α) : (f <$> x).ret = f x.ret :=
  rfl

@[simp] theorem ret_seqRight {α} (x : AddWriter w α) (y : Unit → AddWriter w β) [Add w] :
    (SeqRight.seqRight x y).ret = (y ()).ret := rfl

@[simp] theorem ret_seqLeft {α} [Add w] (x : AddWriter w α) (y : Unit → AddWriter w β) :
    (SeqLeft.seqLeft x y).ret = x.ret := rfl

@[simp] theorem ret_seq {α β} [Add w] (f : AddWriter w (α → β)) (x : Unit → AddWriter w α) :
    (Seq.seq f x).ret = f.ret (x ()).ret := rfl

/-- Extracting the return value preserves monadic operations. -/
theorem isMonadHom_pure_ret [AddZero w] : IsMonadHom (AddWriter w) Id (fun x => pure x.ret) where
  map_map _ _ := rfl
  map_mapConst _ _ := rfl
  map_pure _ := rfl
  map_seq _ _ := rfl
  map_seqLeft _ _ := rfl
  map_seqRight _ _ := rfl
  map_bind _ _ := rfl

@[simp, grind =] theorem tell_bind {α β} [Add w] (m : AddWriter w α) (f : α → AddWriter w β) :
    (m >>= f).tell = m.tell + (f m.ret).tell := rfl

@[simp, grind =] theorem tell_pure {α} [Zero w] (a : α) : (pure a : AddWriter w α).tell = 0 := rfl

@[simp, grind =] theorem tell_map {α β} (f : α → β) (x : AddWriter w α) : (f <$> x).tell = x.tell :=
  rfl
@[simp] theorem tell_seqRight {α} [Add w] (x : AddWriter w α) (y : Unit → AddWriter w β) :
    (SeqRight.seqRight x y).tell = x.tell + (y ()).tell := rfl

@[simp] theorem tell_seqLeft {α} [Add w] (x : AddWriter w α) (y : Unit → AddWriter w β) :
    (SeqLeft.seqLeft x y).tell = x.tell + (y ()).tell := rfl

@[simp] theorem tell_seq {α β} [Add w] (f : AddWriter w (α → β)) (x : Unit → AddWriter w α) :
    (Seq.seq f x).tell = f.tell + (x ()).tell := rfl

/-- `AddWriter` is lawful so long as addition in the cost is associative and absorbs zero. -/
instance [AddMonoid w] : LawfulMonad (AddWriter w) := .mk'
  (id_map := fun x => rfl)
  (pure_bind := fun _ _ => by ext <;> simp)
  (bind_assoc := fun _ _ _ => by ext <;> simp [add_assoc])
  (seqLeft_eq := fun _ _ => by ext <;> simp)
  (bind_pure_comp := fun _ _ => by ext <;> simp)

end AddWriter
end Cslib
