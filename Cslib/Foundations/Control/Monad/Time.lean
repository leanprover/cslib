/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai, Tanner Duve
-/

import Mathlib.Control.Monad.Writer

/-!
# Time Monad

`TimeM` is a monad that tracks execution time alongside computations, using natural numbers
as a simple cost model. As plain types it is isomorphic to `WriterT Nat Id`.
-/

structure TimeM (α : Type u) where
  /-- The result of the computation. -/
  ret : α
  /-- The accumulated time cost. -/
  time : Nat

namespace TimeM

def pure {α} (a : α) : TimeM α :=
  ⟨a, 0⟩

def bind {α β} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance : Monad TimeM where
  pure := pure
  bind := bind

@[simp] def tick {α : Type} (a : α) (c : ℕ := 1) : TimeM α :=
  ⟨a, c⟩

scoped notation "✓" a:arg ", " c:arg => tick a c
scoped notation "✓" a:arg => tick a  -- Default case with only one argument

def tickUnit : TimeM Unit :=
  ✓ () -- This uses the default time increment of 1

@[simp] theorem time_of_pure {α} (a : α) : (pure a).time = 0 := rfl
@[simp] theorem time_of_bind {α β} (m : TimeM α) (f : α → TimeM β) :
 (TimeM.bind m f).time = m.time + (f m.ret).time := rfl
@[simp] theorem time_of_tick {α} (a : α) (c : ℕ) : (tick a c).time = c := rfl
@[simp] theorem ret_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (TimeM.bind m f).ret = (f m.ret).ret := rfl

-- this allow us to simplify the chain of compositions
attribute [simp] Bind.bind Pure.pure TimeM.pure

/-- `TimeM` is (definitionally) the same as the writer monad `WriterT Nat Id`. -/
abbrev WriterNat (α : Type) := WriterT Nat Id α

/-- Equivalence between `TimeM α` and `WriterT Nat Id α` as plain types. -/
def equivWriter (α : Type) : TimeM α ≃ WriterNat α where
  toFun m := (m.ret, m.time)
  invFun w := ⟨w.1, w.2⟩
  left_inv m := by cases m; rfl
  right_inv w := by cases w; rfl

@[simp] lemma equivWriter_toFun {α : Type} (m : TimeM α) :
    (equivWriter α m : WriterNat α) = (m.ret, m.time) := rfl

@[simp] lemma equivWriter_invFun {α : Type} (w : WriterNat α) :
    (equivWriter α).invFun w = TimeM.mk w.1 w.2 := rfl

end TimeM
