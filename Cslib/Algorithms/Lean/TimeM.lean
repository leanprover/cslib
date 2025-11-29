/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
-/

import Mathlib.Tactic

/-!
# Time Monad

`TimeM` is a monad that tracks execution time alongside computations.
Time is represented as rational numbers (`ℚ`) to facilitate
manipulation of recurrence relations.

## Notation

 - `✓` : a tick of time, see `tick`.

## References

See [Danielsson'08] for the discussion.
-/

set_option tactic.hygienic false
set_option autoImplicit false

structure TimeM (α : Type) where
  ret : α
  time : ℕ

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

end TimeM
