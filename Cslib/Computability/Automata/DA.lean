/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.Basic

/-! # Deterministic Automaton

A Deterministic Automaton (DA) is a deterministic labelled transition system with an initial state.
For convenience, it is expressed by giving a transition function.
-/
structure DA (State : Type _) (Symbol : Type _) where
  /-- The initial state of the automaton. -/
  start : State
  /-- The transition function of the automaton. -/
  tr : State → Symbol → State

namespace DA

/-- Extended transition function.

Implementation note: compared to [Hopcroft2006], the definition consumes the input list of symbols
from the left (instead of the right), in order to follow the way lists are constructed.
-/
@[grind]
def mtr (da : DA State Symbol) (s : State) (xs : List Symbol) :=
  match xs with
  | [] => s
  | x :: xs => da.mtr (da.tr s x) xs

@[grind]
theorem mtr_nil_eq {da : DA State Symbol} : da.mtr s [] = s := by rfl

section LTS

/-- `DA` is a special case of `LTS`. -/
@[grind]
def toLTS (da : DA State Symbol) : LTS State Symbol :=
  LTS.mk (fun s1 μ s2 => da.tr s1 μ = s2)

instance : Coe (DA State Symbol) (LTS State Symbol) where
  coe := toLTS

/-- `DA.toLTS` correctly characterises transitions. -/
@[grind]
theorem toLTS_tr {da : DA State Symbol} :
  da.toLTS.Tr s1 μ s2 ↔ da.tr s1 μ = s2 := by
  rfl

/-- `DA.toLTS` correctly characterises multistep transitions. -/
@[grind]
theorem toLTS_mtr {da : DA State Symbol} :
  da.toLTS.MTr s1 xs s2 ↔ da.mtr s1 xs = s2 := by
  constructor <;> intro h
  case mp =>
    induction h <;> grind
  case mpr =>
    induction xs generalizing s1
    case nil => grind
    case cons x xs ih =>
      apply LTS.MTr.stepL (s2 := da.tr s1 x) <;> grind

/-- The LTS induced by a DA is deterministic. -/
@[grind]
theorem toLTS_deterministic (da : DA State Symbol) : da.toLTS.Deterministic := by
  grind

end LTS

end DA
