/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.Accept

/-! # Deterministic Automaton
-/

namespace Cslib

open List

structure DA (State Symbol : Type*) where
  /-- The initial state of the automaton. -/
  start : State
  /-- The transition function of the automaton. -/
  tr : State → Symbol → State

variable {State Symbol : Type*}

namespace DA

/-- Extended transition function. -/
@[scoped grind =]
def mtr (da : DA State Symbol) (s : State) (xs : List Symbol) := xs.foldl da.tr s

@[simp, scoped grind =]
theorem mtr_nil_eq {da : DA State Symbol} {s : State} : da.mtr s [] = s := rfl

/-- Infinite run. -/
@[simp, scoped grind =]
def run' (da : DA State Symbol) (xs : ωSequence Symbol) : ℕ → State
  | 0 => da.start
  | n + 1 => da.tr (run' da xs n) (xs n)

@[scoped grind =]
def run (da : DA State Symbol) (xs : ωSequence Symbol) : ωSequence State := da.run' xs

@[scoped grind =]
def accept (da : DA State Symbol) (acc : Set State) : Accept State Symbol where
  Run xl s := da.mtr da.start xl = s
  acc := acc

@[scoped grind =]
def language (da : DA State Symbol) (acc : Set State) : Language Symbol :=
  (da.accept acc).language

@[scoped grind =]
theorem mem_language (da : DA State Symbol) (acc : Set State) (xl : List Symbol) :
    xl ∈ da.language acc ↔ da.mtr da.start xl ∈ acc := by
  constructor
  · rintro ⟨_, _, rfl⟩
    assumption
  · intro h
    refine ⟨da.mtr da.start xl, h, rfl⟩

@[scoped grind =]
def mullerAccept (da : DA State Symbol) (accSet : Set (Set State)) : MullerAccept State Symbol where
  Run xs ss := da.run xs = ss
  accSet := accSet

@[scoped grind =]
def mullerLanguage (da : DA State Symbol) (accSet : Set (Set State)) : ωLanguage Symbol :=
  (da.mullerAccept accSet).language

end DA

end Cslib
