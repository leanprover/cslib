/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Languages.OmegaLanguage

/-! # Deterministic Automaton
-/

open List Filter

namespace Cslib

-- TODO: FLTS related code should be moved to their own files.

/-- Functional LTS -/
structure FLTS (State Symbol : Type*) where
  tr : State → Symbol → State

namespace FLTS

variable {State Symbol : Type*}

/-- Extended transition function. -/
@[scoped grind =]
def mtr (da : FLTS State Symbol) (s : State) (xs : List Symbol) := xs.foldl da.tr s

@[simp, scoped grind =]
theorem mtr_nil_eq {da : FLTS State Symbol} {s : State} : da.mtr s [] = s := rfl

end FLTS

structure DA (State Symbol : Type*) extends FLTS State Symbol where
  /-- The initial state of the automaton. -/
  start : State

structure DA.FinAcc (State Symbol : Type*) extends DA State Symbol where
  acc : Set State

structure DA.Buchi (State Symbol : Type*) extends DA State Symbol where
  acc : Set State

structure DA.Muller (State Symbol : Type*) extends DA State Symbol where
  accSet : Set (Set State)

variable {State Symbol : Type*}

namespace DA

/-- Helper function for defining `run` below. -/
@[simp, scoped grind =]
def run' (da : DA State Symbol) (xs : ωSequence Symbol) : ℕ → State
  | 0 => da.start
  | n + 1 => da.tr (run' da xs n) (xs n)

/-- Infinite run. -/
@[scoped grind =]
def run (da : DA State Symbol) (xs : ωSequence Symbol) : ωSequence State := da.run' xs

namespace FinAcc

@[scoped grind =]
def Accept (dfa : FinAcc State Symbol) (xl : List Symbol) :=
  dfa.mtr dfa.start xl ∈ dfa.acc

@[scoped grind =]
def language (dfa : FinAcc State Symbol) : Language Symbol :=
  { xl : List Symbol | dfa.Accept xl }

@[scoped grind =]
theorem mem_language (dfa : FinAcc State Symbol) (xl : List Symbol) :
    xl ∈ dfa.language ↔ dfa.mtr dfa.start xl ∈ dfa.acc :=
  Iff.rfl

end FinAcc

namespace Buchi

@[scoped grind =]
def Accept (dba : Buchi State Symbol) (xs : ωSequence Symbol) :=
  ∃ᶠ k in atTop, dba.run xs k ∈ dba.acc

@[scoped grind =]
def language (dba : Buchi State Symbol) : ωLanguage Symbol :=
  { xs : ωSequence Symbol | dba.Accept xs }

@[scoped grind =]
theorem mem_language (dba : Buchi State Symbol) (xs : ωSequence Symbol) :
    xs ∈ dba.language ↔ dba.Accept xs :=
  Iff.rfl

end Buchi

namespace Muller

@[scoped grind =]
def Accept (dma : Muller State Symbol) (xs : ωSequence Symbol) :=
  (dma.run xs).infOcc ∈ dma.accSet

@[scoped grind =]
def language (dma : Muller State Symbol) : ωLanguage Symbol :=
  { xs : ωSequence Symbol | dma.Accept xs }

@[scoped grind =]
theorem mem_language (dma : Muller State Symbol) (xs : ωSequence Symbol) :
    xs ∈ dma.language ↔ dma.Accept xs :=
  Iff.rfl

end Muller

end DA

end Cslib
