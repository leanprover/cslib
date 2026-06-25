/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Bolton Bailey
-/

module

public import Cslib.Foundations.Data.BiTape

/-! # Basic definitions for Turing Machines (TMs) -/

@[expose] public section

namespace Cslib.Computability.Turing.SingleTape

/-- The transition labels used by a single-tape Turing Machine. -/
inductive TrLabel (Symbol : Type*)
  /-- Read `x` from the tape. -/
  | read (x : Symbol)
  /-- Write `x` on the tape. -/
  | write (x : Symbol)
  /-- Move the head of the tape. -/
  | move (d : Turing.Dir)
  /-- Do nothing. -/
  | skip

/-- Applies a transition label to a tape, returning `none` if it is not possible. -/
def TrLabel.applyToTape [DecidableEq Symbol] (μ : TrLabel Symbol) (tape : Turing.BiTape Symbol) :
    Option (Turing.BiTape Symbol) :=
  match μ with
  | read x => if x = tape.head then some tape else none
  | write x => some (tape.write x)
  | move d => some (tape.move d)
  | skip => some tape

/-- Configuration of a single-tape Turing machine. -/
structure Cfg (State Symbol : Type*) where
  /-- The state that the machine is in. -/
  state : State
  /-- Tape of the machine (memory). -/
  tape : Turing.BiTape Symbol

/-- Helper builder for a configuration with a given tape content. -/
def Cfg.mk₁ (s : State) (xs : List Symbol) : Cfg State Symbol where
  state := s
  tape := Turing.BiTape.mk₁ xs

/-- The space used by a configuration is the space used by its tape. -/
def Cfg.spaceUsed (cfg : Cfg State Symbol) : ℕ := cfg.tape.spaceUsed

end Cslib.Computability.Turing.SingleTape
