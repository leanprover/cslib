/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Bolton Bailey
-/

module

public import Cslib.Foundations.Data.BiTape

@[expose] public section

/-! # Basic definitions for Turing Machines (TMs) -/

namespace Cslib.Computability.Turing.SingleTape

/-- The transition labels used by a single-tape Turing Machine. -/
structure TrLabel (State Symbol : Type*) where
  /-- Symbol to read from the tape. -/
  read : Option Symbol
  /-- Symbol to write on the tape. -/
  write : Option Symbol
  /-- Head movement of the tape. -/
  move : Option Turing.Dir

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
