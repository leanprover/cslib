/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Data.BiTape
public import Cslib.Foundations.Semantics.LTS.HasTau

/-! # Nondeterministic Single-Tape Turing Machines -/

@[expose] public section

namespace Cslib.Computability.Turing

open Automata Turing

inductive Direction
  | left | right

-- # Alternative 1: everything is visible and the tape is kept separate from states,
-- a-la reactive turing machines

structure NA.TM (State Symbol : Type*) [HasTau Symbol]
    extends NA State (Symbol × Symbol × Direction)

structure SingleTapeNDTM (State Symbol : Type*) [HasTau Symbol] where
  a : NA.TM State Symbol
  tape : Turing.BiTape Symbol

variable {Symbol} [HasTau Symbol]

-- Define the effect of a transition on the tape

-- Define the semantics of a tape under a fixed TM, or a relation between TMs where the `a` remains
-- unaltered.

-- # Alternative 2: states contain the tape, transitions are labelled by the symbol being read

namespace Alternative2

open Automata Turing

structure NA.TM (State Symbol : Type*) [HasTau Symbol]
    extends NA (State × Turing.BiTape Symbol) Symbol

end Alternative2

end Cslib.Computability.Turing
