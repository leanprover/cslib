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

namespace Cslib.Computability.Turing.NTM

open Automata Turing

-- inductive Move
--   | stay | left | right

structure Controller.TrLabel (State Symbol : Type*) where
  read : Option Symbol
  write : Option Symbol
  move : Option Turing.Dir -- Might wanna use a larger inductive here (see Move)

structure Controller (State Symbol : Type*)
    extends NA State (Controller.TrLabel State Symbol)

structure Cfg (State Symbol : Type*) where
  state : State
  tape : Turing.BiTape Symbol

structure SingleTapeNTM (State Symbol : Type*) where
  /-- The controller automaton of the machine. -/
  controller : Controller State Symbol
  /-- The set of accepting (halting) states. -/
  accept : Set State

-- Transition relation for configurations
-- Due to the way BiTape is written, Symbol cannot be universe-polymorphic. To be fixed.
def SingleTapeNTM.Tr {Symbol} (m : SingleTapeNTM State Symbol)
    (c c' : Cfg State Symbol) : Prop :=
  c.state ∉ m.accept ∧
  ∃ μ, m.controller.Tr c.state μ c'.state ∧
    μ.read = c.tape.head ∧ c'.tape = (c.tape.write μ.write).optionMove μ.move

def SingleTapeNTM.MTr {Symbol} (m : SingleTapeNTM State Symbol) := Relation.ReflTransGen m.Tr

def SingleTapeNTM.Accepts {Symbol} (m : SingleTapeNTM State Symbol)
    (xs : List Symbol) : Prop :=
  ∃ s ∈ m.controller.start, ∃ c', m.MTr (Cfg.mk s (Turing.BiTape.mk₁ xs)) c'

end Cslib.Computability.Turing.NTM
