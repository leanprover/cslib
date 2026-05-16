/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Data.BiTape
public import Cslib.Foundations.Semantics.LTS.HasTau

/-! # Nondeterministic Single-Tape Turing Machines

Nondeterministic Turing Machines (NTMs) defined as the composition of a nondeterministic controller
(an `NA`) with a bidirectional tape (`BiTape`).
-/

@[expose] public section

namespace Cslib.Computability.Turing.NTM

open Automata Turing

-- inductive Move
--   | stay | left | right

/-- The transition labels used by a controller. -/
structure Controller.TrLabel (State Symbol : Type*) where
  read : Symbol
  write : Option Symbol
  move : Option Turing.Dir -- Might wanna use a larger inductive here (see Move)

/-- The automaton that defines the behaviour of an NTM. -/
structure Controller (State Symbol : Type*)
    extends NA State (Controller.TrLabel State Symbol) where

/-- Configuration of a Turing machine. -/
structure Cfg (State Symbol : Type*) where
  state : State
  tape : Turing.BiTape Symbol

/-- Single-tape Nondeterministic Turing Machine. -/
structure SingleTapeNTM (State Symbol : Type*) where
  /-- The controller of the machine. -/
  controller : Controller State Symbol
  /-- The set of accepting (halting) states. -/
  accept : Set State
  /-- Proof that all accepting states are halting states. -/
  controller_halts (hmem : s ∈ accept) : ¬∃ μ s', controller.Tr s μ s'

/-- The 'yields' relation, a binary relation on configurations that codifies an execution step. -/
def SingleTapeNTM.Yields {Symbol} (m : SingleTapeNTM State Symbol)
    (c c' : Cfg State Symbol) : Prop :=
  ∃ μ, m.controller.Tr c.state μ c'.state ∧ -- The controller can perform the move
    μ.read = c.tape.head ∧ -- The tape has the expected symbol to be read
    c'.tape = (c.tape.write μ.write).optionMove μ.move -- Write effect on the tape

/-- The extended 'yields' relation, obtained by closing `Yields` for reflexivity and transitivity.
-/
def SingleTapeNTM.MYields {Symbol} (m : SingleTapeNTM State Symbol) :=
  Relation.ReflTransGen m.Yields

/-- An NTM is an acceptor of finite lists of symbols. -/
@[simp, scoped grind =]
instance {Symbol} : Acceptor (SingleTapeNTM State Symbol) Symbol where
  Accepts (m : SingleTapeNTM State Symbol) (xs : List Symbol) :=
    ∃ s ∈ m.controller.start, ∃ c', m.MYields {state := s, tape := Turing.BiTape.mk₁ xs} c'

end Cslib.Computability.Turing.NTM
