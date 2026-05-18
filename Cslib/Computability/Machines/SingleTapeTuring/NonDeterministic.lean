/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Data.BiTape
public import Cslib.Foundations.Semantics.LTS.HasTau

/-! # Single-Tape Nondeterministic Turing Machines (NTMs)

Nondeterministic Turing Machines (NTMs), defined as nondeterministic automata (`NA`) that act on a
bidirectional tape (`BiTape`).
-/

@[expose] public section

namespace Cslib.Computability.Turing.NTM

open Automata Turing

/-- The transition labels used by a controller. -/
structure SingleTapeNTM.TrLabel (State Symbol : Type*) where
  read : Option Symbol
  write : Option Symbol
  move : Option Turing.Dir -- Might wanna use a larger inductive here (see Move)

/-- A (single-tape) Nondeterministic Turing Machine (NTM) is a nondeterministic automaton equipped
with a set of accepting halting states. -/
structure SingleTapeNTM (State Symbol : Type*)
    extends NA State (SingleTapeNTM.TrLabel State Symbol) where
  /-- The set of accepting states. -/
  accept : Set State
  /-- Proof that all accepting states are halting states. -/
  accept_halting (hmem : s ∈ accept) : ¬∃ μ s', Tr s μ s'

/-- Configuration of a single-tape Turing machine. -/
structure Cfg (State Symbol : Type*) where
  /-- Current state in the machine's controller. -/
  state : State
  /-- Current memory of the machine. -/
  tape : Turing.BiTape Symbol

/-- An NTM yields a small-step operational semantics on configurations, which codifies an execution
step. -/
@[scoped grind =]
def SingleTapeNTM.Red {Symbol} (m : SingleTapeNTM State Symbol)
    (c c' : Cfg State Symbol) : Prop :=
  ∃ μ, m.Tr c.state μ c'.state ∧ -- The controller can perform the move
    μ.read = c.tape.head ∧ -- The tape has the expected symbol to be read
    c'.tape = (c.tape.write μ.write).optionMove μ.move -- Write effect on the tape

/-- Multistep execution of an NTM, defined as the reflexive and transitive closure of one-step
execution.
-/
@[scoped grind =]
def SingleTapeNTM.MRed {Symbol} (m : SingleTapeNTM State Symbol) :=
  Relation.ReflTransGen m.Red

/-- An NTM is an acceptor of finite lists of symbols. -/
@[simp, scoped grind =]
instance {Symbol} : Acceptor (SingleTapeNTM State Symbol) Symbol where
  Accepts (m : SingleTapeNTM State Symbol) (xs : List Symbol) :=
    ∃ s ∈ m.start, ∃ c', m.MRed {state := s, tape := Turing.BiTape.mk₁ xs} c'

end Cslib.Computability.Turing.NTM
