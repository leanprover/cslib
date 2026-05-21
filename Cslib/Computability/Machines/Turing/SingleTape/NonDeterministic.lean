/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Data.BiTape
public import Cslib.Computability.Machines.Turing.SingleTape.Defs

/-! # Single-Tape Nondeterministic Turing Machines (NTMs)

Nondeterministic Turing Machines (NTMs), defined as nondeterministic automata (`NA`) that act on a
bidirectional tape (`BiTape`).
-/

@[expose] public section

namespace Cslib.Computability.Turing.SingleTape

open Automata Turing

/-- A (single-tape) Nondeterministic Turing Machine (NTM) is a nondeterministic automaton equipped
with a set of accepting halting states. -/
structure SingleTapeNTM (State Symbol : Type*)
    extends NA State (SingleTape.TrLabel State Symbol) where
  /-- The set of accepting states. -/
  accept : Set State
  /-- Proof that all accepting states are halting states. -/
  accept_halting (hmem : s ∈ accept) : ¬∃ μ s', Tr s μ s'

variable {State Symbol : Type*}

/-- An NTM yields a small-step operational semantics on configurations, which codifies an execution
step. -/
@[scoped grind =]
def SingleTapeNTM.Red (m : SingleTapeNTM State Symbol)
    (c c' : Cfg State Symbol) : Prop :=
  ∃ μ, m.Tr c.state μ c'.state ∧ -- The controller can perform the move
    μ.read = c.tape.head ∧ -- The tape has the expected symbol to be read
    c'.tape = (c.tape.write μ.write).optionMove μ.move -- Write effect on the tape

/-- Multistep execution of an NTM, defined as the reflexive and transitive closure of one-step
execution.
-/
@[scoped grind =]
def SingleTapeNTM.MRed (m : SingleTapeNTM State Symbol) :=
  Relation.ReflTransGen m.Red

/-- An NTM is an acceptor of finite lists of symbols. -/
@[simp, scoped grind =]
instance : Acceptor (SingleTapeNTM State Symbol) Symbol where
  Accepts (m : SingleTapeNTM State Symbol) (xs : List Symbol) :=
    ∃ s ∈ m.start, ∃ c', c'.state ∈ m.accept ∧ m.MRed (Cfg.mk₁ s xs) c'

end Cslib.Computability.Turing.SingleTape
