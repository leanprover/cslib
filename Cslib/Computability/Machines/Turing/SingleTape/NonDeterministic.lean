/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Relation.Defs
public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Data.BiTape
public import Cslib.Computability.Machines.Turing.SingleTape.Defs

/-! # Single-Tape Nondeterministic Turing Machines (NTMs)

Nondeterministic Turing Machines (NTMs), defined as nondeterministic automata (`NA`) that act on a
bidirectional tape (`BiTape`).
-/

@[expose] public section

namespace Cslib.Computability.Turing.SingleTape

open Automata

/-- A (single-tape) Nondeterministic Turing Machine (NTM) is a nondeterministic automaton equipped
with a set of accepting halting states. -/
structure SingleTapeNTM (State Symbol : Type*)
    extends NA State (TrLabel Symbol) where
  /-- The set of accepting states. -/
  accept : Set State
  /-- Proof that all accepting states are halting states. -/
  accept_halting (hmem : s ∈ accept) : ¬∃ μ s', Tr s μ s'

variable {State Symbol : Type*}

namespace SingleTapeNTM

variable [DecidableEq Symbol]

/-- An NTM yields a small-step operational semantics on configurations, which codifies an execution
step. -/
def Red (m : SingleTapeNTM State Symbol)
    (c c' : Cfg State Symbol) : Prop :=
  ∃ μ, m.Tr c.state μ c'.state ∧ μ.applyToTape c.tape = c'.tape

@[scoped grind =]
theorem red_tr {m : SingleTapeNTM State Symbol} :
    m.Red c c' ↔ ∃ μ, m.Tr c.state μ c'.state ∧ μ.applyToTape c.tape = c'.tape := by rfl

/-- Multistep execution of an NTM, defined as the reflexive and transitive closure of one-step
execution.
-/
@[scoped grind =]
def MRed (m : SingleTapeNTM State Symbol) := Relation.ReflTransGen m.Red

/-- An NTM is an acceptor of finite lists of symbols. -/
@[simp, scoped grind =]
instance : Acceptor (SingleTapeNTM State Symbol) Symbol where
    Accepts (m : SingleTapeNTM State Symbol) (xs : List Symbol) :=
  ∃ s ∈ m.start, ∃ c', c'.state ∈ m.accept ∧ m.MRed (Cfg.mk₁ s xs) c'

end SingleTapeNTM

end Cslib.Computability.Turing.SingleTape
