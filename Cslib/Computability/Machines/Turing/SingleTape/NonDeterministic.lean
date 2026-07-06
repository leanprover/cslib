/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Relation.Defs
public import Cslib.Foundations.Data.RelatesInSteps
public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Automata.Transducers.Transducer
public import Cslib.Foundations.Data.BiTape
public import Cslib.Computability.Machines.Turing.SingleTape.Defs

/-! # Single-Tape Nondeterministic Turing Machines (NTMs)

Nondeterministic Turing Machines (NTMs), defined as nondeterministic automata (`NA`) that act on a
bidirectional tape (`BiTape`).

## References

* [M. Sipser, *Introduction to Theory of Computation*][Sipser2013]
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
step. This formalises the 'yields' relation from [Sipser2013]. -/
def Yields (m : SingleTapeNTM State Symbol)
    (c c' : Cfg State Symbol) : Prop :=
  ∃ μ, m.Tr c.state μ c'.state ∧ μ.applyToTape c.tape = c'.tape

@[scoped grind =]
theorem yields_tr {m : SingleTapeNTM State Symbol} :
    m.Yields c c' ↔ ∃ μ, m.Tr c.state μ c'.state ∧ μ.applyToTape c.tape = c'.tape := by rfl

/-- Multistep execution of an NTM, defined as the reflexive and transitive closure of one-step
execution.
-/
def MYields (m : SingleTapeNTM State Symbol) := Relation.ReflTransGen m.Yields

open scoped LTS LTS.MTr TrLabel

/-- Characterisation of executions in terms of multistep transitions. -/
@[scoped grind =]
theorem mYields_mTr {m : SingleTapeNTM State Symbol} :
    m.MYields c c' ↔ ∃ μs, m.MTr c.state μs c'.state ∧
    μs.foldl TrLabel.applyToTape (some c.tape) = c'.tape := by
  apply Iff.intro <;> intro h
  case mp =>
    induction h using Relation.ReflTransGen.head_induction_on
    case refl =>
      exists []
      grind
    case head _ c cb hred hmred ih =>
      rcases ih with ⟨μs, hmtr, ih⟩
      have ⟨μ, _⟩ := yields_tr.mp hred
      exists μ :: μs
      grind
  case mpr =>
    rcases h with ⟨μs, hmtr, h⟩
    induction μs generalizing c
    case nil =>
      rw [show c = c' by grind [Cfg.ext]]
      apply Relation.ReflTransGen.refl
    case cons μ μs ih =>
      cases hmtr
      case stepL sb htr hmtr =>
        have hat : ∀ (μ : TrLabel Symbol) t, (μ.applyToTape t).isSome → t.isSome := by grind
        have ⟨tb, htb⟩ : ∃ tb, μ.applyToTape c.tape = some tb := by grind [Option.isSome_iff_exists]
        let cb := {state := sb, tape := tb : Cfg State Symbol}
        have hmyields : m.MYields cb c' := by grind
        apply Relation.ReflTransGen.head (b := cb) (by grind)
        simp only [MYields] at hmyields
        grind

/-- An NTM is an acceptor of finite lists of symbols. -/
instance : Acceptor (SingleTapeNTM State Symbol) Symbol where
    Accepts (m : SingleTapeNTM State Symbol) (xs : List Symbol) :=
  ∃ s ∈ m.start, ∃ c', c'.state ∈ m.accept ∧ m.MYields (Cfg.mk₁ s xs) c'

/-- The NTM `m` accepts `xs` in `n` execution steps. -/
def AcceptsInSteps (m : SingleTapeNTM State Symbol) (xs : List Symbol) (n : ℕ) : Prop :=
  ∃ s ∈ m.start, ∃ c', c'.state ∈ m.accept ∧ Relation.RelatesInSteps m.Yields (Cfg.mk₁ s xs) c' n

/-- The NTM `m` accepts `xs` in at most `n` execution steps. -/
def AcceptsInAtMostSteps (m : SingleTapeNTM State Symbol) (xs : List Symbol) (n : ℕ) : Prop :=
  ∃ k ≤ n, m.AcceptsInSteps xs k

/-- An NTM is a transducer of finite lists of symbols. -/
instance : Transducer (SingleTapeNTM State Symbol) Symbol Symbol where
    Translates (m : SingleTapeNTM State Symbol) (xs ys : List Symbol) :=
  ∃ s ∈ m.start, ∃ c',
    c'.state ∈ m.accept ∧
    m.MYields (Cfg.mk₁ s xs) c' ∧
    /- The following condition on output deviates from textbooks, in order to have the same
    criterion as for deterministic TMs. We might want to revisit this in the future.
    -/
    c'.tape = Turing.BiTape.mk₁ ys

end SingleTapeNTM

end Cslib.Computability.Turing.SingleTape
