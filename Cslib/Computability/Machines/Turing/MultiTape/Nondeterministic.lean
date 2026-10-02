/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Mathlib.Order.RelSeries
public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-!
# Nondeterministic Multi-Tape Turing Machines

Defines nondeterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape, and computations that halt and emit a given output.

## Design

The design choices for configurations and actions are documented in
`Cslib.Computability.Machines.Turing.MultiTape.Configuration`.

Following [Papadimitriou94], chapter 2.7, a nondeterministic machine is a Turing machine whose
transition function is replaced by a transition relation: `Tr q input work action` holds when
`action` is one of the actions permitted in that situation.

A halted configuration steps to itself, so once a machine has halted it has a run of every length.
A time bound is therefore an upper bound, with no separate account of the step at which it halted.

The transition relation may be empty at a running configuration, so a machine can get stuck. The
computation predicates ask for a path ending in a halted configuration, so a stuck one is not a
witness.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `Step`: the one-step relation on configurations
* `RunPath`: finite relation series of steps
* `ComputationPath`: a run path starting at the initial configuration
* `ComputesSuchThat`: some computation halts, emits a given output and meets a given constraint
* `Computes`, `ComputesInExactTime`: its instances, with no constraint or a given number of steps

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/--
A nondeterministic multi-tape Turing machine with `k` work tapes over the alphabet of
`Option Symbol` (where `none` is the blank symbol). Neither `Symbol` nor `State` is required to be
finite.
-/
structure MultiTapeNTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition relation: which combinations of state, current input symbol, tuple of work head
  symbols and resulting actions are valid transitions -/
  Tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol)
    (action : Action k Symbol State) : Prop

namespace MultiTapeNTM

variable {ntm : MultiTapeNTM k Symbol State}

/-- The one-step relation on configurations. A halted configuration steps to itself. A running one
steps by any permitted transition. -/
@[scoped grind =]
def Step (ntm : MultiTapeNTM k Symbol State) (c₁ c₂ : Cfg k Symbol State input) : Prop :=
  match c₁.state with
  | none => c₂ = c₁
  | some q =>
    ∃ action, ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols action ∧ c₂ = action.apply c₁

/-- A halted configuration steps only to itself. -/
lemma step_of_halt {c c' : Cfg k Symbol State input} (h : c.Halted) :
    ntm.Step c c' ↔ c' = c := by
  simp [Step, h]

/-- A step emits at most one symbol. -/
lemma Step.length_output_le {c c' : Cfg k Symbol State input} (h : ntm.Step c c') :
    c'.output.length ≤ c.output.length + 1 := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨action, _, rfl⟩ := h
    simp

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    Cfg k Symbol State input :=
  Cfg.init ntm.q₀ input

/-- A nonempty list of configurations joined by steps of `ntm`. -/
abbrev RunPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :=
  RelSeries {(c, c') | ntm.Step (input := input) c c'}

namespace RunPath

/-- A run path emits at most one symbol per step. -/
lemma length_output_le (p : ntm.RunPath input) :
    p.last.output.length ≤ p.head.output.length + p.length := by
  induction p using RelSeries.inductionOn' with
  | singleton c => simp
  | snoc p c h ih =>
    simpa [Nat.add_assoc] using (Step.length_output_le h).trans (Nat.add_le_add_right ih 1)

/-- The number of steps taken by a run path. -/
def time (p : ntm.RunPath input) : ℕ := p.length

end RunPath

/-- A run path starting at the initial configuration for `input`. -/
structure ComputationPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol)
    extends toRunPath : ntm.RunPath input where
  /-- the path starts at the initial configuration -/
  head_eq : toRunPath.head = ntm.initCfg input

namespace ComputationPath

/-- The number of steps taken by a computation path. -/
def time (p : ntm.ComputationPath input) : ℕ := RunPath.time p.toRunPath

end ComputationPath

/-- `ntm` has a computation on `input` that starts at the initial configuration, halts, emits
`output` and satisfies `P`. The notions below are its instances, so their constraints all refer to
a single computation. -/
def ComputesSuchThat (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (P : ntm.ComputationPath input → Prop) : Prop :=
  ∃ p : ntm.ComputationPath input, p.last.Halted ∧ p.last.output = output ∧ P p

/-- `ntm` computes `output` from `input`, with no bound on resources. -/
def Computes (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) : Prop :=
  ntm.ComputesSuchThat input output fun _ => True

/-- `ntm` computes `output` from `input` in exactly `t` steps. -/
def ComputesInExactTime (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (t : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p => p.time = t

end MultiTapeNTM

end Turing
