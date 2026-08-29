/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Mathlib.Data.List.Chain
public import Cslib.Foundations.Data.List.IsChainFromTo
public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-!
# Nondeterministic Multi-Tape Turing Machines

Defines nondeterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape, and what it means for one to compute an output within a time and space
bound.

## Design

Following [Papadimitriou94], chapter 2.7, a nondeterministic machine is a Turing machine whose
transition function is replaced by a transition relation: `Tr q input work action` holds when
`action` is one of the actions permitted in that situation.

A halted configuration steps to itself, so once a machine has halted it has a run of every length.
A time bound is therefore an upper bound, with no separate account of the step at which it halted.

The transition relation may be empty at a running configuration, so a machine can get stuck. Every
notion below asks for a computation ending in a halted configuration, so a stuck one is not a
witness.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `Step`: the one-step relation on configurations
* `ComputationPath`: a run of the machine: a series of configurations from the initial one, each
    reached from the previous by a step
* `ComputationPath.space_le`: a machine touches at most `k` cells per step
* `ComputesSuchThat`: some computation halts, emits a given output and meets a given constraint
* `Computes`, `ComputesInExactTime`, `ComputesInExactSpace`, `ComputesInExactTimeAndSpace`:
    its instances, whose
    bounds all refer to a single computation

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
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

/-- The one-step relation on configurations. A halted configuration steps to itself; a running one
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

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    Cfg k Symbol State input :=
  Cfg.init ntm.q₀ input

/-- A computation path of `ntm` on `input`: the configurations it passes through, forming a chain
of steps from the initial configuration to the one it ends at. -/
structure ComputationPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) where
  /-- the configurations passed through, starting with the initial one -/
  cfgs : List (Cfg k Symbol State input)
  /-- the configuration the path ends at -/
  last : Cfg k Symbol State input
  /-- consecutive configurations are joined by a step, from the initial configuration to `last` -/
  isChainFromTo : cfgs.IsChainFromTo ntm.Step (ntm.initCfg input) last

namespace ComputationPath

variable {ntm : MultiTapeNTM k Symbol State} {input : List Symbol}

/-- The number of steps taken, the time the computation takes. -/
def time (p : ntm.ComputationPath input) : ℕ := p.cfgs.length - 1

/-- The number of work tape cells touched. -/
def space (p : ntm.ComputationPath input) : ℕ := spaceUsedOfCfgs p.cfgs

/-- A path visiting `t + 1` configurations takes `t` steps. -/
lemma length_cfgs (p : ntm.ComputationPath input) : p.cfgs.length = p.time + 1 := by
  have := p.isChainFromTo.length_pos
  simp only [time]
  omega

/-- A machine touches at most `k` cells per step, whether or not it is deterministic. -/
theorem space_le (p : ntm.ComputationPath input) : p.space ≤ k * p.time + k := by
  calc p.space ≤ k * p.cfgs.length := spaceUsedOfCfgs_le _
    _ = k * p.time + k := by rw [p.length_cfgs, Nat.mul_succ]

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

/-- `ntm` computes `output` from `input` touching exactly `s` work tape cells. -/
def ComputesInExactSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (s : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p => p.space = s

/-- `ntm` computes `output` from `input` in `t` steps and `s` work tape cells, by a single
computation. -/
def ComputesInExactTimeAndSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (t s : ℕ) : Prop :=
  ntm.ComputesSuchThat input output fun p => p.time = t ∧ p.space = s

end MultiTapeNTM

end Turing
