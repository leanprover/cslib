/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Foundations.Semantics.LTS.Execution
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Nondeterministic Multi-Tape Turing Machines

Defines nondeterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape, and what it means for one to compute an output within a time and space
bound.

## Design

Following [Papadimitriou94], chapter 2.7, a nondeterministic machine is a `MultiTapeTM` whose
transition function is replaced by a transition relation: `Tr q input work out` holds when `out` is
one of the transitions permitted in that situation. Configurations, transition outputs and
`TransitionOut.apply` are shared with the deterministic machine.

The semantics is the labelled transition system `lts` on configurations, a step being labelled by
the symbol it emits. The label is where that symbol has to live, since two transitions may lead to
the same successor while emitting different symbols. A halted configuration steps to itself
emitting nothing, as `MultiTapeTM.step` does.

A `Computation` is a chain of such transitions, with `final`, `time`, `output` and `visited` read
off it by recursion and `space` counting the cells `visited` touches. Space depends on the whole
trajectory and output on the labels, so a computation records both.

The transition relation may be empty at a running configuration. Every notion below asks for a
computation whose final configuration has halted, so one that cannot continue is not a witness.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `lts`: the labelled transition system on configurations, labelled by the emitted symbol
* `Step`: its underlying unlabelled relation
* `Computation`: a chain of transitions, with `time`, `space`, `output` and `Halts`
* `ComputesSuchThat`: some computation halts, emits a given output and meets a given constraint
* `Computes`, `ComputesInTime`, `ComputesInSpace`, `ComputesInTimeAndSpace`: its instances, whose
    bounds all refer to a single computation

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

open Cslib

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
  /-- transition relation: which transitions are permitted for a state, the current input symbol
  and a tuple of work head symbols -/
  Tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    TransitionOut k Symbol State → Prop

namespace MultiTapeNTM

variable {ntm : MultiTapeNTM k Symbol State}

/-- The labelled transition system on configurations. A halted configuration steps to itself
emitting nothing; a running one steps by any permitted transition. -/
def lts (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    LTS (Cfg k Symbol State input) (Option Symbol) where
  Tr c₁ o c₂ := match c₁.state with
    | none => o = none ∧ c₂ = c₁
    | some q =>
      ∃ out, ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols out ∧ out.outS = o ∧ c₂ = out.apply c₁

/-- A halted configuration idles, emitting nothing, exactly as `MultiTapeTM.step` does. -/
theorem lts_tr_of_halt {c₁ c₂ : Cfg k Symbol State input} {o : Option Symbol}
    (h_halt : c₁.Halted) : (ntm.lts input).Tr c₁ o c₂ ↔ o = none ∧ c₂ = c₁ := by
  simp [lts, h_halt]

/-- The one-step relation on configurations, forgetting the emitted symbol. Nondeterministic
analogue of `MultiTapeTM.TransitionRelation`. -/
@[scoped grind =]
abbrev Step (c₁ c₂ : Cfg k Symbol State input) : Prop := (ntm.lts input).UnlabelledTr c₁ c₂

/-- A halted configuration steps only to itself. -/
theorem step_of_halt {c c' : Cfg k Symbol State input} (h_halt : c.Halted) :
    ntm.Step c c' ↔ c' = c := by
  simp [Step, LTS.UnlabelledTr, lts_tr_of_halt h_halt]

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init ntm.q₀ input

/-- A computation of `ntm` from configuration `c`: a chain of transitions of `lts`, in the style of
`SimpleGraph.Walk`. -/
inductive Computation (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    Cfg k Symbol State input → Type _
  /-- The empty computation, which does nothing. -/
  | nil {c : Cfg k Symbol State input} : ntm.Computation input c
  /-- Extend a computation by one transition at its front. -/
  | cons {c₁ c₂ : Cfg k Symbol State input} (o : Option Symbol)
      (h : (ntm.lts input).Tr c₁ o c₂) (rest : ntm.Computation input c₂) :
      ntm.Computation input c₁

namespace Computation

variable {ntm : MultiTapeNTM k Symbol State} {input : List Symbol}
  {c : Cfg k Symbol State input}

/-- The configuration the computation ends in. -/
def final {c : Cfg k Symbol State input} : ntm.Computation input c → Cfg k Symbol State input
  | .nil => c
  | .cons _ _ rest => rest.final

/-- The symbol emitted at each step, in order. -/
def labels {c : Cfg k Symbol State input} : ntm.Computation input c → List (Option Symbol)
  | .nil => []
  | .cons o _ rest => o :: rest.labels

/-- The configurations passed through, starting with `c`. -/
def visited {c : Cfg k Symbol State input} :
    ntm.Computation input c → List (Cfg k Symbol State input)
  | .nil => [c]
  | .cons _ _ rest => c :: rest.visited

/-- The number of steps taken. -/
def time (p : ntm.Computation input c) : ℕ := p.labels.length

/-- The string emitted. -/
def output (p : ntm.Computation input c) : List Symbol := outputOfLabels p.labels

/-- The number of work tape cells touched. -/
def space (p : ntm.Computation input c) : ℕ := spaceUsedOfCfgs p.visited

/-- The computation ended in the halting state. -/
abbrev Halts (p : ntm.Computation input c) : Prop := p.final.Halted

end Computation

/-- `ntm` has a computation on `input` that halts, emits `output` and satisfies `P`. The notions
below are its instances, so their constraints all refer to a single computation. -/
def ComputesSuchThat (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (P : ntm.Computation input (ntm.initCfg input) → Prop) : Prop :=
  ∃ p : ntm.Computation input (ntm.initCfg input), p.Halts ∧ p.output = output ∧ P p

/-- `ntm` computes `output` from `input`, with no bound on resources. -/
def Computes (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) : Prop :=
  ntm.ComputesSuchThat input output fun _ => True

/-- `ntm` computes `output` from `input` in exactly `t` steps. -/
def ComputesInTime (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (t : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p => p.time = t

/-- `ntm` computes `output` from `input` touching exactly `s` work tape cells. -/
def ComputesInSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (s : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p => p.space = s

/-- `ntm` computes `output` from `input` in `t` steps and `s` work tape cells, by a single
computation. Nondeterministic analogue of `MultiTapeTM.ComputesInTimeAndSpace`. -/
def ComputesInTimeAndSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (t s : ℕ) : Prop :=
  ntm.ComputesSuchThat input output fun p => p.time = t ∧ p.space = s

end MultiTapeNTM

end Turing
