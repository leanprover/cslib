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
write-only output tape, their computation paths, acceptance, and running time.

## Design

The design choices for configurations and actions are documented in
`Cslib.Computability.Machines.Turing.MultiTape.Configuration`.

Following [Papadimitriou94], chapter 2.7, a nondeterministic machine is a Turing machine whose
transition function is replaced by a transition relation: `Tr q input work action` holds when
`action` is one of the actions permitted in that situation.

A halted configuration steps to itself, so once a machine has halted it has a run of every length.
A time bound is therefore an upper bound, with no separate account of the step at which it halted.

Acceptance means that some computation halts with output `[true]`. A branch with no permitted
transition stops without accepting. Following [AroraBarak09], chapter 2, time bounds apply to every
branch, including rejecting ones. `RunsInTime` bounds transitions out of running configurations,
so halted self-loops do not consume additional time. Function computation is defined only for
deterministic machines.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `Step`: the one-step relation on configurations
* `RunPath`: finite relation series of steps
* `ComputationPath`: a run path starting at the initial configuration
* `Accepts`: some computation halts with output `[true]`
* `RunsInTime`: every branch stops within the bound

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

/-- Once a run path is halted, its configuration stays unchanged. -/
lemma last_eq_of_head_halted (p : ntm.RunPath input) (h : p.head.Halted) : p.last = p.head := by
  induction p using RelSeries.inductionOn' with
  | singleton c => rfl
  | snoc p c hc ih =>
    have hp : p.last = p.head := ih (by simpa using h)
    have hh : p.last.Halted := hp ▸ (show p.head.Halted by simpa using h)
    simpa using ((step_of_halt hh).mp hc).trans hp

/-- The last configuration equals any earlier halted configuration. -/
lemma last_eq_of_halted (p : ntm.RunPath input) (i : Fin (p.length + 1))
    (h : (p i).Halted) : p.last = p i := by
  simpa using last_eq_of_head_halted (p.drop i) (by simpa using h)

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

/-- Some computation on `input` halts with output `[true]`. -/
def Accepts (ntm : MultiTapeNTM k Bool State) (input : List Bool) : Prop :=
  ∃ p : ntm.ComputationPath input, p.last.Halted ∧ p.last.output = [true]

/-- Every branch stops within `t` steps: after at least `t` steps, only halted self-loops are
permitted. A branch with no permitted transition has already stopped and need not be extended. -/
def RunsInTime (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) (t : ℕ) : Prop :=
  ∀ p : ntm.ComputationPath input, t ≤ p.time →
    ∀ c, ntm.Step p.last c → p.last.Halted

/-- A time bound can be increased. -/
lemma RunsInTime.mono {input : List Symbol} {t t' : ℕ}
    (h : ntm.RunsInTime input t) (ht : t ≤ t') : ntm.RunsInTime input t' :=
  fun p hp ↦ h p (ht.trans hp)

end MultiTapeNTM

end Turing
