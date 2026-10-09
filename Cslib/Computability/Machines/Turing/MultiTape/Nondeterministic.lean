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
write-only output tape, their computation paths, and time bounds.

## Design

The design choices for configurations and actions are documented in
`Cslib.Computability.Machines.Turing.MultiTape.Configuration`.

Following [Papadimitriou94], chapter 2.7, a nondeterministic machine is a Turing machine whose
transition function is replaced by a transition relation: `Tr q input work action` holds when `Tr`
relates the state `q` and the read symbols `input` and `work` to `action`.

A halted configuration steps to itself, so once a machine has halted it has a run of every length.
A time bound is therefore an upper bound, with no separate account of the step at which it halted.

The transition relation may be empty at a running configuration. Such a configuration has no
successor configuration and is called stuck.

Time bounds apply to every computation path, regardless of its outcome. `RunsInTime input t`
requires every path of at least `t` steps to end in a halted configuration. A path that gets stuck
after `u` steps therefore requires a bound strictly greater than `u`. Function computation and
decidability are defined only for deterministic machines.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `Step`: the one-step relation on configurations
* `RunPath`: finite relation series of steps
* `ComputationPath`: a run path starting at the initial configuration
* `RunsInTime`: every computation path of at least the given length ends in a halted
  configuration

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

/-- The one-step relation on configurations. A halted configuration steps only to itself. A running
configuration steps by applying any action related to its state and read symbols by `Tr`. -/
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

/-- A nonempty list of configurations joined by steps of `ntm`. -/
abbrev RunPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :=
  RelSeries {(c, c') | ntm.Step (input := input) c c'}

namespace RunPath

/-- The output only grows along a run path. -/
lemma length_output_mono (p : ntm.RunPath input) :
    Monotone fun i ↦ (p i).output.length := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have : ntm.Step (p i.castSucc) (p i.succ) := p.step i
  grind [Step, Action.apply_output]

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

/-- Every computation path on `input` of at least `t` steps ends in a halted configuration.
A path ending in a stuck configuration must have fewer than `t` steps. -/
def RunsInTime (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) (t : ℕ) : Prop :=
  ∀ p : ntm.ComputationPath input, t ≤ p.time → p.last.Halted

/-- A time bound can be increased. -/
lemma RunsInTime.mono {input : List Symbol} {t t' : ℕ}
    (h : ntm.RunsInTime input t) (ht : t ≤ t') : ntm.RunsInTime input t' :=
  fun p hp ↦ h p (ht.trans hp)

end MultiTapeNTM

end Turing
