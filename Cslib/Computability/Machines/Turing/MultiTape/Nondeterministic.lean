/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.RelSeries
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

The transition relation may be empty at a running configuration, so a machine can get stuck. The
computation predicates ask for a path ending in a halted configuration, so a stuck one is not a
witness.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `Step`: the one-step relation on configurations
* `RunPath`: finite relation series of steps
* `ComputationPath`: a run path starting at the initial configuration
* `ComputesSuchThat`: some computation halts, emits a given output and meets a given constraint
* `Computes`, `ComputesInExactTime`, `ComputesInExactSpace`, `ComputesInExactTimeAndSpace`:
    its instances, whose
    bounds all refer to a single computation
* `ComputesFunInTimeAndSpace`: computation of an encoded function within input-indexed bounds
* `ComputableInTimeAndSpace`: existence of a machine satisfying the bounds and an optional predicate

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

/-- A finite nonempty list of configurations joined by steps of `ntm`. -/
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

/-!
## Space usage

The input tape is read-only with bounded head movement, and the output tape is write-only, so we
ignore both for space usage. The space usage is defined as the total number of cells the work tape
heads visited along a run path.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
(including [AroraBarak09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.
-/

/-- The set of positions visited by the head of work tape `i` along a run path. -/
def visitedByTapeHead (p : ntm.RunPath input) (i : Fin k) : Finset ℤ :=
  Finset.univ.image fun n => (p n).workTapePos i

/-- The number of cells touched by the head of work tape `i` along a run path. -/
def spaceUsedByTape (p : ntm.RunPath input) (i : Fin k) : ℕ :=
  (p.visitedByTapeHead i).card

/-- The number of work tape cells touched along a run path. -/
def space (p : ntm.RunPath input) : ℕ := ∑ i, p.spaceUsedByTape i

end RunPath

/-- A run path starting at the initial configuration for `input`. -/
structure ComputationPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol)
    extends toRunPath : ntm.RunPath input where
  /-- the path starts at the initial configuration -/
  head_eq : toRunPath.head = ntm.initCfg input

namespace ComputationPath

/-- The number of steps taken by a computation path. -/
def time (p : ntm.ComputationPath input) : ℕ := RunPath.time p.toRunPath

/-- The number of work tape cells touched along a computation path. -/
def space (p : ntm.ComputationPath input) : ℕ := RunPath.space p.toRunPath

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

/-- A machine computes `f` between the supplied encodings, within input-indexed bounds.
For each input, this requires the existence of a computation path producing the encoded result
within the supplied time and space bounds. -/
def ComputesFunInTimeAndSpace {α β : Type*}
    (ntm : MultiTapeNTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ t' ≤ t a, ∃ s' ≤ s a,
    ntm.ComputesInExactTimeAndSpace (encIn a) (encOut (f a)) t' s'

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {ntm : MultiTapeNTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ}
    (h : ntm.ComputesFunInTimeAndSpace encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ntm.ComputesFunInTimeAndSpace encIn encOut f t' s' := fun a => by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

/-- A function is computable within the input-indexed bounds by a binary machine with finitely
many states. `P` optionally restricts the witnessing machine. By default, every machine is
allowed. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (t s : α → ℕ)
    (P : ∀ {k : ℕ} {State : Type}, MultiTapeNTM k Bool State → Prop := fun _ => True) :
    Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State),
    P ntm ∧ ntm.ComputesFunInTimeAndSpace encIn encOut f t s

/-- Computability is monotone in the resource bounds. -/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    {P : ∀ {k : ℕ} {State : Type}, MultiTapeNTM k Bool State → Prop}
    (h : ComputableInTimeAndSpace f encIn encOut t s P)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' P := by
  obtain ⟨k, State, hfinite, ntm, hP, htm⟩ := h
  exact ⟨k, State, hfinite, ntm, hP, htm.mono ht hs⟩

/-- A machine emits at most one symbol per step, so the encoded result is no longer than its
time bound. -/
theorem ComputableInTimeAndSpace.length_encOut_le {α β : Type*}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {t s : α → ℕ}
    {P : ∀ {k : ℕ} {State : Type}, MultiTapeNTM k Bool State → Prop}
    (h : ComputableInTimeAndSpace f encIn encOut t s P) (a : α) :
    (encOut (f a)).length ≤ t a := by
  obtain ⟨k, State, _, ntm, _, htm⟩ := h
  obtain ⟨t', ht', s', _, p, _, hout, htime, _⟩ := htm a
  have hlen := RunPath.length_output_le p.toRunPath
  rw [hout, p.head_eq] at hlen
  exact le_trans (by simpa [← htime, ComputationPath.time, RunPath.time] using hlen) ht'

end MultiTapeNTM

end Turing
