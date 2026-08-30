/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Computability.Language
public import Cslib.Foundations.Data.RelatesInSteps
public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Deterministic Multi-Tape Turing Machines

Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one write-only
output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

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

This definition is adapted from the one in [Papadimitriou94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AroraBarak09], Claim 1.4). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

`MultiTapeTM` extends `MultiTapeNTM` with a transition function and the requirement that the
permitted transitions are exactly the ones it prescribes. `Step`, `ComputationPath` and the
`Computes` notions of the nondeterministic machine therefore apply unchanged, and what this file
adds is what follows from there being no choice to make.

## Important Declarations

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself, a `MultiTapeNTM` whose transition relation is a function
* `ofTr`: the machine with a given initial state and transition function
* `runPath`: the machine's own run from a configuration, as a `ComputationPath`
* `runFrom`: the configuration that run ends in, equal to iterating `step` (`runFrom_eq_iterate`)
* `spaceUsed`: the number of tape cells touched by work tape heads, our main space measure;
    the space of that run
* `step_iff`: the inherited `Step` is the graph of `step`
* `computesInExactTimeAndSpace_iff_runFrom`: the inherited `ComputesInExactTimeAndSpace`, stated
    by step index rather than by computation path, via `ComputationPath.cfgs_eq`
* `ComputableInTimeAndSpace`: a proof that there is a multi-tape TM that computes a function
    (on strings) respecting a time and space bound in the input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

There are two ways to talk about the behaviour of a multi-tape Turing machine, and they are
proven to be equivalent.

* `MultiTapeTM.runFrom`: the configuration reached after a given number of execution steps
* `RelatesInSteps tm.Step cfg cfg' t`: a proof that `tm` transforms the configuration
    `cfg` into `cfg'` in exactly `t` steps

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]

-/

@[expose] public section

open Cslib Relation

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*)
    extends MultiTapeNTM k Symbol State where
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State
  /-- the permitted transitions are exactly the one `tr` prescribes -/
  Tr_iff (q : State) (i : Option Symbol) (w : Fin k → Option Symbol)
    (action : Action k Symbol State) : Tr q i w action ↔ action = tr q i w

attribute [simp] MultiTapeTM.Tr_iff

/-- The deterministic machine with initial state `q₀` and transition function `tr`. -/
def MultiTapeTM.ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State) :
    MultiTapeTM k Symbol State where
  q₀ := q₀
  Tr q i w action := action = tr q i w
  tr := tr
  Tr_iff _ _ _ _ := Iff.rfl

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

section Cfg

/-!
## Stepping a Turing Machine

This section defines the step function that lets the machine transition from one configuration to
the next, and the configuration reached after a number of steps. Configurations themselves are
defined in `Cslib.Computability.Machines.Turing.MultiTape.Configuration`.
-/

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  cfg.stepWith fun q => tm.tr q cfg.inputSymbol cfg.workTapeSymbols

/-- `Step` is the relation `step` induces: from each configuration there is exactly one step.
Everything below about a deterministic machine rests on this. -/
@[simp]
theorem step_iff {c c' : Cfg k Symbol State input} : tm.Step c c' ↔ c' = tm.step c :=
  Cfg.stepWith_iff (by simp)

/-- A halted configuration steps to itself, inherited from `MultiTapeNTM`. -/
@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg :=
  (MultiTapeNTM.step_of_halt h).mp (step_iff.mpr rfl)

/-- The machine's own run from `cfg` for `t` steps: it does nothing, or takes one more step. -/
def runPath (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) :
    ℕ → tm.ComputationPath input
  | 0 => .single cfg
  | t + 1 => (tm.runPath cfg t).concat (tm.step (tm.runPath cfg t).last) (step_iff.mpr rfl)

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`: the one its
run ends in. If the Turing machine halts, it will stay at the halting configuration. -/
def runFrom (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) (t : ℕ) :
    Cfg k Symbol State input := (tm.runPath cfg t).last

@[simp]
lemma runPath_last (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runPath cfg t).last = tm.runFrom cfg t := rfl

@[simp]
lemma runFrom_zero {cfg : Cfg k Symbol State input} : tm.runFrom cfg 0 = cfg := rfl

lemma runFrom_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) := by
  simp only [runFrom, runPath, MultiTapeNTM.ComputationPath.concat_last]

/-- The run ends where iterating `step` lands. Building the run says what running *is*; iterating
says how to *do* it, and carries the `Function.iterate` API. -/
theorem runFrom_eq_iterate (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (t : ℕ) : tm.runFrom cfg t = tm.step^[t] cfg := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [runFrom_succ_eq_step', ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

/-- How `runFrom` is evaluated: iterating `step`, rather than building the run it ends. -/
def runFromIter (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) (t : ℕ) :
    Cfg k Symbol State input := tm.step^[t] cfg

@[csimp]
theorem runFrom_eq_runFromIter : @runFrom = @runFromIter := by
  funext k State Symbol input tm cfg t
  exact tm.runFrom_eq_iterate cfg t

@[simp]
lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg := by
  induction n with
  | zero => rfl
  | succ d ih =>
    rw [runFrom_succ_eq_step', ih, step_of_halt h]

end Cfg


open Cfg


/-! ## Determinism

`MultiTapeTM` extends `MultiTapeNTM`, so `Step`, `ComputationPath` and the `Computes` notions
already apply to it; only the facts below are specific to having a transition function. They say
that there is no choice to make: `Step` is the graph of `step`, so a computation path can only
follow `runFrom`, and `runPath` shows there is one of every length.
-/

/-- Its run takes `t` steps. -/
@[simp]
lemma runPath_time (cfg : Cfg k Symbol State input) (t : ℕ) : (tm.runPath cfg t).time = t := by
  induction t with
  | zero => rfl
  | succ n ih => simp [runPath, ih]

/-- Its run starts where it was asked to. -/
@[simp]
lemma runPath_start (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runPath cfg t).start = cfg := by
  induction t with
  | zero => rfl
  | succ n ih => simp [runPath, ih]

/-- Its run passes through the configurations reached after each step. -/
lemma runPath_cfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runPath cfg t).cfgs = (List.range (t + 1)).map (tm.runFrom cfg) := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [runPath, MultiTapeNTM.ComputationPath.concat_cfgs, ih]
    simp [List.range_succ, runFrom_succ_eq_step']

section Space
/-! Space is read off the machine's own run, so it is the space of a `ComputationPath`. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  visitedOfCfgs (tm.runPath cfg t).cfgs i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`: the space of the machine's own run.
-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := (tm.runPath cfg t).space

/-- The space used up to step `t` is the space of the run up to step `t`. -/
@[simp]
lemma runPath_space (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runPath cfg t).space = tm.spaceUsed cfg t := rfl

/-- Space is the sum over the tapes of the cells each head touched. -/
lemma spaceUsed_eq_sum (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = ∑ i, tm.spaceUsedByTape cfg t i := rfl

/-- The space used up to step `t` is the space touched by the configurations up to step `t`. -/
lemma spaceUsed_eq_spaceUsedOfCfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = spaceUsedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) := by
  rw [spaceUsed, MultiTapeNTM.ComputationPath.space, runPath_cfgs]

end Space

/-- `tm` has exactly one computation path of each length, so `ComputesInExactTimeAndSpace`,
inherited from `MultiTapeNTM`, is the direct statement about `runFrom` and `spaceUsed` at step
`t`. -/
theorem computesInExactTimeAndSpace_iff_runFrom {input output : List Symbol} {t s : ℕ} :
    tm.ComputesInExactTimeAndSpace input output t s ↔
      (tm.runFrom (tm.initCfg input) t).state = none ∧
      (tm.runFrom (tm.initCfg input) t).output = output ∧
      tm.spaceUsed (tm.initCfg input) t = s := by
  constructor
  · rintro ⟨p, hstart, hhalt, hout, rfl, hspace⟩
    have hp : p = tm.runPath (tm.initCfg input) p.time :=
      MultiTapeNTM.ComputationPath.eq_of_start_of_time
        (fun h₁ h₂ => (step_iff.mp h₁).trans (step_iff.mp h₂).symm)
        (by simpa using hstart) (by simp)
    rw [hp] at hhalt hout hspace
    exact ⟨by simpa using hhalt, by simpa using hout, by simpa using hspace⟩
  · rintro ⟨hhalt, hout, hspace⟩
    exact ⟨tm.runPath (tm.initCfg input) t, by simp, by simpa using hhalt, by simpa using hout,
      by simp, by simpa using hspace⟩

/-- A proof that the Turing machine `tm` computes the function `f` such that on all inputs of
length `n` it uses at most `t n` steps and `s n` space. It assumes an embedding function
from the input/output alphabet into the machine alphabet.
Note that this does not require the alphabet or state set to be finite. -/
def ComputesFunInTimeAndSpace
    (tm : MultiTapeTM k Symbol State)
    {IOSymbol : Type*}
    (f : List IOSymbol → List IOSymbol)
    (toMachineSymbol : IOSymbol ↪ Symbol)
    (t s : ℕ → ℕ) : Prop :=
  ∀ input, ∃ t' ≤ t input.length, ∃ s' ≤ s input.length,
  tm.ComputesInExactTimeAndSpace (input.map toMachineSymbol) ((f input).map toMachineSymbol) t' s'

/-- The main definition of complexity of multi-tape Turing machines:
A proof that the function `f` is computable by some multi-tape Turing machine `tm` (with finite
work alphabet and finite state set) via an alphabet embedding function `toMachineSymbol`,
such that on all inputs of length `n`, `tm` uses at most `t n` steps and at most `s n` space. -/
def ComputableInTimeAndSpace
    {IOSymbol : Type*}
    (f : List IOSymbol → List IOSymbol)
    (t s : ℕ → ℕ) : Prop :=
  ∃ (k sym state : ℕ) (toMachineSymbol : _) (tm : MultiTapeTM k (Fin sym) (Fin state)),
  ComputesFunInTimeAndSpace tm f toMachineSymbol t s

open Classical in
/-- The indicator function of a language. -/
noncomputable def indicator {Symbol : Type*} [Inhabited Symbol] (L : Language Symbol) :
    List Symbol → List Symbol
  | x => if x ∈ L then [default] else []

/-- A language is decidable in time `t` and space `s` if and only if its indicator function
is computable in time `t` and space `s`. -/
def DecidableInTimeAndSpace
    {IOSymbol : Type} [Inhabited IOSymbol]
    (L : Language IOSymbol)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) t s

/-- This lemma translates between the relational notion and the iterated step notion. The latter
can be more convenient especially for deterministic machines as we have here. -/
@[scoped grind =]
lemma relatesInSteps_iff_runFrom_eq
    (tm : MultiTapeTM k Symbol State)
    (cfg₁ cfg₂ : Cfg k Symbol State input)
    (t : ℕ) :
    RelatesInSteps tm.Step cfg₁ cfg₂ t ↔ tm.runFrom cfg₁ t = cfg₂ := by
  induction t generalizing cfg₁ cfg₂ with
  | zero => simp
  | succ t ih =>
    rw [RelatesInSteps.succ_iff, runFrom_succ_eq_step']
    constructor
    · grind [step_iff]
    · intro h_runFrom
      use tm.runFrom cfg₁ t
      grind [step_iff]


end MultiTapeTM

end Turing
