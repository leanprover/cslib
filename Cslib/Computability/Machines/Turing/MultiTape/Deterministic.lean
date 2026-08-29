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
* `spaceUsed`: the number of tape cells touched by work tape heads, our main space measure;
    the shared `spaceUsedOfCfgs` read at a step index
* `step_iff`: the inherited `Step` is the graph of `step`
* `runPath`: the machine's own run, as a computation path
* `computesInExactTimeAndSpace_iff_runFrom`: the inherited `ComputesInExactTimeAndSpace`, stated
    by step index rather than by computation path
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
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`. -/
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).outS

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input := tm.step^[t] cfg

@[simp]
lemma runFrom_zero {cfg : Cfg k Symbol State input} :
    tm.runFrom cfg 0 = cfg := by
  simp [runFrom]

lemma runFrom_succ_eq_step {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t := by
  simp [runFrom, Function.iterate_succ_apply]

lemma runFrom_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) := by
  simp [runFrom, Function.iterate_succ_apply']

lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg := by
  induction n with
  | zero => rfl
  | succ d ih =>
    rw [runFrom_succ_eq_step', ih, step_of_halt h]

lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q => exact workTapePos_apply_le _ c i

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  visitedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- The space used up to step `t` is the space touched by the configurations up to step `t`. -/
lemma spaceUsed_eq_spaceUsedOfCfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = spaceUsedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) := rfl

end Space

open Cfg


/-! ## Determinism

`MultiTapeTM` extends `MultiTapeNTM`, so `Step`, `ComputationPath` and the `Computes` notions
already apply to it; only the facts below are specific to having a transition function. They say
that there is no choice to make: `Step` is the graph of `step`, so a computation path can only
follow `runFrom`, and `runPath` shows there is one of every length.
-/

/-- `Step` is the relation `step` induces: from each configuration there is exactly one step. -/
@[simp]
theorem step_iff {c c' : Cfg k Symbol State input} : tm.Step c c' ↔ c' = tm.step c := by
  cases hq : c.state <;> simp [MultiTapeNTM.Step, step, hq]

/-- The configurations the machine passes through form a chain of steps. -/
lemma isChain_map_range (cfg : Cfg k Symbol State input) (t : ℕ) :
    ((List.range (t + 1)).map (tm.runFrom cfg)).IsChain tm.Step := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [List.getElem_map, List.getElem_range]
  rw [runFrom_succ_eq_step']
  exact step_iff.mpr rfl

/-- The machine's own run for `t` steps, as a computation path. -/
def runPath (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    tm.ComputationPath input where
  cfgs := (List.range (t + 1)).map (tm.runFrom (tm.initCfg input))
  last := tm.runFrom (tm.initCfg input) t
  isChainFromTo :=
    { isChain := isChain_map_range _ t
      ne_nil := by simp
      head_eq := by rw [List.head_map]; simp
      getLast_eq := by
        rw [← Option.some_inj, ← List.getLast?_eq_some_getLast, List.range_succ, List.map_append]
        simp }

@[simp]
lemma runPath_time (input : List Symbol) (t : ℕ) : (tm.runPath input t).time = t := by
  simp [MultiTapeNTM.ComputationPath.time, runPath]

@[simp]
lemma runPath_last (input : List Symbol) (t : ℕ) :
    (tm.runPath input t).last = tm.runFrom (tm.initCfg input) t := rfl

@[simp]
lemma runPath_space (input : List Symbol) (t : ℕ) :
    (tm.runPath input t).space = tm.spaceUsed (tm.initCfg input) t := by
  simp [MultiTapeNTM.ComputationPath.space, runPath, spaceUsed_eq_spaceUsedOfCfgs]

/-- A computation path of `tm` has no choice but to follow `runFrom`. -/
lemma path_getElem {p : tm.ComputationPath input} (i : ℕ) (h : i < p.cfgs.length) :
    p.cfgs[i] = tm.runFrom (tm.initCfg input) i := by
  induction i with
  | zero => simpa using p.isChainFromTo.getElem_zero
  | succ n ih =>
    have hstep := List.isChain_iff_getElem.mp p.isChainFromTo.isChain n h
    rw [step_iff.mp hstep, ih (by omega), ← runFrom_succ_eq_step']

/-- A path visiting `t + 1` configurations takes `t` steps. -/
lemma path_length {p : tm.ComputationPath input} : p.cfgs.length = p.time + 1 := by
  have := p.isChainFromTo.length_pos
  simp only [MultiTapeNTM.ComputationPath.time]
  omega

lemma path_cfgs {p : tm.ComputationPath input} :
    p.cfgs = (List.range (p.time + 1)).map (tm.runFrom (tm.initCfg input)) := by
  refine List.ext_getElem (by simp [path_length]) fun i h₁ h₂ => ?_
  simpa using path_getElem i h₁

/-- It ends where `tm` is after that many steps. -/
lemma path_last {p : tm.ComputationPath input} :
    p.last = tm.runFrom (tm.initCfg input) p.time := by
  have h := p.isChainFromTo.getElem_length_sub_one
  rw [path_getElem _ (by have := p.isChainFromTo.length_pos; omega)] at h
  exact h.symm

/-- Its space is the space `tm` uses over the same number of steps. -/
lemma path_space {p : tm.ComputationPath input} :
    p.space = tm.spaceUsed (tm.initCfg input) p.time := by
  rw [MultiTapeNTM.ComputationPath.space, path_cfgs, ← spaceUsed_eq_spaceUsedOfCfgs]

/-- `tm` has exactly one computation path of each length, so `ComputesInExactTimeAndSpace`,
inherited from `MultiTapeNTM`, is the direct statement about `runFrom` and `spaceUsed` at step
`t`. -/
theorem computesInExactTimeAndSpace_iff_runFrom {input output : List Symbol} {t s : ℕ} :
    tm.ComputesInExactTimeAndSpace input output t s ↔
      (tm.runFrom (tm.initCfg input) t).state = none ∧
      (tm.runFrom (tm.initCfg input) t).output = output ∧
      tm.spaceUsed (tm.initCfg input) t = s := by
  constructor
  · rintro ⟨p, hhalt, hout, rfl, hspace⟩
    rw [path_last] at hhalt hout
    rw [path_space] at hspace
    exact ⟨hhalt, hout, hspace⟩
  · rintro ⟨hhalt, hout, hspace⟩
    exact ⟨tm.runPath input t, by simpa using hhalt, by simpa using hout, by simp,
      by simpa using hspace⟩

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
  unfold runFrom
  induction t generalizing cfg₁ cfg₂ with
  | zero => simp
  | succ t ih =>
    rw [RelatesInSteps.succ_iff, Function.iterate_succ_apply']
    constructor
    · grind [step_iff]
    · intro h_runFrom
      use tm.step^[t] cfg₁
      grind [step_iff]


end MultiTapeTM

end Turing
