/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Computability.Language
public import Cslib.Foundations.Data.RelatesInSteps

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

## Important Declarations

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `Cfg`: the configuration of a TM, including internal state, the tapes and the output so far
* `spaceUsed`: the number of work tape cells touched by the head until a certain step
* `TransitionRelation`: the transition relation from one configuration to the next
* `ComputesInTimeAndSpace`: a proof that a TM computes an output from an input in a certain number
    of steps and using a certain number of tape cells
* `ComputesFunInTimeAndSpace`: a proof that a TM computes a function (on strings) respecting a
    time and space bound in the input length
* `DecidesLanguageInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound

There are two ways to talk about the behaviour of a multi-tape Turing machine, and they are
proven to be equivalent.

* `MultiTapeTM.configs`: a sequence of configurations by execution step
* `RelatesInSteps tm.TransitionRelation cfg cfg' t`: a proof that `tm` transforms the configuration
    `cfg` into `cfg'` in exactly `t` steps

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser09]

-/

@[expose] public section

open Cslib Relation

namespace Turing

variable {Symbol : Type*}

variable {k : ℕ}

/-- Possible moves of tape heads. -/
inductive Move
  | left
  | stay
  | right

/-- Translate moves to integer offsets for tape head positions. -/
def Move.toInt : Move → ℤ
  | left => -1
  | stay => 0
  | right => 1

@[scoped grind .]
lemma Move.toInt_bound (m : Move) : -1 ≤ m.toInt ∧ m.toInt ≤ 1 := by
  rcases m with _ | d <;> decide

/-- The output of the transition function. -/
structure TransitionOut (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputMove : Move
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workActions : Fin k → (Option (Option Symbol)) × Move
  /-- An optional symbol to output. -/
  outS : Option Symbol
  /-- The successor state or none to halt. -/
  q' : Option State

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank `BiTape` symbol).
-/
structure MultiTapeTM k Symbol [Inhabited Symbol] [Fintype Symbol] where
  /-- type of state labels -/
  State : Type
  /-- finiteness of the state type -/
  [stateFintype : Fintype State]
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of head symbols
  to a movement for the input head, actions on the work tape, optionally a symbol to output and
  the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
      TransitionOut k Symbol State

namespace MultiTapeTM

section Cfg

/-!
## Configurations of a Turing Machine

This section defines the configurations of a Turing machine,
the step function that lets the machine transition from one configuration to the next,
and the intended initial and final configurations.
-/

variable [Inhabited Symbol] [Fintype Symbol] (tm : MultiTapeTM k Symbol)

/--
The configurations of a Turing machine consist of:
- an `Option`al state (or none for the halting state),
- `BiTape`s representing the tape contents and
- the output so far.
-/
@[ext]
structure Cfg where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.State
  /-- the input -/
  input : List Symbol
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
  /-- the output so far -/
  output : List Symbol
deriving Inhabited

/-- Attempt to move the input tape head.
The machine can only read one empty cell outside of the input,
any attempted movement beyond that results in no movement. -/
@[scoped grind =]
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : Move) : Fin (n + 2) :=
  let p := (pos + m.toInt).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

/-- The symbol currently under the input tape head. -/
@[scoped grind =]
def inputSymbol (cfg : tm.Cfg) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = cfg.input.length + 1 then none
  else cfg.input[cfg.inputPos.val - 1]'(by grind)

@[simp]
lemma inputSymbolInner {cfg : tm.Cfg} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < cfg.input.length) :
    tm.inputSymbol cfg = some cfg.input[p] := by
  simp [inputSymbol, h₁]
  grind

/-- The symbol read by work tape `i`. -/
def workTapeSymbols (cfg : tm.Cfg) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : tm.Cfg) : tm.Cfg :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q =>
    let {inputMove, workActions, outS, q'} := tm.tr q (tm.inputSymbol cfg) (tm.workTapeSymbols cfg)
    {
      state := q',
      input := cfg.input,
      inputPos := moveInputPos cfg.inputPos inputMove,
      workTapes i := match (workActions i).1 with
        | none => cfg.workTapes i
        | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
      workTapePos i := (cfg.workTapePos i) + (workActions i).2.toInt
      output := match outS with
      | none => cfg.output
      | some s => cfg.output ++ [s]
    }

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (s : List Symbol) : tm.Cfg :=
  ⟨some tm.q₀, s, 1, fun _ _ => none, fun _ => 0, []⟩

/-- The sequence of configurations of the Turing machine starting from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def configs (cfg : tm.Cfg) (t : ℕ) : tm.Cfg := tm.step^[t] cfg

/-- Any number of steps run from a halting configuration results in the same configuration. -/
@[simp, scoped grind =]
lemma iter_step_eq_of_halt {cfg : tm.Cfg} {n : ℕ} (h_halt : cfg.state = none) :
    tm.step^[n] cfg = cfg := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, step, h_halt]

/-- The work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : tm.Cfg) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q =>
    have := (tm.tr q (tm.inputSymbol c) (tm.workTapeSymbols c)).workActions i |>.2 |>.toInt_bound
    simp only [add_sub_cancel_left]
    rw [abs_le]
    omega

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

variable [Inhabited Symbol] [Fintype Symbol] (tm : MultiTapeTM k Symbol)

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : tm.Cfg) (t : ℕ) (i : Fin k) : ℕ :=
  ((List.range (t + 1)).map fun t' => (tm.configs cfg t').workTapePos i).toFinset.card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
def spaceUsed (cfg : tm.Cfg) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : tm.Cfg) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- The number of cells touched by a single work tape grows by at most one each step. -/
lemma spaceUsedByTape_le (cfg : tm.Cfg) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ t + 1 := by
  calc
    tm.spaceUsedByTape cfg t i
    _ ≤ ((List.range (t + 1)).map _).length := List.toFinset_card_le _
    _ = t + 1 := by simp

/--
The space used by a computation is bounded linearly by the number of steps.
-/
lemma spaceUsed_linear (cfg : tm.Cfg) (t : ℕ) : tm.spaceUsed cfg t ≤ k * t + k := by
  calc tm.spaceUsed cfg t
      = ∑ i, (tm.spaceUsedByTape cfg t i) := by rfl
    _ ≤ ∑ i, (t + 1) := Finset.sum_le_sum (fun i _ => tm.spaceUsedByTape_le cfg t i)
    _ = k * t + k := by simp [Nat.mul_succ]

end Space

open Cfg

variable [Inhabited Symbol] [Fintype Symbol]

/--
The `TransitionRelation` corresponding to a `MultiTapeTM k Symbol`
is defined by the `step` function,
which maps a configuration to its next configuration, if it exists.
-/
@[scoped grind =]
def TransitionRelation (tm : MultiTapeTM k Symbol) (c₁ c₂ : tm.Cfg) : Prop := tm.step c₁ = c₂

/-- A proof that the Turing machine `tm` on input `input` outputs `output` in at most `t` steps
and uses `s` space. -/
def ComputesInTimeAndSpace
    (tm : MultiTapeTM k Symbol)
    (input output : List Symbol)
    (t s : ℕ) : Prop :=
  ∃ cfg,
  cfg.state = none ∧
  cfg.output = output ∧
  RelatesInSteps tm.TransitionRelation (tm.initCfg input) cfg t ∧
  tm.spaceUsed (tm.initCfg input) t = s

/-- A proof that the Turing machine `tm` computes the function `f` such that on all inputs of
length `n` it uses at most `t n` steps and `s n` space. It assumes an embedding function
from the input/output alphabet into the machine alphabet. -/
def ComputesFunInTimeAndSpace
    {IOSymbol : Type*}
    (tm : MultiTapeTM k Symbol)
    (f : List IOSymbol → List IOSymbol)
    (toMachineSymbol : IOSymbol ↪ Symbol)
    (t s : ℕ → ℕ) : Prop :=
  ∀ input, ∃ t' ≤ t input.length, ∃ s' ≤ s input.length,
  ComputesInTimeAndSpace tm (input.map toMachineSymbol) ((f input).map toMachineSymbol) t' s'

open Classical in
/-- The indicator function of a language. -/
noncomputable def indicator (L : Language Symbol) : List Symbol → List Symbol
  | x => if x ∈ L then [default] else []

/-- A proof that a Turing machine `tm` decides a language `L` with time and space bounds. -/
def DecidesLanguageInTimeAndSpace
    {IOSymbol : Type*} [Inhabited IOSymbol]
    (tm : MultiTapeTM k Symbol)
    (L : Language IOSymbol)
    (toMachineSymbol : IOSymbol ↪ Symbol)
    (t s : ℕ → ℕ) : Prop :=
  ComputesFunInTimeAndSpace tm (indicator L) toMachineSymbol t s

/-- This lemma translates between the relational notion and the iterated step notion. The latter
can be more convenient especially for deterministic machines as we have here. -/
@[scoped grind =]
lemma relatesInSteps_iff_configs_eq
    (tm : MultiTapeTM k Symbol)
    (cfg₁ cfg₂ : tm.Cfg)
    (t : ℕ) :
  RelatesInSteps tm.TransitionRelation cfg₁ cfg₂ t ↔ tm.configs cfg₁ t = cfg₂ := by
  unfold configs
  induction t generalizing cfg₁ cfg₂ with
  | zero => simp
  | succ t ih =>
    rw [RelatesInSteps.succ_iff, Function.iterate_succ_apply']
    constructor
    · grind
    · intro h_configs
      use tm.step^[t] cfg₁
      grind

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`
if its state is `none` at step `t` and non-none at step `t - 1`.
Note that every Turing machine hast to perform at least one step to halt. -/
def haltsAtStep (tm : MultiTapeTM k Symbol) (input : List Symbol) (t : ℕ) : Bool :=
  (tm.configs (tm.initCfg input) t).state.isNone &&
  !(tm.configs (tm.initCfg input) (t - 1)).state.isNone

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiTapeTM k Symbol}
    {input : List Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep input t₁)
    (h_halts₂ : tm.haltsAtStep input t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    have halts₁ : (tm.step^[t₁] (tm.initCfg input)).state = none := by
      simp [haltsAtStep, configs] at h_halts₁
      exact h_halts₁.left
    have halts₂ : (tm.step^[d + t₁] (tm.initCfg input)).state ≠ none := by
      grind [haltsAtStep, configs]
    refine absurd ?_ halts₂
    rw [Function.iterate_add_apply, tm.iter_step_eq_of_halt halts₁]
    exact halts₁

end MultiTapeTM

end Turing
