/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Computability.Language
public import Cslib.Foundations.Data.BiTape
public import Cslib.Foundations.Data.RelatesInSteps
public import Cslib.Computability.Machines.TuringCommon

/-!
# Multi-Tape Turing Machines

Defines Turing machines with a read-only input tape, `k` work tapes and one write-only output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, the input and output tapes do not count towards the space usage of
the machine. The space usage of the work tapes is the number of cells the head accessed.

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

-/

@[expose] public section

open Cslib Relation

namespace Turing

open BiTape StackTape

variable {Symbol : Type}

variable {k : ℕ}

/-- The output of the transition function. -/
structure TransitionOut (k : ℕ) (Symbol State : Type) where
  /-- The movement (attempt) of the input head. -/
  inputMove : Option Dir
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  stmts : Fin k → Stmt Symbol
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
  /-- transition function, mapping a state and a tuple of head symbols to a movement for the
  input head, actions on the work tape, optionally a symbol to output and the successor state -/
  tr : State → (Fin (k + 1) → Option Symbol) → TransitionOut k Symbol State

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
structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.State
  /-- the tape contents -/
  tapes : Fin (k + 1) → BiTape Symbol
  /-- the output so far -/
  output : List Symbol
deriving Inhabited

/-- Applies the actions / statements to the tapes.
The input tape is handled specially: The machine can read one empty cell outside of the input,
but any attempted movement beyond that results in no movement. -/
def applyTapeActions
    (inputMove : Option Dir)
    (stmts : Fin k → Stmt Symbol)
    (tapes : Fin (k + 1) → BiTape Symbol) :
    Fin (k + 1) → BiTape Symbol
  | ⟨0, _⟩ => match inputMove, tapes ⟨0, by omega⟩ with
    | none, t => t
    | some .left, t => if t.left.toList = [] ∧ t.head = none then t else t.move_left
    | some .right, t => if t.right.toList = [] ∧ t.head = none then t else t.move_right
  | ⟨i + 1, _⟩ => let s := stmts ⟨i, by omega⟩
    ((tapes ⟨i + 1, by omega⟩).write s.symbol).optionMove s.movement

/-- The output of the transition function applied to a configuration. -/
def transitionOutput : tm.Cfg → Option (TransitionOut k Symbol tm.State)
  | ⟨none, _, _⟩ => none -- halting state
  | ⟨some q, tapes, _⟩ => some (tm.tr q (fun i => (tapes i).head))

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : tm.Cfg) : Option tm.Cfg :=
  (tm.transitionOutput cfg).map fun {inputMove, stmts, outS, q'} =>
    let output := match outS with
      | none => cfg.output
      | some s => cfg.output ++ [s]
    ⟨q', applyTapeActions inputMove stmts cfg.tapes, output⟩

/-- Any number of positive steps run from a halting configuration lead to `none`. -/
@[simp, scoped grind =]
lemma step_iter_none_eq_none (tapes : Fin (k + 1) → BiTape Symbol) (out : List Symbol) (n : ℕ) :
    (Option.bind · tm.step)^[n + 1] (some ⟨none, tapes, out⟩) = none := by
  rw [Function.iterate_succ_apply]
  induction n with
  | zero => rfl
  | succ n ih => grind [Function.iterate_succ_apply']

/-- A collection of tapes where the first tape contains `s` -/
def firstTape (s : List Symbol) : Fin k → BiTape Symbol
  | ⟨0, _⟩ => BiTape.mk₁ s
  | ⟨_, _⟩ => default

/-- The initial configuration corresponding to a list in the input alphabet. -/
@[simp]
def initCfg (s : List Symbol) : tm.Cfg :=
  ⟨some tm.q₀, firstTape s, []⟩

/-- The sequence of configurations of the Turing machine starting from `cfg`.
If the Turing machine halts, it will eventually get and stay `none` after reaching the halting
configuration. -/
def configs (cfg : tm.Cfg) (t : ℕ) : Option tm.Cfg :=
  (Option.bind · tm.step)^[t] cfg

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

variable [Inhabited Symbol] [Fintype Symbol] (tm : MultiTapeTM k Symbol)

/-- Convert an "optional movement" to an integer where positive is "right". -/
@[simp, grind]
def OptionDirToInt : Option Dir → ℤ
  | some .left => -1
  | none => 0
  | some .right => 1

/-- The movements of the work tape heads after configuration `cfg`. -/
def headMovements (cfg : tm.Cfg) : Fin k → ℤ
  | i => match tm.transitionOutput cfg with
      | some tro => OptionDirToInt (tro.stmts ⟨i, by omega⟩).movement
      | none => 0

/-- The head positions of the work tapes as a function of the number of steps, relative to
the starting position in `cfg`. -/
def headPositions (cfg : tm.Cfg) (t : ℕ) : Fin k → ℤ
  | i => ∑ t' ∈ Finset.range t, (tm.configs cfg t').elim 0 (tm.headMovements · i)

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : tm.Cfg) (t : ℕ) (i : Fin k) : ℕ :=
  let positions := (Finset.range (t + 1)).image (fun t' => tm.headPositions cfg t' i)
  have ne := Finset.image_nonempty.mpr ⟨0, by simp⟩
  (positions.max' ne - positions.min' ne).toNat + 1

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

@[scoped grind .]
lemma OptionDirToInt_bound (d : Option Dir) :
    -1 ≤ OptionDirToInt d ∧ OptionDirToInt d ≤ 1 := by
  rcases d with _ | d
  · decide
  · rcases d <;> decide

/-- A single step moves each work tape head by at most one cell. -/
lemma step_head_movement_bound (cfg : tm.Cfg) (t : ℕ) (i : Fin k) :
    -1 ≤ (tm.configs cfg t).elim 0 (tm.headMovements · i)
      ∧ (tm.configs cfg t).elim 0 (tm.headMovements · i) ≤ 1 := by
  unfold headMovements
  dsimp
  rcases h : tm.configs cfg t <;>
  grind

/-- The head position changes by the corresponding head movement on each step. -/
lemma headPositions_succ (cfg : tm.Cfg) (t : ℕ) (i : Fin k) :
    tm.headPositions cfg (t + 1) i
      = tm.headPositions cfg t i + (tm.configs cfg t).elim 0 (tm.headMovements · i) := by
  simp only [headPositions, Finset.sum_range_succ]

/--
Inserting one new point `a`, adjacent to an existing point `q` of `s`, widens the spanned
interval `max' - min'` by at most one cell.
-/
lemma span_insert_le {s S : Finset ℤ} (hs : s.Nonempty) (hS : S.Nonempty)
    {a q : ℤ} (hSeq : S = insert a s) (hq : q ∈ s) (h1 : a ≤ q + 1) (h2 : q ≤ a + 1) :
    (S.max' hS - S.min' hS).toNat ≤ (s.max' hs - s.min' hs).toNat + 1 := by
  subst hSeq
  rw [Finset.max'_insert _ _ hs, Finset.min'_insert _ _ hs]
  have hm := Finset.min'_le _ _ hq
  have hM := Finset.le_max' _ _ hq
  grind

/-- The number of cells touched by a single work tape grows by at most one each step. -/
lemma spaceUsedByTape_succ_le (cfg : tm.Cfg) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg (t + 1) i ≤ tm.spaceUsedByTape cfg t i + 1 := by
  unfold spaceUsedByTape
  have hs := tm.headPositions_succ cfg t i
  have step_bound := tm.step_head_movement_bound cfg t i
  apply Nat.add_le_add_right
  refine span_insert_le _ _
    (by rw [Finset.range_add_one, Finset.image_insert])
    (by exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_self t)))
    (by grind)
    (by grind)

/--
The space used by a configuration grows by at most `k` each step.
-/
lemma spaceUsed_linear (cfg : tm.Cfg) (t : ℕ) :
    tm.spaceUsed cfg (t + 1) ≤ tm.spaceUsed cfg t + k := by
  calc tm.spaceUsed cfg (t + 1)
      ≤ ∑ i, (tm.spaceUsedByTape cfg t i + 1) :=
        Finset.sum_le_sum fun i _ => tm.spaceUsedByTape_succ_le cfg t i
    _ = (∑ i, tm.spaceUsedByTape cfg t i) + k := by simp [Finset.sum_add_distrib]

end Space

open Cfg

variable [Inhabited Symbol] [Fintype Symbol]

/--
The `TransitionRelation` corresponding to a `MultiTapeTM k Symbol`
is defined by the `step` function,
which maps a configuration to its next configuration, if it exists.
-/
@[scoped grind =]
def TransitionRelation (tm : MultiTapeTM k Symbol) (c₁ c₂ : tm.Cfg) : Prop :=
  tm.step c₁ = some c₂

/-- A proof that the Turing machine `tm` on input `input` outputs `output` in exactly `t` steps
and uses at most `s` space. -/
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
length `n` it uses at most `t n` steps and `s n` space. -/
def ComputesFunInTimeAndSpace
    (tm : MultiTapeTM k Symbol)
    (f : List Symbol → List Symbol)
    (t s : ℕ → ℕ) : Prop :=
  ∀ input, ∃ t' ≤ t input.length, ∃ s' ≤ s input.length,
  ComputesInTimeAndSpace tm input (f input) t' s'

open Classical in
/-- The indicator function of a language. -/
noncomputable def indicator (l : Language Symbol) : List Symbol → List Symbol
  | x => if x ∈ l then [default] else []

/-- A proof that a Turing machine `tm` decides a language `l` with time and space bounds. -/
def DecidesLanguageInTimeAndSpace
    (tm : MultiTapeTM k Symbol)
    (L : Language Symbol)
    (t s : ℕ → ℕ) : Prop :=
  ComputesFunInTimeAndSpace tm (indicator L) t s

/-- This lemma translates between the relational notion and the iterated step notion. The latter
can be more convenient especially for deterministic machines as we have here. -/
@[scoped grind =]
lemma relatesInSteps_iff_step_iter_eq_some
    (tm : MultiTapeTM k Symbol)
    (cfg₁ cfg₂ : tm.Cfg)
    (t : ℕ) :
  RelatesInSteps tm.TransitionRelation cfg₁ cfg₂ t ↔
    (Option.bind · tm.step)^[t] cfg₁ = .some cfg₂ := by
  induction t generalizing cfg₁ cfg₂ with
  | zero => simp
  | succ t ih =>
    rw [RelatesInSteps.succ_iff, Function.iterate_succ_apply']
    constructor
    · grind
    · intro h_configs
      cases h : (Option.bind · tm.step)^[t] cfg₁ with
      | none => grind
      | some cfg' =>
        use cfg'
        grind

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`. -/
def haltsAtStep (tm : MultiTapeTM k Symbol) (input : List Symbol) (t : ℕ) : Bool :=
  match (tm.configs (tm.initCfg input) t) with
  | some ⟨none, _, _⟩ => true
  | _ => false

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
    unfold haltsAtStep configs at h_halts₁ h_halts₂
    rw [Nat.add_comm t₁ (d + 1), Function.iterate_add_apply] at h_halts₂
    grind

/-- At the halting step, the configuration sequence of a Turing machine is still `some`. -/
lemma configs_isSome_of_haltsAtStep
    {tm : MultiTapeTM k Symbol} {input : List Symbol} {t : ℕ}
    (h_halts : tm.haltsAtStep input t) :
    (tm.configs (tm.initCfg input) t).isSome := by
  grind [haltsAtStep]


end MultiTapeTM

end Turing
