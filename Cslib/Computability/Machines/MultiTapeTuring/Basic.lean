/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- TODO create a "common file"?
public import Cslib.Computability.Machines.SingleTapeTuring.Basic

public import Mathlib.Data.Part

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Multi-Tape Turing Machines

Defines Turing machines with `k` tapes (bidirectionally infinite, `BiTape`) containing symbols
from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the blank symbol).

## Design

The design of the multi-tape Turing machine follows the one for single-tape Turing machines.
With multiple tapes, it is not immediatly clear how to define the function computed by a Turing
machine. For a single-tape Turing machine, function composition follows easily from composition
of configurations. For multi-tape machines, we focus on composition of tape configurations
(cf. `MultiTapeTM.eval`) and defer the decision of how to define the function computed by a
Turing machine to a later stage.

Since these Turing machines are deterministic, we base the definition of semantics on the sequence
of configurations instead of reachability in a configuration relation, although equivalence
between these two notions is proven.

## Important Declarations

We define a number of structures related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `Cfg`: the configuration of a TM, including internal state and the state of the tapes
* `UsesSpaceUntilStep`: a TM uses at most space `s` when run for up to `t` steps
* `TrasformsTapesInExactTime`: a TM transforms tapes `tapes` to `tapes'` in exactly `t` steps
* `TransformsTapesInTime`: a TM transforms tapes `tapes` to `tapes'` in up to `t` steps
* `TransformsTapes`: a TM transforms tapes `tapes` to `tapes'` in some number of steps
* `TransformsTapesInTimeAndSpace`: a TM transforms tapes `tapes` to `tapes'` in up to `t` steps
  and uses at most `s` space

There are multiple ways to talk about the behaviour of a multi-tape Turing machine:

* `MultiTapeTM.configs`: a sequence of configurations by execution step
* `TransformsTapes`: a TM transforms initial tapes `tapes` and halts with tapes `tapes'`
* `MultiTapeTM.eval`: executes a TM on initial tapes `tapes` and returns the resulting tapes if it
  eventually halts

## TODOs

* Define sequential composition of multi-tape Turing machines.
* Define different kinds of tapes (input-only, output-only, oracle, etc) and how they influence
   how space is counted.
* Define the notion of a multi-tape Turing machine computing a function.

-/

open Cslib Relation

namespace Turing

open BiTape StackTape

variable {Symbol : Type}

variable {k : ℕ}

/--
A `k`-tape Turing machine
over the alphabet of `Option Symbol` (where `none` is the blank `BiTape` symbol).
-/
public structure MultiTapeTM k Symbol [Inhabited Symbol] [Fintype Symbol] where
  /-- type of state labels -/
  (State : Type)
  /-- finiteness of the state type -/
  [stateFintype : Fintype State]
  /-- initial state -/
  (q₀ : State)
  /-- transition function, mapping a state and a tuple of head symbols to a `Stmt` to invoke
  for each tape and optionally the new state to transition to afterwards (`none` for halt) -/
  (tr : State → (Fin k → Option Symbol) → ((Fin k → (SingleTapeTM.Stmt Symbol)) × Option State))

namespace MultiTapeTM

section Cfg

/-!
## Configurations of a Turing Machine

This section defines the configurations of a Turing machine,
the step function that lets the machine transition from one configuration to the next,
and the intended initial and final configurations.
-/

variable [Inhabited Symbol] [Fintype Symbol] (tm : MultiTapeTM k Symbol)

instance : Inhabited tm.State := ⟨tm.q₀⟩

instance : Fintype tm.State := tm.stateFintype

instance inhabitedStmt : Inhabited (SingleTapeTM.Stmt Symbol) := inferInstance


/--
The configurations of a Turing machine consist of:
an `Option`al state (or none for the halting state),
and a `BiTape` representing the tape contents.
-/
@[ext]
public structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.State
  /-- the BiTape contents -/
  tapes : Fin k → BiTape Symbol
deriving Inhabited

/-- The step function corresponding to a `MultiTapeTM`. -/
public def step : tm.Cfg → Option tm.Cfg
  | ⟨none, _⟩ =>
    -- If in the halting state, there is no next configuration
    none
  | ⟨some q, tapes⟩ =>
    -- If in state q, perform look up in the transition function
    match tm.tr q (fun i => (tapes i).head) with
    -- and enter a new configuration with state q' (or none for halting)
    -- and tapes updated according to the Stmt
    | ⟨stmts, q'⟩ => some ⟨q', fun i =>
        ((tapes i).write (stmts i).symbol).optionMove (stmts i).movement⟩

/-- Any number of positive steps run from a halting configuration lead to `none`. -/
@[simp, scoped grind =]
public lemma step_iter_none_eq_none (tapes : Fin k → BiTape Symbol) (n : ℕ) :
    (Option.bind · tm.step)^[n + 1] (some ⟨none, tapes⟩) = none := by
  rw [Function.iterate_succ_apply]
  induction n with
  | zero => simp [step]
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih]
    simp [step]

/-- A collection of tapes where the first tape contains `s` -/
public def firstTape (s : List Symbol) : Fin k → BiTape Symbol
  | ⟨0, _⟩ => BiTape.mk₁ s
  | ⟨_, _⟩ => default

/--
The initial configuration corresponding to a list in the input alphabet.
Note that the entries of the tape constructed by `BiTape.mk₁` are all `some` values.
This is to ensure that distinct lists map to distinct initial configurations.
-/
@[simp]
public def initCfg (s : List Symbol) : tm.Cfg :=
  ⟨some tm.q₀, firstTape s⟩

/-- Create an initial configuration given a tuple of tapes. -/
@[simp]
public def initCfgTapes (tapes : Fin k → BiTape Symbol) : tm.Cfg :=
  ⟨some tm.q₀, tapes⟩

/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
@[simp]
public def haltCfg (s : List Symbol) : tm.Cfg :=
  ⟨none, firstTape s⟩

/-- The final configuration of a Turing machine given a tuple of tapes. -/
@[simp]
public def haltCfgTapes (tapes : Fin k → BiTape Symbol) : tm.Cfg :=
  ⟨none, tapes⟩

/-- The sequence of configurations of the Turing machine starting with initial state and
given tapes at step `t`.
If the Turing machine halts, it will eventually get and stay `none` after reaching the halting
configuration. -/
public def configs (tapes : Fin k → BiTape Symbol) (t : ℕ) : Option tm.Cfg :=
  (Option.bind · tm.step)^[t] (tm.initCfgTapes tapes)



-- TODO shouldn't this be spaceUsed? (If yes, also change it in SingleTapeTM)

/--
The space used by a configuration is the sum of the space used by its tapes.
-/
public def Cfg.space_used (cfg : tm.Cfg) : ℕ := ∑ i, (cfg.tapes i).space_used

/--
The space used by a configuration grows by at most `k` each step.
-/
public lemma Cfg.space_used_step (cfg cfg' : tm.Cfg)
    (hstep : tm.step cfg = some cfg') : cfg'.space_used ≤ cfg.space_used + k := by
  obtain ⟨_ | q, tapes⟩ := cfg
  · simp [step] at hstep
  · simp only [step] at hstep
    generalize h_tr : tm.tr q (fun i => (tapes i).head) = result at hstep
    obtain ⟨stmts, q''⟩ := result
    injection hstep with hstep
    subst hstep
    simp only [space_used]
    trans ∑ i : Fin k, ((tapes i).space_used + 1)
    · refine Finset.sum_le_sum fun i _ => ?_
      unfold BiTape.optionMove
      grind [BiTape.space_used_write, BiTape.space_used_move]
    · simp [Finset.sum_add_distrib]

end Cfg

open Cfg

variable [Inhabited Symbol] [Fintype Symbol]

/--
The `TransitionRelation` corresponding to a `MultiTapeTM k Symbol`
is defined by the `step` function,
which maps a configuration to its next configuration, if it exists.
-/
@[scoped grind =]
public def TransitionRelation (tm : MultiTapeTM k Symbol) (c₁ c₂ : tm.Cfg) : Prop :=
  tm.step c₁ = some c₂

/-- A proof that the Turing machine `tm` transforms tapes `tapes` to `tapes'` in exactly
`t` steps. -/
public def TransformsTapesInExactTime
    (tm : MultiTapeTM k Symbol)
    (tapes tapes' : Fin k → BiTape Symbol)
    (t : ℕ) : Prop :=
  RelatesInSteps tm.TransitionRelation (tm.initCfgTapes tapes) (tm.haltCfgTapes tapes') t

/-- A proof that the Turing machine `tm` transforms tapes `tapes` to `tapes'` in up to
`t` steps. -/
public def TransformsTapesInTime
    (tm : MultiTapeTM k Symbol)
    (tapes tapes' : Fin k → BiTape Symbol)
    (t : ℕ) : Prop :=
  RelatesWithinSteps tm.TransitionRelation (tm.initCfgTapes tapes) (tm.haltCfgTapes tapes') t

/-- The Turing machine `tm` transforms tapes `tapes` to `tapes'`. -/
public def TransformsTapes
    (tm : MultiTapeTM k Symbol)
    (tapes tapes' : Fin k → BiTape Symbol) : Prop :=
  ∃ t, tm.TransformsTapesInExactTime tapes tapes' t

/-- A proof that the Turing machine `tm` uses at most space `s` when run for up to `t` steps
on initial tapes `tapes`. -/
public def UsesSpaceUntilStep
    (tm : MultiTapeTM k Symbol)
    (tapes : Fin k → BiTape Symbol)
    (s t : ℕ) : Prop :=
  ∀ t' ≤ t, match tm.configs tapes t' with
    | none => true
    | some cfg => cfg.space_used ≤ s

/-- A proof that the Turing machine `tm` transforms tapes `tapes` to `tapes'` in exactly `t` steps
and uses at most `s` space. -/
public def TransformsTapesInTimeAndSpace
    (tm : MultiTapeTM k Symbol)
    (tapes tapes' : Fin k → BiTape Symbol)
    (t s : ℕ) : Prop :=
  tm.TransformsTapesInExactTime tapes tapes' t ∧
    tm.UsesSpaceUntilStep tapes s t

/-- This lemma translates between the relational notion and the iterated step notion. The latter
can be more convenient especially for deterministic machines as we have here. -/
@[scoped grind =]
public lemma relatesInSteps_iff_step_iter_eq_some
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
    · grind only [TransitionRelation, = Option.bind_some]
    · intro h_configs
      cases h : (Option.bind · tm.step)^[t] cfg₁ with
      | none => grind
      | some cfg' =>
        use cfg'
        grind

/-- The Turing machine `tm` halts after exactly `t` steps on initial tapes `tapes`. -/
public def haltsAtStep
    (tm : MultiTapeTM k Symbol) (tapes : Fin k → BiTape Symbol) (t : ℕ) : Bool :=
  match (tm.configs tapes t) with
  | some ⟨none, _⟩ => true
  | _ => false

/-- If a Turing machine halts, the time step is uniquely determined. -/
public lemma halting_step_unique
    {tm : MultiTapeTM k Symbol}
    {tapes : Fin k → BiTape Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep tapes t₁)
    (h_halts₂ : tm.haltsAtStep tapes t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    -- this is a contradiction.
    unfold haltsAtStep configs at h_halts₁ h_halts₂
    split at h_halts₁ <;> try contradiction
    next tapes' h_iter_t₁ =>
      rw [Nat.add_comm t₁ (d + 1), Function.iterate_add_apply, h_iter_t₁,
          step_iter_none_eq_none (tm := tm) tapes' d] at h_halts₂
      simp at h_halts₂

/-- At the halting step, the configuration sequence of a Turing machine is still `some`. -/
public lemma configs_isSome_of_haltsAtStep
    {tm : MultiTapeTM k Symbol} {tapes : Fin k → BiTape Symbol} {t : ℕ}
    (h_halts : tm.haltsAtStep tapes t) :
    (tm.configs tapes t).isSome := by
  grind [haltsAtStep]

/-- The Turing machine `tm` eventually halts starting from any initial tape configuration. -/
public def HaltsOn (tm : MultiTapeTM k Symbol) (tapes : Fin k → BiTape Symbol) : Prop :=
  ∃ t, tm.haltsAtStep tapes t

/-- Execute the Turing machine `tm` on initial tapes `tapes` and return the resulting tapes
if it eventually halts. -/
public def eval (tm : MultiTapeTM k Symbol) (tapes : Fin k → BiTape Symbol) :
    Part (Fin k → BiTape Symbol) :=
  ⟨∃ t, tm.haltsAtStep tapes t,
    fun h => ((tm.configs tapes (Nat.find h)).get
      (configs_isSome_of_haltsAtStep (Nat.find_spec h))).tapes⟩

/-- Evaluating a Turing machine on a tuple of tapes `tapes` has a value `tapes'` if and only if
it transforms `tapes` into `tapes'`. -/
@[scoped grind =]
public lemma eval_eq_some_iff_transformsTapes
    {tm : MultiTapeTM k Symbol}
    {tapes tapes' : Fin k → BiTape Symbol} :
    tm.eval tapes = .some tapes' ↔ tm.TransformsTapes tapes tapes' := by
  simp only [eval, Part.eq_some_iff, Part.mem_mk_iff]
  constructor
  · intro ⟨h_dom, h_get⟩
    use Nat.find h_dom
    rw [TransformsTapesInExactTime, relatesInSteps_iff_step_iter_eq_some]
    rw [← configs, Option.eq_some_iff_get_eq]
    use configs_isSome_of_haltsAtStep (Nat.find_spec h_dom)
    ext1
    · simp
      grind [haltsAtStep, Nat.find_spec h_dom]
    · exact h_get
  · intro ⟨t, h_iter⟩
    rw [TransformsTapesInExactTime, relatesInSteps_iff_step_iter_eq_some] at h_iter
    rw [← configs] at h_iter
    have h_halts_at_t : tm.haltsAtStep tapes t := by simp [haltsAtStep, h_iter]
    let h_halts : ∃ t, tm.haltsAtStep tapes t := ⟨t, h_halts_at_t⟩
    use h_halts
    have h_eq : Nat.find h_halts = t := halting_step_unique (Nat.find_spec h_halts) h_halts_at_t
    simp [h_eq, h_iter]

/-- Execute the Turing machine `tm` that always halts on initial tapes `tapes` and
return the resulting tapes. -/
@[simp]
public def eval_tot
  (tm : MultiTapeTM k Symbol)
  (h_alwaysHalts : ∀ tapes, tm.HaltsOn tapes)
  (tapes : Fin k → BiTape Symbol) :
  Fin k → BiTape Symbol :=
(tm.eval tapes).get (h_alwaysHalts tapes)

end MultiTapeTM

end Turing
