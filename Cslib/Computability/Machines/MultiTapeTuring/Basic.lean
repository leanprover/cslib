/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Pim Spelier, Daan van Gent
-/

module

public import Cslib.Foundations.Data.BiTape
public import Cslib.Foundations.Data.RelatesInSteps

-- TODO create a "common file"
public import Cslib.Computability.Machines.SingleTapeTuring.Basic

public import Mathlib.Data.Nat.PartENat

@[expose] public section

/-!
# Multi-Tape Turing Machines

Defines Turing machines with `k` tapes (bidirectionally infinite, `BiTape`) containing symbols
from `Option α` for a finite alphabet `α` (where `none` is the blank symbol).

## Important Declarations

We define a number of structures related to Turing machine computation:

* `Stmt`: the write and movement operations a TM can do in a single step.
* `SingleTapeTM`: the TM itself.
* `Cfg`: the configuration of a TM, including internal and tape state.
* `TimeComputable f`: a TM for computing `f`, packaged with a bound on runtime.
* `PolyTimeComputable f`: `TimeComputable f` packaged with a polynomial bound on runtime.

We also provide ways of constructing polynomial-runtime TMs

* `PolyTimeComputable.id`: computes the identity function
* `PolyTimeComputable.comp`: computes the composition of polynomial time machines

## TODOs


-/

open Cslib Relation

namespace Turing

open BiTape StackTape

variable {α : Type}

variable {k : ℕ}

/--
A `k`-tape Turing machine
over the alphabet of `Option α` (where `none` is the blank `BiTape` symbol).
-/
structure MultiTapeTM k α where
  /-- Inhabited instance for the alphabet -/
  [αInhabited : Inhabited α]
  /-- Finiteness of the alphabet -/
  [αFintype : Fintype α]
  /-- type of state labels -/
  (Λ : Type)
  /-- finiteness of the state type -/
  [ΛFintype : Fintype Λ]
  /-- Initial state -/
  (q₀ : Λ)
  /-- Transition function, mapping a state and a head symbol to a `Stmt` to invoke,
  and optionally the new state to transition to afterwards (`none` for halt) -/
  (M : Λ → (Fin k → Option α) → ((Fin k → (SingleTapeTM.Stmt α)) × Option Λ))

namespace MultiTapeTM

section Cfg

/-!
## Configurations of a Turing Machine

This section defines the configurations of a Turing machine,
the step function that lets the machine transition from one configuration to the next,
and the intended initial and final configurations.
-/

variable (tm : MultiTapeTM k α)

instance : Inhabited tm.Λ := ⟨tm.q₀⟩

instance : Fintype tm.Λ := tm.ΛFintype

instance inhabitedStmt : Inhabited (SingleTapeTM.Stmt α) := inferInstance

/--
The configurations of a Turing machine consist of:
an `Option`al state (or none for the halting state),
and a `BiTape` representing the tape contents.
-/
structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.Λ
  /-- the BiTape contents -/
  tapes : Fin k → BiTape α
deriving Inhabited

/-- The step function corresponding to a `MultiTapeTM`. -/
@[simp]
def step : tm.Cfg → Option tm.Cfg
  | ⟨none, _⟩ =>
    -- If in the halting state, there is no next configuration
    none
  | ⟨some q, tapes⟩ =>
    -- If in state q', perform look up in the transition function
    match tm.M q (fun i => (tapes i).head) with
    -- and enter a new configuration with state q'' (or none for halting)
    -- and tape updated according to the Stmt
    | ⟨stmts, q'⟩ => some ⟨q', fun i =>
        ((tapes i).write (stmts i).symbol).optionMove (stmts i).movement⟩

/-- Any number of positive steps run from a halting configuration lead to `none`. -/
@[simp, scoped grind =]
lemma step_iter_none_eq_none (tapes : Fin k → BiTape α) (n : ℕ) :
    (Option.bind · tm.step)^[n + 1] (some ⟨none, tapes⟩) = none := by
  rw [Function.iterate_succ_apply]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih]
    simp [step]

/-- A collection of tapes where the first tape (if it exists)
contains `s` -/
def first_tape (s : List α) : Fin k → BiTape α
  | ⟨0, _⟩ => BiTape.mk₁ s
  | ⟨_, _⟩ => default

/--
The initial configuration corresponding to a list in the input alphabet.
Note that the entries of the tape constructed by `BiTape.mk₁` are all `some` values.
This is to ensure that distinct lists map to distinct initial configurations.
-/
def initCfg (s : List α) : tm.Cfg :=
  ⟨some tm.q₀, first_tape s⟩

def initCfgTapes (tapes : Fin k → BiTape α) : tm.Cfg :=
  ⟨some tm.q₀, tapes⟩

/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
def haltCfg (s : List α) : tm.Cfg :=
  ⟨none, first_tape s⟩

def haltCfgTapes (tapes : Fin k → BiTape α) : tm.Cfg :=
  ⟨none, tapes⟩

/--
The space used by a configuration is the space used by its tape.
-/
def Cfg.space_used (cfg : tm.Cfg) : ℕ := ∑ i, (cfg.tapes i).space_used

lemma Cfg.space_used_step {tm : MultiTapeTM k α} (cfg cfg' : tm.Cfg)
    (hstep : tm.step cfg = some cfg') : cfg'.space_used ≤ cfg.space_used + k := by
  obtain ⟨_ | q, tapes⟩ := cfg
  · simp [step] at hstep
  · simp only [step] at hstep
    generalize hM : tm.M q (fun i => (tapes i).head) = result at hstep
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

/--
The `TransitionRelation` corresponding to a `MultiTapeTM k α`
is defined by the `step` function,
which maps a configuration to its next configuration, if it exists.
-/
@[scoped grind =]
def TransitionRelation (tm : MultiTapeTM k α) (c₁ c₂ : tm.Cfg) : Prop := tm.step c₁ = some c₂

def TransformsTapesInTime
    (tm : MultiTapeTM k α)
    (tapes tapes' : Fin k → BiTape α)
    (t : ℕ) : Prop :=
  RelatesInSteps tm.TransitionRelation ⟨some tm.q₀, tapes⟩ ⟨none, tapes'⟩ t

def TransformsTapesWithinTime
    (tm : MultiTapeTM k α)
    (tapes tapes' : Fin k → BiTape α)
    (t : ℕ) : Prop :=
  RelatesWithinSteps tm.TransitionRelation ⟨some tm.q₀, tapes⟩ ⟨none, tapes'⟩ t

def TransformsTapes
    (tm : MultiTapeTM k α)
    (tapes tapes' : Fin k → BiTape α) : Prop :=
  ∃ t, tm.TransformsTapesInTime tapes tapes' t

@[scoped grind =]
lemma relatesInSteps_iff_step_iter_eq_some
    (tm : MultiTapeTM k α)
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
      cases h : (Option.bind · tm.step)^[t] cfg₁
      · grind
      · rename_i cfg'
        use cfg'
        grind

/-- If a Turing machine transforms tapes to tapes₁, then tapes₁ is uniquely determined. -/
lemma transformsTapes_unique (tm : MultiTapeTM k α)
    (tapes tapes₁ tapes₂ : Fin k → BiTape α)
    (h1 : tm.TransformsTapes tapes tapes₁)
    (h2 : tm.TransformsTapes tapes tapes₂) :
    tapes₁ = tapes₂ := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  unfold TransformsTapesInTime at ht1 ht2
  rw [relatesInSteps_iff_step_iter_eq_some] at ht1 ht2
  rcases Nat.lt_trichotomy t1 t2 with hlt | heq | hgt
  · -- `t1 < t2` is a contradiction because if we halt at `t1` steps
    -- we cannot compute "some" after `t2` steps
    obtain ⟨t', ht2_eq⟩ := Nat.exists_eq_add_of_lt hlt
    rw [ht2_eq] at ht2
    rw [show t1 + t' + 1 = (t' + 1) + t1 by omega] at ht2
    rw [Function.iterate_add_apply] at ht2
    grind
  · rw [heq] at ht1
    subst heq
    simp_all only [step, Option.some.injEq, Cfg.mk.injEq, true_and]
  · -- Symmetric to the case `t1 < t2`
    obtain ⟨t', ht1_eq⟩ := Nat.exists_eq_add_of_lt hgt
    rw [ht1_eq] at ht1
    rw [show t2 + t' + 1 = (t' + 1) + t2 by omega] at ht1
    rw [Function.iterate_add_apply] at ht1
    grind

-- TODO we can actually make it computable, but we have to go a different route
-- via iterated steps
public noncomputable def eval (tm : MultiTapeTM k α) (tapes : Fin k → BiTape α) :
    Part (Fin k → BiTape α) :=
  ⟨∃ tapes', tm.TransformsTapes tapes tapes', fun h => h.choose⟩

-- TODO this is a simple consequence of relatesInSteps_iff_configurations_eq_some, maybe not needed.
lemma configurations_of_transformsTapesInTime
    (tm : MultiTapeTM k α)
    (tapes tapes' : Fin k → BiTape α)
    (t : ℕ)
    (h_transforms : tm.TransformsTapesInTime tapes tapes' t) :
    (Option.bind · tm.step)^[t] (tm.initCfgTapes tapes) =
      some (tm.haltCfgTapes tapes') := by
  simp [TransformsTapesInTime] at h_transforms
  apply (relatesInSteps_iff_step_iter_eq_some tm (tm.initCfgTapes tapes) ⟨none, tapes'⟩ t).mp
  simpa using h_transforms

@[scoped grind =]
lemma eval_iff_exists_steps_iter_eq_some
    {tm : MultiTapeTM k α}
    {tapes tapes' : Fin k → BiTape α} :
    tm.eval tapes = some tapes' ↔
      ∃ t : ℕ, (Option.bind · tm.step)^[t] (tm.initCfgTapes tapes) =
          some (tm.haltCfgTapes tapes') := by
  constructor
  · simp only [Part.coe_some, Part.eq_some_iff, eval]
    intro ⟨h_x, h_tapes_eq⟩
    simp at h_tapes_eq
    obtain ⟨tapes'', h_choose⟩ := h_x
    let tapes'' := h_choose.choose
    use tapes''
    obtain ⟨t, h_transforms⟩ := h_choose
    rw [← relatesInSteps_iff_step_iter_eq_some]
    sorry
  · sorry

/-- A proof of `tm` outputting `l'` on input `l`. -/
def Outputs (tm : MultiTapeTM k α) (l l' : List α) : Prop :=
  ReflTransGen tm.TransitionRelation (initCfg tm l) (haltCfg tm l')

/-- A proof of `tm` outputting `l'` on input `l` in at most `m` steps. -/
def OutputsWithinTime (tm : MultiTapeTM k α) (l l' : List α) (m : ℕ) :=
  RelatesWithinSteps tm.TransitionRelation (initCfg tm l) (haltCfg tm l') m

-- /--
-- This lemma bounds the size blow-up of the output of a Turing machine.
-- It states that the increase in length of the output over the input is bounded by the runtime.
-- This is important for guaranteeing that composition of polynomial time Turing machines
-- remains polynomial time, as the input to the second machine
-- is bounded by the output length of the first machine.
-- -/
-- lemma output_length_le_input_length_add_time (tm : MultiTapeTM k α) (l l' : List α) (t : ℕ)
--     (h : tm.OutputsWithinTime l l' t) :
--     l'.length ≤ max 1 l.length + k * t := by
--   obtain ⟨steps, hsteps_le, hevals⟩ := h
--   grind [hevals.apply_le_apply_add (Cfg.space_used tm)
--       fun a b hstep ↦ Cfg.space_used_step a b (Option.mem_def.mp hstep)]

end MultiTapeTM

end Turing
