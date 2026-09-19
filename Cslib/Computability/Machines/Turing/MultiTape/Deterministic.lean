/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan
-/

module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Data.Set.BoolIndicator
public import Cslib.Foundations.Data.RelatesInSteps
public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Deterministic Multi-Tape Turing Machines

A deterministic machine is a `MultiTapeNTM` whose transition relation permits exactly one action
for each state and tuple of symbols. The configuration and tape conventions are described in
`Cslib.Computability.Machines.Turing.MultiTape.Configuration`.

## Design

`MultiTapeTM` extends `MultiTapeNTM` by a unique-existence proof. This follows the same pattern as
Mathlib's `MetricSpace` extending `PseudoMetricSpace` by an additional law: definitions and results
that do not need the extra law belong to the parent. In particular, `Step`, `initCfg`,
`ComputationPath` and the computation predicates are inherited without a translation.

The transition function `tr` is derived from `Tr` by selecting its unique result, following
Mathlib's `forall_existsUnique_iff` and CSLib's `LTS.chooseFLTS`. There is no separate stored
transition function. This uses classical choice, so the evaluator is noncomputable. `ofTr`
constructs a machine from a function, and `tr_ofTr` recovers that function by simplification.
The simp lemmas `tr_iff` and `step_iff` turn relational statements into function equations.

`runFrom` iterates the derived step function. `runPath` is that run in the inherited path type,
starting at any configuration. Its space is definitionally `spaceUsed`. Every path of a
deterministic machine consists of these same iterates, which gives the characterization
`computesInExactTimeAndSpace_iff_runFrom` of the shared computation predicate.

## Important Declarations

* `MultiTapeTM`: a nondeterministic machine with exactly one action per situation
* `ofTr`, `tr`: construction from a function and the derived function API
* `runFrom`, `runPath`: execution by iteration and its shared computation path
* `spaceUsed`: the space of that path
* `computesInExactTimeAndSpace_iff_runFrom`: the shared predicate expressed using iteration
* `ComputableInTimeAndSpace`: existence of a deterministic machine within input-indexed bounds
* `ComputableInTimeAndSpaceOfLength`: bounds indexed by the encoded input length
* `DecidableInTimeAndSpace`: decidability of a set within time and space bounds

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
  /-- Every situation permits exactly one action. -/
  deterministic (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    ∃! action, Tr q input work action

instance : CoeOut (MultiTapeTM k Symbol State) (MultiTapeNTM k Symbol State) :=
  ⟨MultiTapeTM.toMultiTapeNTM⟩

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

/-- A deterministic machine is determined by its underlying nondeterministic machine. -/
@[ext]
theorem ext {tm tm' : MultiTapeTM k Symbol State}
    (h : tm.toMultiTapeNTM = tm'.toMultiTapeNTM) : tm = tm' := by
  cases tm
  cases tm'
  cases h
  rfl

/-- The unique action permitted by the transition relation. This derived function uses classical
choice; `tr_ofTr` recovers a supplied transition function by simplification. -/
noncomputable def tr (tm : MultiTapeTM k Symbol State) (q : State) (input : Option Symbol)
    (work : Fin k → Option Symbol) : Action k Symbol State :=
  (tm.deterministic q input work).choose

/-- The transition relation is the graph of its derived transition function. -/
@[simp, scoped grind =]
lemma tr_iff {q : State} {input : Option Symbol} {work : Fin k → Option Symbol}
    {action : Action k Symbol State} : tm.Tr q input work action ↔ tm.tr q input work = action :=
  ⟨fun h => ((tm.deterministic q input work).choose_spec.2 action h).symm,
    fun h => h ▸ (tm.deterministic q input work).choose_spec.1⟩

/-- The derived transition is permitted by the relation. -/
lemma tr_tr (tm : MultiTapeTM k Symbol State) (q : State) (input : Option Symbol)
    (work : Fin k → Option Symbol) : tm.Tr q input work (tm.tr q input work) :=
  tr_iff.mpr rfl

/-- Construct a deterministic machine from an initial state and transition function. -/
def ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State) :
    MultiTapeTM k Symbol State where
  q₀ := q₀
  Tr q input work action := tr q input work = action
  deterministic _ _ _ := by simp

/-- Extracting the transition of `ofTr` recovers the supplied function. -/
@[simp]
lemma tr_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    (ofTr q₀ tr).tr q input work = tr q input work :=
  tr_iff.mp rfl

section Cfg

/-!
## Stepping a Turing Machine

This section defines the step function that lets the machine transition from one configuration to
the next, and the configuration reached after a number of steps. Configurations themselves are
defined in `Cslib.Computability.Machines.Turing.MultiTape.Configuration`.
-/

/-- The step function corresponding to a `MultiTapeTM`. -/
noncomputable def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`. -/
noncomputable def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output

/-- The inherited step relation is the graph of `step`. -/
@[simp, scoped grind =]
lemma step_iff {c c' : Cfg k Symbol State input} : tm.Step c c' ↔ tm.step c = c' := by
  cases h : c.state <;> simp [MultiTapeNTM.Step, step, h, eq_comm]

/-- Taking the derived step gives a step of the underlying nondeterministic machine. -/
lemma step_step (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) :
    tm.Step c (tm.step c) := step_iff.mpr rfl

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg :=
  (MultiTapeNTM.step_of_halt h).mp (tm.step_step cfg)

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
noncomputable def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input :=
  tm.step^[t] cfg

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

/-- Running `a + b` steps equals running `b` steps from the configuration reached after `a`. -/
lemma runFrom_add (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.runFrom cfg (a + b) = tm.runFrom (tm.runFrom cfg a) b := by
  unfold runFrom
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- If a function `f` that maps the configurations of one TM to those of another one commutes with
their `step` function, then it also commutes with their `runFrom` function. -/
lemma runFrom_comm_of_step {k' : ℕ} {State' : Type*} {input input' : List Symbol}
    {tm : MultiTapeTM k Symbol State} {tm' : MultiTapeTM k' Symbol State'}
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstep : ∀ cfg, tm'.step (f cfg) = f (tm.step cfg))
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm'.runFrom (f cfg) n = f (tm.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (hstep c).symm) n cfg).symm

/-- Running from a halting configuration stays at that configuration. -/
@[simp]
lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg :=
  Function.iterate_fixed (step_of_halt h) n

/-- Nothing changes after the machine has halted. -/
lemma runFrom_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    tm.runFrom cfg t = tm.runFrom cfg τ := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [runFrom_add, runFrom_of_halt _ hhalt]

/-- Every halted run has a first halting time no later than the supplied one. -/
lemma exists_minimal_halting_time
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ)
    (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u ≤ t, (tm.runFrom cfg u).state = none ∧ ∀ s < u, (tm.runFrom cfg s).state ≠ none := by
  classical
  have hex : ∃ n, (tm.runFrom cfg n).state = none := ⟨t, hhalt⟩
  exact ⟨Nat.find hex, Nat.find_min' hex hhalt, Nat.find_spec hex,
    fun s hs => Nat.find_min hex hs⟩

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg k Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- The work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 :=
  (tm.step_step c).workTapePos_le i

end Cfg

/-- The configurations reached by iteration form a chain of steps. -/
lemma isChain_map_range (cfg : Cfg k Symbol State input) (t : ℕ) :
    ((List.range (t + 1)).map (tm.runFrom cfg)).IsChain tm.Step := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [List.getElem_map, List.getElem_range]
  rw [runFrom_succ_eq_step']
  exact tm.step_step _

/-- The machine's run from any configuration, as a path of its underlying nondeterministic
machine. -/
noncomputable def runPath (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (t : ℕ) : tm.ComputationPath input cfg where
  cfgs := (List.range (t + 1)).map (tm.runFrom cfg)
  last := tm.runFrom cfg t
  isChainFromTo :=
    { isChain := isChain_map_range cfg t
      ne_nil := by simp
      head_eq := by rw [List.head_map]; simp
      getLast_eq := by
        rw [← Option.some_inj, ← List.getLast?_eq_some_getLast, List.range_succ, List.map_append]
        simp }

@[simp]
lemma runPath_time (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runPath cfg t).time = t := by
  simp [MultiTapeNTM.ComputationPath.time, runPath]

@[simp]
lemma runPath_cfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runPath cfg t).cfgs = (List.range (t + 1)).map (tm.runFrom cfg) := rfl

@[simp]
lemma runPath_last (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runPath cfg t).last = tm.runFrom cfg t := rfl

/-- Every configuration of a deterministic computation is fixed by its index. -/
lemma getElem_eq_runFrom {cfg : Cfg k Symbol State input} (p : tm.ComputationPath input cfg)
    (n : ℕ) (h : n < p.cfgs.length) : p.cfgs[n] = tm.runFrom cfg n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [runFrom_succ_eq_step', ← ih (by omega)]
    exact (step_iff.mp (p.step_getElem n h)).symm

/-- A deterministic path consists precisely of the iterates of `step`. -/
lemma cfgs_eq_runPath {cfg : Cfg k Symbol State input} (p : tm.ComputationPath input cfg) :
    p.cfgs = (tm.runPath cfg p.time).cfgs := by
  apply List.ext_getElem
  · simpa using p.length_eq_time_add_one
  · intro n hn hn'
    simpa using getElem_eq_runFrom p n hn

/-- A deterministic path is the unique run of its length from its starting configuration. -/
lemma eq_runPath {cfg : Cfg k Symbol State input} (p : tm.ComputationPath input cfg) :
    p = tm.runPath cfg p.time := MultiTapeNTM.ComputationPath.ext (cfgs_eq_runPath p)

/-- The endpoint of a deterministic path is the corresponding iterate. -/
lemma last_eq_runFrom {cfg : Cfg k Symbol State input} (p : tm.ComputationPath input cfg) :
    p.last = tm.runFrom cfg p.time := by
  simpa using getElem_eq_runFrom p p.time
    (by rw [p.length_eq_time_add_one]; omega)

section Space

/-- Positions visited by work tape `i` during the run from `cfg` for `t` steps. -/
noncomputable def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    Finset ℤ := (tm.runPath cfg t).visited i

/-- The number of cells visited on one work tape during a run. -/
noncomputable def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.runPath cfg t).spaceByTape i

/-- Space usage is the space of the machine's path, with the same measure as any nondeterministic
computation. -/
noncomputable def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ :=
  (tm.runPath cfg t).space

@[simp]
lemma runPath_space (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runPath cfg t).space = tm.spaceUsed cfg t := rfl

/-- Space is the sum of the space used by each work tape. -/
lemma spaceUsed_eq_sum (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = ∑ i, tm.spaceUsedByTape cfg t i := rfl

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := (tm.runPath cfg t).space_zero_tapes h_zero

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ tm.spaceUsed cfg t :=
  (tm.runPath cfg t).spaceByTape_le_space i

/-- Space usage is read from the configurations traversed by the run. -/
lemma spaceUsed_eq_spaceUsedOfCfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = spaceUsedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) := rfl

end Space

open Cfg

/-- One step appends the symbol (optionally) emitted by that step to the output tape. -/
@[simp]
lemma step_output (cfg : Cfg k Symbol State input) :
    (tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList := by
  unfold step outputSymbol Action.apply
  cases cfg.state <;> simp

/-- The output does not change after the machine has halted. -/
lemma runFrom_output_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    (tm.runFrom cfg t).output = (tm.runFrom cfg τ).output := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [runFrom_add, runFrom_of_halt _ hhalt]

/-- Any predicate on computations can be checked on the unique run of each length. This gives a
single bridge from all the inherited computation predicates to iteration. -/
theorem computesSuchThat_iff_runPath {input output : List Symbol}
    {P : tm.ComputationPath input → Prop} :
    tm.ComputesSuchThat input output P ↔
      ∃ t, (tm.runFrom (tm.initCfg input) t).Halted ∧
        (tm.runFrom (tm.initCfg input) t).output = output ∧
        P (tm.runPath (tm.initCfg input) t) := by
  constructor
  · rintro ⟨p, hhalt, hout, hP⟩
    refine ⟨p.time, ?_⟩
    simpa only [← last_eq_runFrom p, ← eq_runPath p] using And.intro hhalt (And.intro hout hP)
  · rintro ⟨t, hhalt, hout, hP⟩
    exact ⟨tm.runPath (tm.initCfg input) t, hhalt, hout, hP⟩

/-- The shared exact-time/space predicate can be expressed using the unique deterministic run. -/
theorem computesInExactTimeAndSpace_iff_runFrom {input output : List Symbol} {t s : ℕ} :
    tm.ComputesInExactTimeAndSpace input output t s ↔
      (tm.runFrom (tm.initCfg input) t).Halted ∧
      (tm.runFrom (tm.initCfg input) t).output = output ∧
      tm.spaceUsed (tm.initCfg input) t = s := by
  simp only [MultiTapeNTM.ComputesInExactTimeAndSpace, computesSuchThat_iff_runPath,
    runPath_time, runPath_space]
  constructor
  · rintro ⟨_, hhalt, hout, rfl, hspace⟩
    exact ⟨hhalt, hout, hspace⟩
  · rintro ⟨hhalt, hout, hspace⟩
    exact ⟨t, hhalt, hout, rfl, hspace⟩

/-- A function is computable within the input-indexed bounds by a machine with binary alphabet
and finitely many states. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    tm.ComputesFunInTimeAndSpace encIn encOut f t s

/-- There exists a binary Turing machine with finitely many states that, for every input `a`,
computes `encOut (f a)` from `encIn a` in at most `t (encIn a).length` steps,
using at most `s (encIn a).length` work-tape cells. -/
abbrev ComputableInTimeAndSpaceOfLength {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Computability is monotone in the resource bounds. -/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

/-- The Boolean indicator function of a set, as defined by Mathlib. -/
noncomputable abbrev indicator {α : Type*} (L : Set α) : α → Bool := L.boolIndicator

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b => [b], by intro a b h; simpa using h⟩ t s

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
    · grind
    · intro h_runFrom
      use tm.step^[t] cfg₁
      grind

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`
if its state is `none` at step `t` and non-none at step `t - 1`.
Note that every Turing machine has to perform at least one step to halt. -/
noncomputable def haltsAtStep (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    Bool :=
  (tm.runFrom (tm.initCfg input) t).state.isNone &&
  !(tm.runFrom (tm.initCfg input) (t - 1)).state.isNone

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiTapeTM k Symbol State}
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
    have halts₁ : (tm.runFrom (tm.initCfg input) t₁).state = none := by
      simp [haltsAtStep] at h_halts₁
      exact h_halts₁.left
    have halts₂ : (tm.runFrom (tm.initCfg input) (d + t₁)).state ≠ none := by
      grind [haltsAtStep, runFrom]
    refine absurd ?_ halts₂
    rw [Nat.add_comm, runFrom_add, tm.runFrom_of_halt _ halts₁]
    exact halts₁

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `tm.runFrom_add`. -/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg k Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.runFrom cfg (t + 1) = cfg) :
    ∀ t', (tm.runFrom cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.runFrom cfg (n * (t + 1)) = cfg := by
    intro n
    unfold runFrom
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed heq n
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.runFrom cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    obtain ⟨tΔ , htΔ⟩ := Nat.exists_eq_add_of_le hle
    rw [htΔ, tm.runFrom_add]
    simp [hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing
