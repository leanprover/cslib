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
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Cslib.Computability.Machines.Turing.MultiTape.Space

/-!
# Deterministic Multi-Tape Turing Machines

A deterministic Turing machine is a nondeterministic machine whose transition relation has exactly
one action for every combination of state and symbols read. From the transition relation it derives
a transition function `tr` and a function `step` which maps each configuration to its unique
successor configuration (a halted configuration maps to itself).

The design choices for configurations and actions are documented in
`Cslib.Computability.Machines.Turing.MultiTape.Configuration`.

## Important Declarations

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeNTM.IsDeterministic`: the transition relation relates every state and tuple of read
    symbols to exactly one action
* `MultiTapeTM`: the TM itself
* `tr`, `ofTr`: the derived transition function and construction from a function
* `step`, `runFrom`: the successor configuration and iteration of this function
* `MultiTapeNTM.RunPath.ofDeterministic`, `MultiTapeNTM.ComputationPath.ofDeterministic`:
    paths of a given length from an arbitrary or initial configuration
* `Computes`: the machine halts with the given output on an input
* `ComputesSuchThat`: computation satisfying a predicate on the machine and input
* `ComputesFunSuchThat`: function computation satisfying such a predicate for each argument
* `ComputableSuchThat`: such a machine exists with binary alphabet and finitely many states
* `ComputesInTime` and `ComputesFunInTime`: computation within a time bound
* `ComputableInTime`: computability by a finite-state binary machine within a time bound
* `ComputesInSpace`: the machine produces an output within a space bound
* `ComputesFunInSpace`: function computation within an input-indexed space bound
* `ComputableInSpace`: computability by a finite-state binary machine within a space bound
* `DecidableInSpace`: the Boolean indicator of a set is computable within a space bound
* `ComputesInTimeAndSpace`: the machine produces an output within the shared resource bounds
* `ComputesFunInTimeAndSpace`: function computation with the shared time and space bounds
* `ComputableInTimeAndSpace`: such a machine exists with binary alphabet and finitely many states.
* `ComputableInTimeAndSpaceOfLength`: the specialization to bounds on encoded input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- Every state and tuple of read symbols is related to exactly one action by `ntm`'s transition
relation. -/
def MultiTapeNTM.IsDeterministic (ntm : MultiTapeNTM k Symbol State) : Prop :=
  ∀ (q : State) (input : Option Symbol) (work : Fin k → Option Symbol),
    ∃! action, ntm.Tr q input work action

/-- Adapting a deterministic machine gives a deterministic machine. -/
lemma MultiTapeNTM.IsDeterministic.adapt {ntm : MultiTapeNTM k Symbol State} {k' : ℕ}
    {readIn : Option Symbol → (Fin k' → Option Symbol) → Option Symbol}
    {readWork : (Fin k' → Option Symbol) → Fin k → Option Symbol}
    {act : (Fin k' → Option Symbol) → Action k Symbol State → Action k' Symbol State}
    (h : ntm.IsDeterministic) : (ntm.adapt readIn readWork act).IsDeterministic := fun q inp work =>
  (h q (readIn inp work) (readWork work)).elim fun a ha hu =>
    ⟨act work a, ⟨a, ha, rfl⟩, fun _ ⟨b, hb, hab⟩ => hab ▸ congrArg (act work) (hu b hb)⟩

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*)
    extends MultiTapeNTM k Symbol State where
  /-- Every state and tuple of read symbols is related to exactly one action by the transition
  relation. -/
  deterministic : toMultiTapeNTM.IsDeterministic

instance : CoeOut (MultiTapeTM k Symbol State) (MultiTapeNTM k Symbol State) :=
  ⟨MultiTapeTM.toMultiTapeNTM⟩

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

/-- The deterministic machine `tm` with its output writes erased. -/
abbrev eraseOutput (tm : MultiTapeTM k Symbol State) : MultiTapeTM k Symbol State :=
  ⟨tm.toMultiTapeNTM.eraseOutput, tm.deterministic.adapt⟩

/-- The unique action related to the given state and read symbols by `Tr`. -/
noncomputable def tr (tm : MultiTapeTM k Symbol State) (q : State) (input : Option Symbol)
    (work : Fin k → Option Symbol) : Action k Symbol State :=
  (tm.deterministic q input work).choose

/-- `Tr` relates a state and read symbols to an action exactly when `tr` returns that action. -/
@[simp, scoped grind =]
lemma tr_iff {q : State} {input : Option Symbol} {work : Fin k → Option Symbol}
    {action : Action k Symbol State} : tm.Tr q input work action ↔ tm.tr q input work = action :=
  ⟨fun h => ((tm.deterministic q input work).choose_spec.2 action h).symm,
    fun h => h ▸ (tm.deterministic q input work).choose_spec.1⟩

/-- Construct a deterministic machine from an initial state and transition function. -/
def ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State) :
    MultiTapeTM k Symbol State where
  q₀ := q₀
  Tr q input work action := tr q input work = action
  deterministic _ _ _ := by simp

/-- The initial state of `ofTr` is the supplied one. -/
@[simp]
lemma q₀_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State) :
    (ofTr q₀ tr).q₀ = q₀ :=
  rfl

/-- Extracting the transition of `ofTr` recovers the supplied function. -/
@[simp]
lemma tr_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    (ofTr q₀ tr).tr q input work = tr q input work :=
  tr_iff.mp rfl

/-!
## Stepping a Turing Machine

The step function lets the machine transition from one configuration to the next, and `runFrom`
gives the configuration reached after a number of steps. Configurations themselves are defined in
`Cslib.Computability.Machines.Turing.MultiTape.Configuration`.
-/

private lemma existsUnique_step (cfg : Cfg k Symbol State input) :
    ∃! cfg', tm.Step cfg cfg' := by
  unfold MultiTapeNTM.Step
  cases cfg.state <;> simp

/-- The unique successor configuration related to `cfg` by the inherited step relation. -/
noncomputable def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  (show ∃! cfg', tm.Step cfg cfg' from by exact existsUnique_step cfg).choose

/-- `Step` relates `c` to `c'` exactly when `step c = c'`. -/
@[simp, scoped grind =]
lemma step_iff {c c' : Cfg k Symbol State input} : tm.Step c c' ↔ tm.step c = c' := by
  unfold step
  exact (ExistsUnique.choose_eq_iff _).symm

/-- A running configuration takes the action selected by the transition function. -/
lemma step_of_state {cfg : Cfg k Symbol State input} {q : State} (h : cfg.state = some q) :
    tm.step cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by
  apply step_iff.mp
  simp [MultiTapeNTM.Step, h]

/-- The input head after a live step. -/
public lemma step_inputPos_of_state {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) :
    (tm.step cfg).inputPos =
      moveInputPos cfg.inputPos (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputTape := by
  rw [step_of_state h, Action.apply_inputPos]

/-- A work tape after a live step. -/
public lemma step_workTapes_of_state {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) (i : Fin k) :
    (tm.step cfg).workTapes i =
      match (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes i |>.1 with
      | none => cfg.workTapes i
      | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s := by
  rw [step_of_state h]
  rfl

/-- A work tape head after a live step. -/
public lemma step_workTapePos_of_state {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) (i : Fin k) :
    (tm.step cfg).workTapePos i =
      cfg.workTapePos i + ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes i).2 := by
  rw [step_of_state h]
  rfl

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg :=
  step_iff.mp ((MultiTapeNTM.step_of_halt h).mpr rfl)

/-- A configuration map commuting with the step functions on running configurations is a
homomorphism from the running steps of `tm` to the steps of `tm'`. -/
@[simps! apply]
def runningStepHom {k' : ℕ} {State' : Type*} {input' : List Symbol}
    {tm' : MultiTapeTM k' Symbol State'}
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (h : ∀ c, ¬c.Halted → tm'.step (f c) = f (tm.step c)) :
    (tm.runningStepRel input).Hom (tm'.stepRel input') where
  toFun := f
  map_rel' {c _} hc := step_iff.mpr ((h c hc.1).trans (congrArg f (step_iff.mp hc.2)))

end MultiTapeTM

namespace MultiTapeNTM

variable {tm : MultiTapeTM k Symbol State} {input : List Symbol}

/-- The path of the first `t` steps from `cfg`. -/
noncomputable def RunPath.ofDeterministic (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) : tm.RunPath input where
  length := t
  toFun n := tm.step^[n.val] cfg
  step n := by simp [MultiTapeTM.step_iff, Function.iterate_succ_apply']

/-- Every deterministic run path is the canonical path from its head for its duration. -/
lemma RunPath.eq_ofDeterministic (p : tm.RunPath input) :
    p = .ofDeterministic tm p.head p.time := by
  refine RelSeries.ext rfl ?_
  change p.toFun = fun i ↦ tm.step^[i.val] p.head
  refine funext (Fin.induction rfl fun i ih ↦ ?_)
  simpa [Function.iterate_succ_apply'] using
    (MultiTapeTM.step_iff.mp (p.step i)).symm.trans (congrArg tm.step ih)

/-- The path of the first `t` steps on `input`, starting at the initial configuration. -/
noncomputable def ComputationPath.ofDeterministic (tm : MultiTapeTM k Symbol State)
    (input : List Symbol) (t : ℕ) : tm.ComputationPath input :=
  ⟨RunPath.ofDeterministic tm (tm.initCfg input) t, rfl⟩

/-- Every deterministic computation path is the canonical path for its duration. -/
lemma ComputationPath.eq_ofDeterministic (p : tm.ComputationPath input) :
    p = .ofDeterministic tm input p.time := by
  rcases p with ⟨p, hp⟩
  congr 1
  exact (RunPath.eq_ofDeterministic p).trans (by rw [hp]; rfl)

/-- Deterministic run paths from the same configuration are prefixes of one another: the shorter one
is the longer one, cut at its length. -/
lemma RunPath.eq_take {p q : tm.RunPath input} (hhead : p.head = q.head) (h : p.length ≤ q.length) :
    p = q.take ⟨p.length, Nat.lt_succ_of_le h⟩ := by
  refine p.eq_ofDeterministic.trans ((eq_ofDeterministic (q.take _)).trans ?_).symm
  rw [RelSeries.head_take, hhead]
  rfl

/-- Every computation prefix ends at a configuration of any halted computation path. -/
lemma ComputationPath.last_mem_of_halted (p : tm.ComputationPath input)
    {q : tm.ComputationPath input} (hq : q.last.Halted) : p.last ∈ q.toRunPath := by
  rcases le_total p.length q.length with h | h
  · have hp := RunPath.eq_take (p.head_eq.trans q.head_eq.symm) h
    exact ⟨⟨p.length, Nat.lt_succ_of_le h⟩, (congrArg RelSeries.last hp).symm⟩
  · have hq' := congrArg RelSeries.last (RunPath.eq_take (q.head_eq.trans p.head_eq.symm) h)
    rw [RelSeries.last_take] at hq'
    rw [RunPath.last_eq_of_halted p.toRunPath _ (hq' ▸ hq), ← hq']
    exact RelSeries.last_mem _

/-- The computation paths of a deterministic machine are prefixes of one another, so a path visiting
at most as many cells as another visits at most as many on each tape. -/
lemma ComputationPath.spaceUsedByTape_le_of_space_le (p : tm.ComputationPath input)
    {q : tm.ComputationPath input} (h : p.space ≤ q.space) :
    p.spaceUsedByTape ≤ q.spaceUsedByTape := by
  -- a shorter path is a prefix of a longer one, so it visits fewer cells on each tape
  have hmono {p q : tm.ComputationPath input} (h : p.time ≤ q.time) :
      p.spaceUsedByTape ≤ q.spaceUsedByTape := fun i => by
    change RunPath.spaceUsedByTape p.toRunPath i ≤ RunPath.spaceUsedByTape q.toRunPath i
    rw [RunPath.eq_take (by rw [p.head_eq, q.head_eq]) h]
    exact Finset.card_le_card (RunPath.visitedByTapeHead_take_subset _ _ i)
  rcases le_total p.time q.time with hpq | hqp
  · exact hmono hpq
  -- a longer `p` visits no more cells than `q`, so it visits exactly those of `q`
  have h : ∑ j, p.spaceUsedByTape j ≤ ∑ j, q.spaceUsedByTape j := h
  exact fun i => ((Finset.sum_eq_sum_iff_of_le fun j _ => hmono hqp j).mp
    (le_antisymm (Finset.sum_le_sum fun j _ => hmono hqp j) h) i (Finset.mem_univ i)).ge

/-- A step-preserving map sends the path of `t` steps from `cfg` to the path of `t` steps from the
image of `cfg`. -/
lemma RunPath.map_ofDeterministic {k' : ℕ} {State' : Type*} {input' : List Symbol}
    {tm' : MultiTapeTM k' Symbol State'} (f : (tm.stepRel input).Hom (tm'.stepRel input'))
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (RunPath.ofDeterministic tm cfg t).map f = .ofDeterministic tm' (f cfg) t :=
  ((RunPath.ofDeterministic tm cfg t).map f).eq_ofDeterministic

end MultiTapeNTM

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
noncomputable def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input :=
  tm.step^[t] cfg

/-- Every path of a deterministic machine follows its iterated step function. -/
lemma runPath_apply_eq_runFrom (p : tm.RunPath input) (i : Fin (p.length + 1)) :
    p i = tm.runFrom p.head i := by
  revert i
  rw [p.eq_ofDeterministic]
  exact fun _ ↦ rfl

/-- A deterministic computation ends at the corresponding iterate. -/
lemma computationPath_last_eq_runFrom (p : tm.ComputationPath input) :
    p.last = tm.runFrom (tm.initCfg input) p.time := by
  rw [p.eq_ofDeterministic]
  rfl

/-- Running from the image of a configuration under a step-preserving map reaches the image of the
original run. -/
lemma runFrom_map {k' : ℕ} {State' : Type*} {input' : List Symbol}
    {tm' : MultiTapeTM k' Symbol State'} (f : (tm.stepRel input).Hom (tm'.stepRel input'))
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm'.runFrom (f cfg) t = f (tm.runFrom cfg t) :=
  congrArg RelSeries.last (MultiTapeNTM.RunPath.map_ofDeterministic f cfg t).symm

/-- Nothing changes after the machine has halted. -/
lemma runFrom_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    tm.runFrom cfg t = tm.runFrom cfg τ :=
  (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).last_eq_of_halted
    ⟨τ, Nat.lt_succ_of_le hle⟩ hhalt

/-- A deterministic machine halted after `t` steps satisfies the shared time bound. -/
lemma runsInTime_of_halted {input : List Symbol} {t : ℕ}
    (h : (tm.runFrom (tm.initCfg input) t).Halted) : tm.RunsInTime input t := by
  intro p hp
  rw [computationPath_last_eq_runFrom p, runFrom_eq_of_halt _ _ hp h]
  exact h

/-- The machine eventually halts on `input` with the given `output`. -/
def Computes (tm : MultiTapeTM k Symbol State) (input output : List Symbol) : Prop :=
  ∃ u, (tm.runFrom (tm.initCfg input) u).Halted ∧
    (tm.runFrom (tm.initCfg input) u).output = output

/-- The machine computes `output` from `input`, and `P` holds for this machine and input. -/
def ComputesSuchThat (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (P : MultiTapeTM k Symbol State → List Symbol → Prop) : Prop :=
  tm.Computes input output ∧ P tm input

/-- A condition on a computation can be weakened. -/
theorem ComputesSuchThat.mono {output : List Symbol}
    {P Q : MultiTapeTM k Symbol State → List Symbol → Prop}
    (h : tm.ComputesSuchThat input output P) (hPQ : P tm input → Q tm input) :
    tm.ComputesSuchThat input output Q :=
  ⟨h.1, hPQ h.2⟩

/-- The machine computes `output` from `input` within the given time bound. -/
def ComputesInTime (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t : ℕ) : Prop :=
  tm.ComputesSuchThat input output (fun tm input ↦ tm.RunsInTime input t)

/-- The machine computes `output` from `input` within the given space bound. -/
def ComputesInSpace (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (s : ℕ) : Prop :=
  tm.ComputesSuchThat input output (fun tm input ↦ tm.RunsInSpace input s)

/-- The machine computes `output` from `input` within the shared time and space bounds. -/
def ComputesInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) : Prop :=
  tm.ComputesSuchThat input output (fun tm input ↦
    tm.RunsInTime input t ∧ tm.RunsInSpace input s)

/-- The machine computes `f` relative to given encodings. For each argument `a`, the predicate
`P a` holds for this machine and the encoded input `encIn a`. -/
def ComputesFunSuchThat {α β : Type*} (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (f : α → β)
    (P : α → MultiTapeTM k Symbol State → List Symbol → Prop) : Prop :=
  ∀ a, tm.ComputesSuchThat (encIn a) (encOut (f a)) (P a)

/-- Conditions on a function computation can be weakened independently on every input. -/
theorem ComputesFunSuchThat.mono {α β : Type*}
    {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {f : α → β}
    {P Q : α → MultiTapeTM k Symbol State → List Symbol → Prop}
    (h : tm.ComputesFunSuchThat encIn encOut f P)
    (hPQ : ∀ a, P a tm (encIn a) → Q a tm (encIn a)) :
    tm.ComputesFunSuchThat encIn encOut f Q :=
  fun a ↦ (h a).mono (hPQ a)

/-- The machine computes `f` relative to given encodings within the given time bound. -/
def ComputesFunInTime {α β : Type*} (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (f : α → β) (t : α → ℕ) : Prop :=
  tm.ComputesFunSuchThat encIn encOut f (fun a tm input ↦ tm.RunsInTime input (t a))

/-- The machine computes `f` relative to given encodings within the given space bound. -/
def ComputesFunInSpace {α β : Type*} (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (f : α → β) (s : α → ℕ) : Prop :=
  tm.ComputesFunSuchThat encIn encOut f (fun a tm input ↦ tm.RunsInSpace input (s a))

/-- The machine computes `f` relative to given encodings within the given time and space bounds. -/
def ComputesFunInTimeAndSpace {α β : Type*} (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (f : α → β) (t s : α → ℕ) : Prop :=
  tm.ComputesFunSuchThat encIn encOut f
    (fun a tm input ↦ tm.RunsInTime input (t a) ∧ tm.RunsInSpace input (s a))

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {f : α → β} {t s t' s' : α → ℕ}
    (h : tm.ComputesFunInTimeAndSpace encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    tm.ComputesFunInTimeAndSpace encIn encOut f t' s' :=
  ComputesFunSuchThat.mono h fun a ⟨hₜ, hₛ⟩ ↦ ⟨hₜ.mono (ht a), hₛ.mono (hs a)⟩

/-- Computability by a deterministic machine with a binary tape alphabet and finitely many states.
For each argument `a`, the predicate `P a` holds for this machine and the encoded input `encIn a`.
-/
def ComputableSuchThat {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (P : ∀ {k : ℕ} {State : Type}, α → MultiTapeTM k Bool State → List Bool → Prop) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    tm.ComputesFunSuchThat encIn encOut f P

/-- Conditions on computability can be weakened independently on every input. -/
theorem ComputableSuchThat.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {P Q : ∀ {k : ℕ} {State : Type}, α → MultiTapeTM k Bool State → List Bool → Prop}
    (h : ComputableSuchThat f encIn encOut P)
    (hPQ : ∀ {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) a,
      P a tm (encIn a) → Q a tm (encIn a)) :
    ComputableSuchThat f encIn encOut Q := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono (hPQ tm)⟩

/-- Computability by a deterministic machine with a binary tape alphabet and finitely many states,
within the supplied input-indexed time bound. -/
def ComputableInTime {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (t : α → ℕ) : Prop :=
  ComputableSuchThat f encIn encOut (fun a tm input ↦ tm.RunsInTime input (t a))

/-- Computability by a deterministic machine with a binary tape alphabet and finitely many states,
within the supplied input-indexed space bound. -/
def ComputableInSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (s : α → ℕ) : Prop :=
  ComputableSuchThat f encIn encOut (fun a tm input ↦ tm.RunsInSpace input (s a))

/-- Computability by a deterministic machine with a binary tape alphabet and finitely many states,
within the supplied input-indexed bounds. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableSuchThat f encIn encOut
    (fun a tm input ↦ tm.RunsInTime input (t a) ∧ tm.RunsInSpace input (s a))

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
    ComputableInTimeAndSpace f encIn encOut t' s' :=
  ComputableSuchThat.mono h fun _ a ⟨hₜ, hₛ⟩ ↦ ⟨hₜ.mono (ht a), hₛ.mono (hs a)⟩

open scoped Classical in
/-- The Boolean indicator function of a set. -/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

/-- A set is decidable within the given input-indexed space bound when its Boolean indicator is
computable in that bound. -/
def DecidableInSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool) (s : α → ℕ) : Prop :=
  ComputableInSpace (indicator L) enc ⟨fun b ↦ [b], by intro a b h; simpa using h⟩ s

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is
computable in those bounds. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b ↦ [b], by intro a b h; simpa using h⟩ t s

/-- A deterministic path that ends halted never repeats a running configuration: from a repeated
configuration the machine would cycle forever. -/
lemma _root_.Turing.MultiTapeNTM.RunPath.injOn_running (p : tm.RunPath input)
    (h : p.last.Halted) : Set.InjOn p {i | ¬(p i).Halted} := by
  intro i hi j hj hij
  wlog hlt : i < j generalizing i j
  · rcases (not_lt.mp hlt).lt_or_eq with h' | h'
    · exact (this hj hi hij.symm h').symm
    · exact h'.symm
  exfalso
  have hp (n : Fin (p.length + 1)) : p n = tm.step^[n] p.head := runPath_apply_eq_runFrom p n
  -- `p i` is a periodic point of period `j - i`
  have hper : Function.IsPeriodicPt tm.step (j - i) (p i) := by
    change tm.step^[j - i] (p i) = p i
    conv_rhs => rw [hij]
    rw [hp j, hp i, ← Function.iterate_add_apply]
    congr 1
    omega
  -- so the halted last configuration already occurs within one period after `i`, before `j`
  have hk : (p.length - i) % (j - i) + i < j := by
    have := Nat.mod_lt (p.length - i) (show 0 < j.val - i.val by omega)
    omega
  refine p.not_halted_of_le (i := ⟨_, hk.trans j.isLt⟩) hk.le hj ?_
  rw [hp, Function.iterate_add_apply, ← hp, hper.iterate_mod_apply, hp,
    ← Function.iterate_add_apply]
  convert h using 2
  rw [RelSeries.last, hp (Fin.last _)]
  congr 1
  simp only [Fin.val_last]
  omega

end MultiTapeTM

end Turing
