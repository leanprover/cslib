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
* `spaceUsed`: the number of tape cells touched by work tape heads, our main space measure
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

/-- The unique action permitted by the transition relation. -/
noncomputable def tr (tm : MultiTapeTM k Symbol State) (q : State) (input : Option Symbol)
    (work : Fin k → Option Symbol) : Action k Symbol State :=
  (tm.deterministic q input work).choose

/-- An action is permitted by `Tr` exactly when `tr` returns it. -/
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

private lemma existsUnique_step (cfg : Cfg k Symbol State input) :
    ∃! cfg', tm.Step cfg cfg' := by
  unfold MultiTapeNTM.Step
  cases cfg.state <;> simp

/-- The unique successor configuration permitted by the inherited step relation. -/
noncomputable def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  (show ∃! cfg', tm.Step cfg cfg' from by exact existsUnique_step cfg).choose

/-- A configuration is a permitted successor of `c` exactly when `step c` returns it. -/
@[simp, scoped grind =]
lemma step_iff {c c' : Cfg k Symbol State input} : tm.Step c c' ↔ tm.step c = c' := by
  unfold step
  exact (ExistsUnique.choose_eq_iff _).symm

/-- The successor returned by `step` is permitted by the inherited transition relation `Step`. -/
lemma step_spec (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) :
    tm.Step c (tm.step c) := step_iff.mpr rfl

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

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
noncomputable def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input :=
  tm.step^[t] cfg

/-- Every path of a deterministic machine follows its iterated step function. -/
lemma runPath_apply_eq_runFrom (p : tm.RunPath input) (i : Fin (p.length + 1)) :
    p i = tm.runFrom p.head i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    simp only [Fin.val_castSucc] at ih
    change p.toFun i.succ = tm.step^[i.val + 1] p.head
    rw [Function.iterate_succ_apply', ← runFrom, ← ih]
    exact (step_iff.mp (p.step i)).symm

private noncomputable def computationPath (tm : MultiTapeTM k Symbol State)
    (input : List Symbol) (t : ℕ) : tm.ComputationPath input where
  length := t
  toFun n := tm.runFrom (tm.initCfg input) n
  step n := by simp [runFrom, Function.iterate_succ_apply']
  head_eq := rfl

/-- A deterministic computation ends at the corresponding iterate. -/
lemma computationPath_last_eq_runFrom (p : tm.ComputationPath input) :
    p.last = tm.runFrom (tm.initCfg input) p.time := by
  simpa only [RelSeries.apply_last, Fin.val_last, p.head_eq,
    MultiTapeNTM.ComputationPath.time, MultiTapeNTM.RunPath.time] using
    runPath_apply_eq_runFrom p.toRunPath (Fin.last p.length)

/-- Nothing changes after the machine has halted. -/
lemma runFrom_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    tm.runFrom cfg t = tm.runFrom cfg τ := by
  rw [runFrom, ← Nat.sub_add_cancel hle, Function.iterate_add_apply]
  exact Function.iterate_fixed (step_of_halt hhalt) _

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

/-- The work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  cases hstate : c.state with
  | none => simp [step_of_halt hstate]
  | some q => rw [step_of_state hstate]; exact workTapePos_apply_le _ c i

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
noncomputable def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    Finset ℤ :=
  Finset.univ.image fun n : Fin (t + 1) => (tm.runFrom cfg n).workTapePos i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
noncomputable def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
noncomputable def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ :=
  ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ tm.spaceUsed cfg t :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

end Space

/-- In `t` steps the input head moves at most `t` positions to the right. -/
lemma inputPos_runFrom_le (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    ((tm.runFrom cfg t).inputPos : ℕ) ≤ (cfg.inputPos : ℕ) + t := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    by_cases hq : (tm.runFrom cfg t).state = none
    · rw [step_of_halt hq]
      omega
    · obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hq
      have h : ((tm.step (tm.runFrom cfg t)).inputPos : ℕ) ≤
          ((tm.runFrom cfg t).inputPos : ℕ) + 1 := by
        rw [step_inputPos_of_state hq]
        exact val_moveInputPos_le _ _
      omega

/-- The output only grows during a run. -/
lemma length_output_mono (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) :
    Monotone fun t => (tm.runFrom cfg t).output.length :=
  monotone_nat_of_le_succ fun t => by
    conv_rhs => rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    cases h : (tm.runFrom cfg t).state with
    | none => simp [step_of_halt h]
    | some q => simp [step_of_state h]

/-- A machine emits at most one symbol per step. -/
theorem length_output_runFrom_le (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runFrom cfg t).output.length ≤ cfg.output.length + t := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    exact (tm.step_spec _).length_output_le.trans (by omega)

/-- The shared time bound is halting by that time for a deterministic machine. -/
lemma runsInTime_iff {input : List Symbol} {t : ℕ} :
    tm.RunsInTime input t ↔ (tm.runFrom (tm.initCfg input) t).Halted := by
  refine ⟨fun h ↦ h (computationPath tm input t) le_rfl _ (tm.step_spec _),
    fun h p hp _ _ ↦ ?_⟩
  rw [computationPath_last_eq_runFrom p, tm.runFrom_eq_of_halt _ hp h]
  exact h

/-- A halted deterministic machine accepts exactly when its output is `[true]`. -/
lemma accepts_iff_of_halted {tm : MultiTapeTM k Bool State} {input : List Bool} {t : ℕ}
    (h : (tm.runFrom (tm.initCfg input) t).Halted) :
    tm.Accepts input ↔ (tm.runFrom (tm.initCfg input) t).output = [true] := by
  refine ⟨?_, fun hout ↦ ⟨computationPath tm input t, h, hout⟩⟩
  rintro ⟨p, hp, hout⟩
  rw [computationPath_last_eq_runFrom p] at hp hout
  rcases le_total p.time t with hle | hle
  · rwa [tm.runFrom_eq_of_halt _ hle hp]
  · rwa [tm.runFrom_eq_of_halt _ hle h] at hout

/-- Once a deterministic machine halts, the shared space bound is its space usage so far. -/
lemma usesSpace_iff_of_halted {input : List Symbol} {t s : ℕ}
    (h : (tm.runFrom (tm.initCfg input) t).Halted) :
    tm.UsesSpace input s ↔ tm.spaceUsed (tm.initCfg input) t ≤ s := by
  refine ⟨fun hs ↦ hs (computationPath tm input t), fun hs p ↦ le_trans ?_ hs⟩
  unfold MultiTapeNTM.ComputationPath.space MultiTapeNTM.RunPath.space spaceUsed
  apply Finset.sum_le_sum
  intro i _
  unfold MultiTapeNTM.RunPath.spaceUsedByTape spaceUsedByTape
  apply Finset.card_le_card
  intro z hz
  simp only [MultiTapeNTM.RunPath.visitedByTapeHead, visitedByTapeHead,
    Finset.mem_image, Finset.mem_univ, true_and] at hz ⊢
  obtain ⟨n, rfl⟩ := hz
  refine ⟨⟨min n.val t, by omega⟩, ?_⟩
  rw [runPath_apply_eq_runFrom p.toRunPath n, p.head_eq]
  by_cases hn : n.val ≤ t
  · simp [min_eq_left hn]
  · simp only [min_eq_right (by omega : t ≤ n.val)]
    rw [tm.runFrom_eq_of_halt (tm.initCfg input) (by omega : t ≤ n.val) h]

/-- On every input `a`, the deterministic machine halts with output `encOut (f a)` within the
supplied time and space bounds. -/
def ComputesFunInTimeAndSpace {α β : Type*} (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ u ≤ t a, (tm.runFrom (tm.initCfg (encIn a)) u).Halted ∧
    (tm.runFrom (tm.initCfg (encIn a)) u).output = encOut (f a) ∧
    tm.spaceUsed (tm.initCfg (encIn a)) u ≤ s a

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {f : α → β} {t s t' s' : α → ℕ}
    (h : tm.ComputesFunInTimeAndSpace encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    tm.ComputesFunInTimeAndSpace encIn encOut f t' s' := fun a ↦ by
  obtain ⟨u, hu, hh, hout, hspace⟩ := h a
  exact ⟨u, hu.trans (ht a), hh, hout, hspace.trans (hs a)⟩

/-- A machine emits at most one symbol per step, so the encoded result is no longer than its
time bound. -/
theorem ComputesFunInTimeAndSpace.length_encOut_le {α β : Type*}
    {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {f : α → β} {t s : α → ℕ}
    (h : tm.ComputesFunInTimeAndSpace encIn encOut f t s) (a : α) :
    (encOut (f a)).length ≤ t a := by
  obtain ⟨u, hu, _, hout, _⟩ := h a
  rw [← hout]
  exact (tm.length_output_runFrom_le (tm.initCfg (encIn a)) u).trans
    (by simpa using hu)

/-- Computability by a deterministic machine with a binary tape alphabet and finitely many states,
within the supplied input-indexed bounds. -/
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

open Classical in
/-- The Boolean indicator function of a set. -/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

/-- For a deterministic machine, decision is computation of the Boolean indicator. -/
lemma decidesInTimeAndSpace_iff {α : Type*} {tm : MultiTapeTM k Bool State}
    {L : Set α} {enc : α ↪ List Bool} {t s : α → ℕ} :
    tm.DecidesInTimeAndSpace L enc t s ↔
      tm.ComputesFunInTimeAndSpace enc
        ⟨fun b ↦ [b], by intro a b h; simpa using h⟩ (indicator L) t s := by
  classical
  constructor
  · intro h a
    have hh := runsInTime_iff.mp (h a).2.1
    refine ⟨t a, le_rfl, hh, ?_, (usesSpace_iff_of_halted hh).mp (h a).2.2.1⟩
    change (tm.runFrom (tm.initCfg (enc a)) (t a)).output = [indicator L a]
    by_cases ha : a ∈ L
    · simp only [indicator, ite_eq_left ha]
      exact (accepts_iff_of_halted hh).mp ((h a).1.mpr ha)
    · rcases (h a).2.2.2 (computationPath tm (enc a) (t a)) hh with hout | hout
      · exact (ha ((h a).1.mp ((accepts_iff_of_halted hh).mpr hout))).elim
      · simp only [indicator, ite_eq_right ha]
        exact hout
  · intro h a
    obtain ⟨u, hu, hh, hout, hs⟩ := h a
    refine ⟨?_, (runsInTime_iff.mpr hh).mono hu, (usesSpace_iff_of_halted hh).mpr hs,
      fun p hp ↦ ?_⟩
    · rw [accepts_iff_of_halted hh, hout]
      simp [indicator]
    · rw [computationPath_last_eq_runFrom p] at hp ⊢
      have heq : tm.runFrom (tm.initCfg (enc a)) p.time =
          tm.runFrom (tm.initCfg (enc a)) u := by
        rcases le_total u p.time with hle | hle
        · exact tm.runFrom_eq_of_halt _ hle hh
        · exact (tm.runFrom_eq_of_halt _ hle hp).symm
      rw [heq, hout]
      cases indicator L a <;> simp

/-- A set is decidable within the bounds by a deterministic machine, using the shared
nondeterministic decision predicate. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    tm.DecidesInTimeAndSpace L enc t s

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`
if its state is `none` at step `t` and non-none at step `t - 1`.
Note that every Turing machine hast to perform at least one step to halt. -/
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
    rw [runFrom, Function.iterate_add_apply]
    exact (congrArg Cfg.state
      (Function.iterate_fixed (step_of_halt (tm := tm) halts₁) d)).trans halts₁

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `Function.iterate_add_apply`. -/
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
    rwa [tm.runFrom_eq_of_halt cfg hle hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing
