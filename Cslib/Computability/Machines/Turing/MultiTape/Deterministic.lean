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
* `Computes`: the machine halts with the given output on an input
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

end Cfg

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

/-- The machine eventually halts on `input` with the given `output`. -/
def Computes (tm : MultiTapeTM k Symbol State) (input output : List Symbol) : Prop :=
  ∃ u, (tm.runFrom (tm.initCfg input) u).Halted ∧
    (tm.runFrom (tm.initCfg input) u).output = output

/-- The machine computes `output` from `input` within the shared time and space bounds. -/
def ComputesInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) : Prop :=
  tm.Computes input output ∧ tm.RunsInTime input t ∧ tm.RunsInSpace input s

/-- The machine computes `f`, with every computation path subject to the supplied time and space
bounds. -/
def ComputesFunInTimeAndSpace {α β : Type*} (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, tm.ComputesInTimeAndSpace (encIn a) (encOut (f a)) (t a) (s a)

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {f : α → β} {t s t' s' : α → ℕ}
    (h : tm.ComputesFunInTimeAndSpace encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    tm.ComputesFunInTimeAndSpace encIn encOut f t' s' :=
  fun a ↦ ⟨(h a).1, (h a).2.1.mono (ht a), (h a).2.2.mono (hs a)⟩

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

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b ↦ [b], by intro a b h; simpa using h⟩ t s

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

namespace MultiTapeNTM

/-- A deterministic machine has at most one successor configuration. -/
lemma IsDeterministic.step_rightUnique {ntm : MultiTapeNTM k Symbol State}
    (h : ntm.IsDeterministic) {input : List Symbol} {c c' c'' : Cfg k Symbol State input}
    (hc : ntm.Step c c') (hc' : ntm.Step c c'') : c' = c'' := by
  cases hq : c.state with
  | none => exact ((step_of_halt hq).mp hc).trans ((step_of_halt hq).mp hc').symm
  | some q =>
    obtain ⟨a, ha, rfl⟩ := (step_of_state hq).mp hc
    obtain ⟨b, hb, rfl⟩ := (step_of_state hq).mp hc'
    rw [(h q c.inputSymbol c.workTapeSymbols).unique ha hb]

/-- Paths of a deterministic machine with the same start agree at every common index. -/
lemma IsDeterministic.apply_eq {ntm : MultiTapeNTM k Symbol State} (h : ntm.IsDeterministic)
    {input : List Symbol} (p q : ntm.RunPath input) (hh : p.head = q.head)
    (i : Fin (p.length + 1)) (j : Fin (q.length + 1)) (hij : i.val = j.val) : p i = q j := by
  induction i using Fin.induction generalizing j with
  | zero =>
    have hj : j = 0 := Fin.ext hij.symm
    subst j
    exact hh
  | succ i ih =>
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by intro hj; simp [hj] at hij)
    have hp := p.step i
    rw [ih j.castSucc (Nat.succ.inj hij)] at hp
    exact h.step_rightUnique hp (q.step j)

end MultiTapeNTM

end Turing
