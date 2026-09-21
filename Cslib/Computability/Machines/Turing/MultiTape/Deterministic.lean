/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Deterministic Multi-Tape Turing Machines

A deterministic machine is a `MultiTapeNTM` whose transition relation permits exactly one action
for each state and tuple of symbols.

## Design

Deterministic machines specialize nondeterministic machines by requiring a unique transition.
The shared definitions and the relation-to-function API let results about nondeterministic machines
apply directly to deterministic machines.

## Important Declarations

* `MultiTapeTM`: a nondeterministic machine with exactly one action per situation
* `ofTr`, `tr`: construction from a function and the derived function API
* `step`: the unique successor permitted by the shared step relation
* `runFrom`: the configuration reached by iterating `step`
* `spaceUsed`: the space used during a finite number of steps
* `ComputableInTimeAndSpace`: existence of a deterministic machine within input-indexed bounds
-/

@[expose] public section

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
  deterministic : toMultiTapeNTM.IsDeterministic

instance : CoeOut (MultiTapeTM k Symbol State) (MultiTapeNTM k Symbol State) :=
  ⟨MultiTapeTM.toMultiTapeNTM⟩

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

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

/-- The unique successor permitted by the inherited step relation. -/
noncomputable def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  (show ∃! cfg', tm.Step cfg cfg' from by
    unfold MultiTapeNTM.Step
    cases cfg.state <;> simp).choose

/-- The inherited step relation is the graph of `step`. -/
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

end Cfg

/-- The configuration reached after `t` steps. After halting, the configuration stays fixed. -/
noncomputable def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input :=
  tm.step^[t] cfg

/-- Space usage along the first `t` steps, using the shared measure on configuration lists. -/
@[simp]
noncomputable def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ :=
  spaceUsedOfCfgs (List.ofFn fun n : Fin (t + 1) => tm.runFrom cfg n)

/-- Computability by a deterministic binary machine with finitely many states, within the supplied
input-indexed bounds. This specializes nondeterministic computability to deterministic witnesses. -/
abbrev ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  MultiTapeNTM.ComputableInTimeAndSpace f encIn encOut t s MultiTapeNTM.IsDeterministic

end MultiTapeTM

end Turing
