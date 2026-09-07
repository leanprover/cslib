/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-! # Configuration state replacement and execution paths

`Cfg.withState` changes the control state, possibly changing its type, and preserves all tapes,
head positions, and accumulated output. `runFrom_map` transports runs along maps that preserve
steps, and `runFrom_eq_of_isChain` identifies the endpoint of an explicit execution path.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- The configuration `cfg` with its state replaced by `q`, possibly over a different state
type. -/
@[simps]
def Cfg.withState (cfg : Cfg k Symbol State input) {State' : Type*}
    (q : Option State') : Cfg k Symbol State' input :=
  ⟨q, cfg.inputPos, cfg.workTapes, cfg.workTapePos, cfg.output⟩

@[simp]
lemma Cfg.withState_inputSymbol {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).inputSymbol = cfg.inputSymbol := rfl

@[simp]
lemma Cfg.withState_workTapeSymbols {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).workTapeSymbols = cfg.workTapeSymbols := rfl

@[simp]
lemma Cfg.withState_withState {cfg : Cfg k Symbol State input} {State' State'' : Type*}
    {q : Option State'} {q' : Option State''} :
    (cfg.withState q).withState q' = cfg.withState q' := rfl

@[simp]
lemma Cfg.withState_self {cfg : Cfg k Symbol State input} :
    cfg.withState cfg.state = cfg := rfl

/-- A map that preserves steps maps every configuration of an execution. -/
lemma runFrom_map {k' : ℕ} {Symbol' State' : Type*} {input' : List Symbol'}
    (tm : MultiTapeTM k Symbol State) (tm' : MultiTapeTM k' Symbol' State')
    (embed : Cfg k Symbol State input → Cfg k' Symbol' State' input')
    (hstep : ∀ cfg, tm'.step (embed cfg) = embed (tm.step cfg))
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm'.runFrom (embed cfg) n = embed (tm.runFrom cfg n) := by
  have h : Function.Semiconj embed tm.step tm'.step := fun cfg => (hstep cfg).symm
  exact (h.iterate_right n cfg).symm

/-- An execution path ends at the configuration reached after one step per adjacent pair. -/
lemma runFrom_eq_of_isChain (tm : MultiTapeTM k Symbol State)
    {cfg cfg' : Cfg k Symbol State input} {path : List (Cfg k Symbol State input)}
    (hpath : path.IsChainFromTo tm.TransitionRelation cfg cfg') :
    tm.runFrom cfg (path.length - 1) = cfg' := by
  apply (tm.relatesInSteps_iff_runFrom_eq cfg cfg' _).mp
  exact hpath.relatesInSteps (by have := hpath.length_pos; omega)

end Turing.MultiTapeTM
