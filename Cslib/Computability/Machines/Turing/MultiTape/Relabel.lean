/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Relabelling the States of a Multi-Tape Turing Machine

The behaviour of a Turing machine does not depend on the actual state type.
This is useful because it allows us to restrict the state type to e.g. `Fin s` for some `s`
in some definitions or theorems while still being able to use more convenient arbitrary finite types
in constructions.

## Main Declarations

* `Turing.MultiTapeTM.relabel`: transport of a machine along an equivalence of state types
* `Turing.MultiTapeTM.encodedComputableInTimeAndSpace_of_computes`: a machine with an arbitrary
  finite state type witnesses `EncodedComputableInTimeAndSpace`

-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State State' : Type*}
    {tm : MultiTapeTM k Symbol State} {e : State ≃ State'}
    {input : List Symbol} {cfg : Cfg k Symbol State input}

/-- Transform a Turing machine along an equivalence of state types. -/
def relabel (tm : MultiTapeTM k Symbol State) (e : State ≃ State') :
    MultiTapeTM k Symbol State' where
  q₀ := e tm.q₀
  tr q input work :=
    { tm.tr (e.symm q) input work with q' := ((tm.tr (e.symm q) input work).q').map e }

/-- Transform a configuration along an equivalence of state types. -/
@[simps]
def Cfg.relabel (cfg : Cfg k Symbol State input) (e : State ≃ State') :
    Cfg k Symbol State' input :=
  { cfg with state := cfg.state.map e }

@[simp]
lemma Cfg.relabel_inputSymbol : (cfg.relabel e).inputSymbol = cfg.inputSymbol := rfl

@[simp]
lemma Cfg.relabel_workTapeSymbols : (cfg.relabel e).workTapeSymbols = cfg.workTapeSymbols := rfl

/-- One step commutes with relabelling. -/
lemma step_relabel : (tm.relabel e).step (cfg.relabel e) = (tm.step cfg).relabel e := by
  cases h : cfg.state with
  | none => simp [step, Cfg.relabel, h]
  | some q =>
    simp only [step, Cfg.relabel, relabel, h, Option.map_some, Equiv.symm_apply_apply]
    rfl

/-- Running the machine commutes with relabelling. -/
lemma runFrom_relabel {t : ℕ} :
    (tm.relabel e).runFrom (cfg.relabel e) t = (tm.runFrom cfg t).relabel e := by
  induction t with
  | zero => simp
  | succ t ih => rw [runFrom_succ_eq_step', runFrom_succ_eq_step', ih, step_relabel]

@[simp]
lemma initCfg_relabel : (tm.relabel e).initCfg input = (tm.initCfg input).relabel e := rfl

@[simp]
lemma spaceUsed_relabel {t : ℕ} :
    (tm.relabel e).spaceUsed (cfg.relabel e) t = tm.spaceUsed cfg t := by
  simp [spaceUsed, spaceUsedByTape, visitedByTapeHead, runFrom_relabel]

/-- Relabelling the states preserves the computed output as well as the time and space usage. -/
lemma ComputesInTimeAndSpace.relabel {output : List Symbol} {t s : ℕ}
    (h : ComputesInTimeAndSpace tm input output t s) :
    ComputesInTimeAndSpace (tm.relabel e) input output t s := by
  obtain ⟨hhalt, hout, hspace⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [initCfg_relabel, runFrom_relabel] <;>
    simpa using ‹_›

end Turing.MultiTapeTM
