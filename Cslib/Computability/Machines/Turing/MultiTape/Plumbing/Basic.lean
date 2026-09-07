/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-! # Configuration state replacement

`Cfg.withState` changes the control state, possibly changing its type, and preserves all tapes,
head positions, and accumulated output.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- The configuration `cfg` with its state replaced by `q`, possibly over a different state
type. -/
def Cfg.withState (cfg : Cfg k Symbol State input) {State' : Type*}
    (q : Option State') : Cfg k Symbol State' input :=
  ⟨q, cfg.inputPos, cfg.workTapes, cfg.workTapePos, cfg.output⟩

@[simp]
lemma Cfg.withState_state {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).state = q := rfl

@[simp]
lemma Cfg.withState_inputPos {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).inputPos = cfg.inputPos := rfl

@[simp]
lemma Cfg.withState_workTapes {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).workTapes = cfg.workTapes := rfl

@[simp]
lemma Cfg.withState_workTapePos {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).workTapePos = cfg.workTapePos := rfl

@[simp]
lemma Cfg.withState_output {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).output = cfg.output := rfl

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

/-- The configuration `cfg` with `o` prepended to the output produced so far. -/
def Cfg.prependOutput (o : List Symbol) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input :=
  { cfg with output := o ++ cfg.output }

@[simp]
lemma Cfg.prependOutput_state {o : List Symbol} {cfg : Cfg k Symbol State input} :
    (cfg.prependOutput o).state = cfg.state := rfl

@[simp]
lemma Cfg.prependOutput_inputPos {o : List Symbol} {cfg : Cfg k Symbol State input} :
    (cfg.prependOutput o).inputPos = cfg.inputPos := rfl

@[simp]
lemma Cfg.prependOutput_workTapes {o : List Symbol} {cfg : Cfg k Symbol State input} :
    (cfg.prependOutput o).workTapes = cfg.workTapes := rfl

@[simp]
lemma Cfg.prependOutput_workTapePos {o : List Symbol} {cfg : Cfg k Symbol State input} :
    (cfg.prependOutput o).workTapePos = cfg.workTapePos := rfl

@[simp]
lemma Cfg.prependOutput_output {o : List Symbol} {cfg : Cfg k Symbol State input} :
    (cfg.prependOutput o).output = o ++ cfg.output := rfl

@[simp]
lemma Cfg.prependOutput_inputSymbol {o : List Symbol} {cfg : Cfg k Symbol State input} :
    (cfg.prependOutput o).inputSymbol = cfg.inputSymbol := rfl

@[simp]
lemma Cfg.prependOutput_workTapeSymbols {o : List Symbol} {cfg : Cfg k Symbol State input} :
    (cfg.prependOutput o).workTapeSymbols = cfg.workTapeSymbols := rfl

/-- A step does not depend on the output accumulated so far, since the output tape is write-only
and a step only appends to it. -/
lemma step_prependOutput (tm : MultiTapeTM k Symbol State) (o : List Symbol)
    (cfg : Cfg k Symbol State input) :
    tm.step (cfg.prependOutput o) = (tm.step cfg).prependOutput o := by
  cases hs : cfg.state with
  | none => simp [step, Cfg.prependOutput, hs]
  | some q =>
    have hstate : (cfg.prependOutput o).state = some q := hs
    unfold step
    rw [hstate, hs, Cfg.prependOutput_inputSymbol, Cfg.prependOutput_workTapeSymbols]
    apply Cfg.ext <;> simp [List.append_assoc]

/-- A whole run does not depend on the output accumulated before it. This is what lets a machine
be run after another one has already written part of the output. -/
lemma runFrom_prependOutput (tm : MultiTapeTM k Symbol State) (o : List Symbol)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm.runFrom (cfg.prependOutput o) n = (tm.runFrom cfg n).prependOutput o := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runFrom_succ_eq_step', ih, step_prependOutput, runFrom_succ_eq_step']

/-- Prepending output does not change the space used. -/
lemma spaceUsed_prependOutput (tm : MultiTapeTM k Symbol State) (o : List Symbol)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm.spaceUsed (cfg.prependOutput o) n = tm.spaceUsed cfg n :=
  spaceUsed_eq_of_workTapePos _ _ n fun m _ => by
    rw [runFrom_prependOutput, Cfg.prependOutput_workTapePos]

/-- A family of configurations with the prescribed steps agrees with `runFrom`. -/
lemma runFrom_eq_of_step (tm : MultiTapeTM k Symbol State)
    (path : ℕ → Cfg k Symbol State input) (n : ℕ)
    (hstep : ∀ r < n, tm.step (path r) = path (r + 1)) :
    tm.runFrom (path 0) n = path n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ_eq_step', ih (fun r hr => hstep r (by omega)), hstep n (by omega)]

end Turing.MultiTapeTM
