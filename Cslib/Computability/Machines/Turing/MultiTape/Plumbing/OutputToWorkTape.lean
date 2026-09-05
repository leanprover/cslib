/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TapeContents
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Redirecting output to a fresh work tape

`outputToWorkTape` adds one work tape, at index `Fin.last k`, and writes the native output there.
Its head stays immediately after the output. The original work tapes and native input head follow
the original machine exactly; the external output is empty.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- Redirect output to a new last work tape without changing the alphabet or control states. -/
def outputToWorkTape (tm : MultiTapeTM k Symbol State) : MultiTapeTM (k + 1) Symbol State where
  q₀ := tm.q₀
  tr q input work :=
    let out := tm.tr q input (fun i => work i.castSucc)
    ⟨out.inputMove,
      Fin.lastCases (out.outS.elim (none, 0) (fun s => (some (some s), 1))) out.workActions,
      none, out.q'⟩

namespace OutputToWorkTape

/-- Represent a native configuration with its output on the new tape. -/
def embed (cfg : Cfg k Symbol State input) : Cfg (k + 1) Symbol State input where
  state := cfg.state
  inputPos := cfg.inputPos
  workTapes := Fin.lastCases (listTape cfg.output) cfg.workTapes
  workTapePos := Fin.lastCases cfg.output.length cfg.workTapePos
  output := []

variable (tm : MultiTapeTM k Symbol State)

/-- Each original transition is one transition of the output-redirected machine. -/
lemma step_embed (cfg : Cfg k Symbol State input) :
    tm.outputToWorkTape.step (embed cfg) = embed (tm.step cfg) := by
  have hwork : (fun i : Fin k => (embed cfg).workTapeSymbols i.castSucc) = cfg.workTapeSymbols := by
    funext i
    simp [embed, Cfg.workTapeSymbols]
  cases hs : cfg.state with
  | none => simp [step, embed, hs]
  | some q =>
    unfold step
    rw [show (embed cfg).state = some q from hs, hs]
    simp only [outputToWorkTape]
    rw [show (embed cfg).inputSymbol = cfg.inputSymbol from rfl, hwork]
    generalize htr : tm.tr q cfg.inputSymbol cfg.workTapeSymbols = out
    simp only [htr]
    apply Cfg.ext <;> try rfl
    · funext i p
      refine Fin.lastCases ?_ (fun j => ?_) i
      · cases out.outS <;> simp [embed, listTape_append_single]
      · cases hw : (out.workActions j).1 <;> simp [embed, hw]
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · cases out.outS <;> simp [embed]
      · simp [embed]

/-- Output redirection preserves arbitrary runs, including padded halting times. -/
lemma runFrom_embed (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm.outputToWorkTape.runFrom (embed cfg) n = embed (tm.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runFrom_succ_eq_step', ih, step_embed, runFrom_succ_eq_step']

end OutputToWorkTape

/-- The output-redirected machine simulates an ordinary run starting with blank work tapes. -/
lemma runFrom_outputToWorkTape (tm : MultiTapeTM k Symbol State) (input : List Symbol) (n : ℕ) :
    tm.outputToWorkTape.runFrom (tm.outputToWorkTape.initCfg input) n =
      OutputToWorkTape.embed (tm.runFrom (tm.initCfg input) n) := by
  have hinit : tm.outputToWorkTape.initCfg input = OutputToWorkTape.embed (tm.initCfg input) := by
    apply Cfg.ext <;> try rfl
    · funext i p
      refine Fin.lastCases ?_ (fun j => ?_) i
      · cases p <;> simp [OutputToWorkTape.embed, listTape]
      · simp [OutputToWorkTape.embed]
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [OutputToWorkTape.embed]
  rw [hinit, OutputToWorkTape.runFrom_embed]

end Turing.MultiTapeTM
