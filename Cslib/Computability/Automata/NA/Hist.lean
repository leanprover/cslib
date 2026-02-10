/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic

@[expose] public section

/-! # Adding a history states to a nondeterministic automaton.

The evolution of the history state can depend on both the original state and the past history
state. But the evolution of the original state is not constrained by the history state.
-/

namespace Cslib.Automata.NA

open Prod ωSequence
open scoped LTS

variable {Symbol State Hist : Type*}

/-- The construction of adding a history state.  Note that `start'` can depend on the initial
value of the original state and `tr'` can depend on the new value of the original state.
So there is no loss of generality in their being functions, rather than relations. -/
@[scoped grind =]
def addHist (na : NA State Symbol) (start' : State → Hist)
    (tr' : State × Hist → Symbol → State → Hist) : NA (State × Hist) Symbol where
  Tr s x t := na.Tr s.fst x t.fst ∧ tr' s x t.fst = t.snd
  start := { s | s.fst ∈ na.start ∧ start' s.fst = s.snd }

variable {na : NA State Symbol} {start' : State → Hist}
  {tr' : State × Hist → Symbol → State → Hist}

/-- Every run of the history automaton projects onto a run of the original automaton. -/
theorem hist_run_proj {xs : ωSequence Symbol} {ss : ωSequence (State × Hist)}
    (h_run : (na.addHist start' tr').Run xs ss) : na.Run xs (ss.map fst) := by
  obtain ⟨h_start, h_trans⟩ := h_run
  simp only [addHist] at h_trans
  grind [Run]

/-- Given a run of the original automaton, `makeHist` builds a run of the history state. -/
@[scoped grind =]
def makeHist (start' : State → Hist) (tr' : State × Hist → Symbol → State → Hist)
  (xs : ωSequence Symbol) (ss : ωSequence State) : ℕ → Hist
  | 0 => start' (ss 0)
  | n + 1 => tr' (ss n, makeHist start' tr' xs ss n) (xs n) (ss (n + 1))

/-- For every run `ss` of the original automaton, there exists a run `ss'` of the history automaton
which projects back onto `ss`. -/
theorem hist_run_exists {xs : ωSequence Symbol} {ss : ωSequence State}
    (h_run : na.Run xs ss) : ∃ ss', (na.addHist start' tr').Run xs ss' ∧ ss'.map fst = ss := by
  use ⟨fun n ↦ (ss n, makeHist start' tr' xs ss n)⟩
  constructor
  · simp only [addHist]
    grind [Run]
  · grind

end Cslib.Automata.NA
