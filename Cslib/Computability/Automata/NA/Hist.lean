/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic

/-! # Adding a history states to a nondeterministic automaton.

The evolution of the history state can depend on both the original state and the past history
state. But the evolution of the original state is not constrained by the history state.
-/

@[expose] public section

namespace Cslib.Automata.NA

open Prod ωSequence
open scoped LTS

variable {Symbol State Hist : Type*}

/-- The construction of adding a history state.  Note that `start'` can depend on the initial
value of the original state and `tr'` can depend on the new value of the original state.
So there is no loss of generality in their being functions, rather than relations. -/
def addHist (na : NA State Symbol) (start' : State → Hist)
    (tr' : State × Hist → Symbol → State → Hist) : NA (State × Hist) Symbol where
  Tr s x t := na.Tr s.fst x t.fst ∧ tr' s x t.fst = t.snd
  start := { s | s.fst ∈ na.start ∧ start' s.fst = s.snd }

variable {na : NA State Symbol} {start' : State → Hist}
  {tr' : State × Hist → Symbol → State → Hist}

/-- Characterization of transitions in `na.addHist start' tr'`. -/
@[simp]
theorem addHist_tr {s t : State × Hist} {x : Symbol} :
    (na.addHist start' tr').Tr s x t ↔ na.Tr s.fst x t.fst ∧ tr' s x t.fst = t.snd :=
  Iff.rfl

/-- Characterization of initial states in `na.addHist start' tr'`. -/
@[simp, scoped grind =]
theorem mem_addHist_start {s : State × Hist} :
    s ∈ (na.addHist start' tr').start ↔ s.fst ∈ na.start ∧ start' s.fst = s.snd :=
  Iff.rfl

/-- Characterization of infinite runs in `na.addHist start' tr'`. -/
@[simp, scoped grind =]
theorem addHist_run_iff {xs : ωSequence Symbol} {ss : ωSequence (State × Hist)} :
    (na.addHist start' tr').Run xs ss ↔
      na.Run xs (ss.map fst) ∧ start' (ss 0).fst = (ss 0).snd ∧
        ∀ n, tr' (ss n) (xs n) (ss (n + 1)).fst = (ss (n + 1)).snd := by
  refine ⟨fun h => ⟨⟨h.start.1, fun n => (h.trans n).1⟩, h.start.2, fun n => (h.trans n).2⟩, ?_⟩
  rintro ⟨h_run, h_start, h_tr⟩
  exact ⟨⟨h_run.start, h_start⟩, fun n => ⟨h_run.trans n, h_tr n⟩⟩

/-- Every run of the history automaton projects onto a run of the original automaton. -/
theorem hist_run_proj {xs : ωSequence Symbol} {ss : ωSequence (State × Hist)}
    (h_run : (na.addHist start' tr').Run xs ss) : na.Run xs (ss.map fst) :=
  (addHist_run_iff.mp h_run).1

/-- Given a run of the original automaton, `makeHist` builds a run of the history state. -/
def makeHist (start' : State → Hist) (tr' : State × Hist → Symbol → State → Hist)
    (xs : ωSequence Symbol) (ss : ωSequence State) : ℕ → Hist
  | 0 => start' (ss 0)
  | n + 1 => tr' (ss n, makeHist start' tr' xs ss n) (xs n) (ss (n + 1))

/-- Initial value of `makeHist`. -/
@[simp, scoped grind =]
theorem makeHist_zero {xs : ωSequence Symbol} {ss : ωSequence State} :
    makeHist start' tr' xs ss 0 = start' (ss 0) :=
  rfl

/-- Step equation of `makeHist`. -/
@[simp, scoped grind =]
theorem makeHist_succ {xs : ωSequence Symbol} {ss : ωSequence State} (n : ℕ) :
    makeHist start' tr' xs ss (n + 1) =
      tr' (ss n, makeHist start' tr' xs ss n) (xs n) (ss (n + 1)) :=
  rfl

/-- Pairing `ss` with `makeHist` gives a run of `na.addHist start' tr'` iff `ss` is a run of
`na`. -/
theorem hist_run_makeHist {xs : ωSequence Symbol} {ss : ωSequence State} :
    (na.addHist start' tr').Run xs (fun n => (ss n, makeHist start' tr' xs ss n)) ↔
      na.Run xs ss :=
  ⟨hist_run_proj, fun h => ⟨⟨h.start, rfl⟩, fun n => ⟨h.trans n, rfl⟩⟩⟩

/-- For every run `ss` of the original automaton, there exists a run `ss'` of the history automaton
which projects back onto `ss`. -/
theorem hist_run_exists {xs : ωSequence Symbol} {ss : ωSequence State}
    (h_run : na.Run xs ss) : ∃ ss', (na.addHist start' tr').Run xs ss' ∧ ss'.map fst = ss :=
  ⟨fun n => (ss n, makeHist start' tr' xs ss n), hist_run_makeHist.mpr h_run, rfl⟩

end Cslib.Automata.NA
