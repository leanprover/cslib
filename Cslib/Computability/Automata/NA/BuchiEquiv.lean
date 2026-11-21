/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic

/-! # Equivalence of nondeterministic Buchi automata (NBAs). -/

@[expose] public section

universe u v w

namespace Cslib.Automata.NA.Buchi

open Set Function Filter ωSequence ωLanguage ωAcceptor
open scoped Run LTS

variable {Symbol : Type u} {State : Type v} {State' : Type w}

/-- Lifts an equivalence on states to an equivalence on NBAs. -/
def reindex (f : State ≃ State') : Buchi State Symbol ≃ Buchi State' Symbol where
  toFun nba := {
    Tr s x t := nba.Tr (f.symm s) x (f.symm t)
    start := f '' nba.start
    accept := f.symm ⁻¹' nba.accept
  }
  invFun nba' := {
    Tr s x t := nba'.Tr (f s) x (f t)
    start := f.symm '' nba'.start
    accept := f ⁻¹' nba'.accept
  }
  left_inv nba := by simp
  right_inv nba' := by simp

/-- Characterization of transitions in `nba.reindex f`. -/
@[simp]
theorem reindex_tr {f : State ≃ State'} {nba : Buchi State Symbol}
    {s t : State'} {x : Symbol} :
    (nba.reindex f).Tr s x t ↔ nba.Tr (f.symm s) x (f.symm t) :=
  Iff.rfl

/-- Characterization of initial states in `nba.reindex f`. -/
@[simp, scoped grind =]
theorem mem_reindex_start {f : State ≃ State'} {nba : Buchi State Symbol} {s : State'} :
    s ∈ (nba.reindex f).start ↔ f.symm s ∈ nba.start :=
  mem_image_equiv

/-- Characterization of accepting states in `nba.reindex f`. -/
@[simp, scoped grind =]
theorem mem_reindex_accept {f : State ≃ State'} {nba : Buchi State Symbol} {s : State'} :
    s ∈ (nba.reindex f).accept ↔ f.symm s ∈ nba.accept :=
  Iff.rfl

/-- Characterization of infinite runs in `nba.reindex f`. -/
@[scoped grind =]
theorem reindex_run_iff {f : State ≃ State'} {nba : Buchi State Symbol}
    {xs : ωSequence Symbol} {ss' : ωSequence State'} :
    (nba.reindex f).Run xs ss' ↔ nba.Run xs (ss'.map f.symm) :=
  ⟨fun ⟨h_init, h_next⟩ => ⟨mem_image_equiv.mp h_init, fun n => h_next n⟩,
   fun ⟨h_init, h_next⟩ => ⟨mem_image_equiv.mpr h_init, fun n => h_next n⟩⟩

/-- Mapping a sequence through `f` gives a run of `nba.reindex f` iff the sequence is a run of
`nba`. -/
@[simp]
theorem reindex_run_iff' {f : State ≃ State'} {nba : Buchi State Symbol}
    {xs : ωSequence Symbol} {ss : ωSequence State} :
    (nba.reindex f).Run xs (ss.map f) ↔ nba.Run xs ss := by
  simp [reindex_run_iff]

/-- Reindexing the states of a Buchi automaton preserves its accepted ω-language. -/
@[simp, scoped grind =]
theorem reindex_language_eq {f : State ≃ State'} {nba : Buchi State Symbol} :
    language (nba.reindex f) = language nba := by
  apply mem_ext
  intro xs
  constructor
  · rintro ⟨ss', h_run', h_acc'⟩
    use ss'.map f.symm
    grind
  · rintro ⟨ss, h_run, h_acc⟩
    use ss.map f
    grind [reindex_run_iff']

end Cslib.Automata.NA.Buchi
