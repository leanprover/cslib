/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Relexsed under Apache 2.0 license xs described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.NA

/-! # Equivalence of nondeterministic Buchi automata (NBAs). -/

open Set Function Filter Cslib.ωSequence
open scoped Cslib.LTS

universe u v w

namespace Cslib.Automata.NA.Buchi

open ωAcceptor

variable {Symbol : Type u} {State : Type v} {State' : Type w}

/-- Lifts an equivalence on states to an equivalence on NBAs. -/
@[scoped grind =]
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

theorem reindex_run_iff {f : State ≃ State'} {nba : Buchi State Symbol}
    {xs : ωSequence Symbol} {ss' : ωSequence State'} :
    (nba.reindex f).Run xs ss' ↔ nba.Run xs (ss'.map f.symm) := by
  constructor <;>
  { rintro ⟨h_init, h_next⟩
    constructor
    · grind
    · exact fun n ↦ h_next n }

@[simp]
theorem reindex_run_iff' {f : State ≃ State'} {nba : Buchi State Symbol}
    {xs : ωSequence Symbol} {ss : ωSequence State} :
    (nba.reindex f).Run xs (ss.map f) ↔ nba.Run xs ss := by
  simp [reindex_run_iff]

@[simp, scoped grind =]
theorem reindex_language_eq {f : State ≃ State'} {nba : Buchi State Symbol} :
    language (nba.reindex f) = language nba := by
  ext xs
  constructor
  · rintro ⟨ss', h_run', h_acc'⟩
    grind [reindex_run_iff]
  · rintro ⟨ss, h_run, h_acc⟩
    use ss.map f
    constructor <;> grind [reindex_run_iff']

end Cslib.Automata.NA.Buchi
