/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Foundations.Semantics.LTS.MapLabel

/-! # Translation of εNA into NA -/

@[expose] public section

namespace Cslib.Automata.εNA.FinAcc

variable {State Symbol : Type*}

/-- Any `εNA.FinAcc` can be converted into an `NA.FinAcc` that does not use ε-transitions. -/
@[scoped grind]
def toNAFinAcc (a : εNA.FinAcc State Symbol) : NA.FinAcc State Symbol where
  start := a.εClosure a.start
  accept := a.accept
  toLTS := a.saturate.mapLabel Option.some

open Acceptor in
open scoped NA.FinAcc LTS LTS.MTr LTS.STr LTS.SMTr in
/-- Correctness of `toNAFinAcc`. -/
@[scoped grind =]
theorem toNAFinAcc_language_eq {a : εNA.FinAcc State Symbol} :
    language a.toNAFinAcc = language a := by
  ext xs
  apply Iff.intro <;> rintro ⟨s, hs, s', hs', h⟩
  case mp =>
    have h_start : ∃ sStart ∈ a.start, a.τSTr sStart s := by
      simp only [toNAFinAcc, εClosure, LTS.τClosure, LTS.setImage, Set.mem_iUnion,
        exists_prop] at hs
      rcases hs with ⟨sStart, h_sStart, hs⟩
      exists sStart
      apply And.intro h_sStart
      simp only [LTS.image, LTS.saturate, Set.mem_setOf_eq] at hs
      grind only [LTS.sTr_τSTr_iff]
    rcases h_start with ⟨sStart, h_sStart, h_start⟩
    exists sStart
    apply And.intro (by grind)
    exists s'
    apply And.intro (by grind)
    apply LTS.SMTr.comp (μs₁ := []) (s₂ := s) <;> grind
  case mpr =>
    cases xs with
    | nil =>
      exists s'
      simp only [toNAFinAcc, LTS.saturate, LTS.τClosure]
      grind [cases LTS.SMTr]
    | cons x xs =>
      exists s
      grind

end Cslib.Automata.εNA.FinAcc
