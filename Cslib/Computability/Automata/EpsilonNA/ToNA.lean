/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic

/-! # Translation of εNA into NA -/

@[expose] public section

namespace Cslib

/-- Converts an `LTS` with Option labels into an `LTS` on the carried label type, by removing all
ε-transitions. -/
@[local grind =]
def LTS.noε (lts : LTS State (Option Label)) : LTS State Label where
  Tr s μ s' := lts.Tr s (some μ) s'

@[local grind .]
private lemma LTS.noε_saturate_tr
  {lts : LTS State (Option Label)} {h : μ = some μ'} :
  lts.saturate.Tr s μ s' ↔ lts.saturate.noε.Tr s μ' s' := by
  grind

@[scoped grind =]
lemma LTS.noε_saturate_mTr {lts : LTS State (Option Label)} :
  lts.saturate.MTr s (μs.map some) = lts.saturate.noε.MTr s μs := by
  ext s'
  induction μs generalizing s <;> grind [<= LTS.MTr.stepL]

namespace Automata.εNA.FinAcc

variable {State Symbol : Type*}

/-- Any `εNA.FinAcc` can be converted into an `NA.FinAcc` that does not use ε-transitions. -/
@[scoped grind]
def toNAFinAcc (a : εNA.FinAcc State Symbol) : NA.FinAcc State Symbol where
  start := a.εClosure a.start
  accept := a.accept
  Tr s μ s' := a.STr s (some μ) s'

open Acceptor in
open scoped NA.FinAcc LTS LTS.STr LTS.SMTr in
/-- Correctness of `toNAFinAcc`. -/
@[scoped grind _=_]
theorem toNAFinAcc_language_eq {ena : εNA.FinAcc State Symbol} :
    language ena.toNAFinAcc = language ena := by
  ext xs
  cases xs
  case nil =>
    apply Iff.intro <;> intro h
    case mp =>
      rcases h with ⟨s, hs, s', hs', h⟩
      simp only [toNAFinAcc, εClosure, LTS.τClosure, LTS.setImage, LTS.saturate, Set.mem_iUnion,
        exists_prop] at hs
      rcases hs with ⟨sStart, hStart, hs⟩
      exists sStart
      apply And.intro
      case left => grind
      case right =>
        exists s'
        apply And.intro
        case left => grind
        case right =>
          simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_nil]
          grind [LTS.SMTr.τ]
    case mpr =>
      rcases h with ⟨s, hs, s', hs', h⟩
      simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_nil] at h
      simp [Accepts]
      exists s'
      constructor
      · simp [toNAFinAcc, εClosure, LTS.τClosure, LTS.saturate]
        simp [LTS.setImage]
        exists s
        constructor
        · grind
        · simp [LTS.image]
          cases h
          grind
      · exists s'
        constructor
        · grind
        · grind
  case cons x xs =>
    have : ∀ {s s'}, ena.toNAFinAcc.MTr s (x :: xs) s' = ena.SMTr s (x :: xs) s' := by
      intro s s'
      have := LTS.sMTr_mTr_not_nil (lts := ena.toLTS) (s := s) (s' := s') (μs := some x :: xs.map some) (by simp)
      ext
      apply Iff.intro <;> intro h
      · simp

      · sorry
    simp [Accepts]
    apply Iff.intro <;> intro h
    · rcases h with ⟨s, hs, s', hs', h⟩
      rw [this] at h
      simp [toNAFinAcc] at hs
      have h_start : ∃ sStart ∈ ena.start, ena.τSTr s sStart := by
        sorry
      rcases h_start with ⟨sStart, h_sStart, h_start⟩
      exists sStart
      apply And.intro
      · grind
      · exists s'
        apply And.intro
        · grind
        · grind
    -- simp [LTS.noε_saturate_mTr]
    -- #adaptation_note
    -- /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
    -- grind [Accepts]
  -- have : ∀ s s', ena.MTr s (xs.map some) s' = ena.εMTr s xs s' := by
  --   simp [LTS.noε_saturate_mTr]
  -- #adaptation_note
  -- /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  -- grind [Accepts]

end Automata.εNA.FinAcc

end Cslib
