/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.EpsilonNFA
import Cslib.Computability.Automata.NFA

/-! # Translation of εNFA into NFA -/

/-- Converts an `LTS` with Option labels into an `LTS` on the carried label type, by removing all
ε-transitions. -/
@[grind]
private def LTS.noε (lts : LTS State (Option Label)) :
  LTS State Label := {
  Tr := fun s μ s' => lts.Tr s (some μ) s'
}

@[grind]
private lemma LTS.noε_saturate_tr
  {lts : LTS State (Option Label)} {h : μ = some μ'} :
  lts.saturate.Tr s μ s' ↔ lts.saturate.noε.Tr s μ' s' := by
  simp only [LTS.noε]
  grind

namespace εNFA

section NFA

/-- Any εNFA can be converted into an NFA that does not use ε-transitions. -/
@[grind]
def toNFA (enfa : εNFA State Symbol) : NFA State Symbol := {
  start := enfa.εClosure enfa.start
  accept := enfa.accept
  Tr := enfa.saturate.noε.Tr
  finite_state := enfa.finite_state
  finite_symbol := enfa.finite_symbol
}

@[grind]
lemma LTS.noε_saturate_mTr
  {lts : LTS State (Option Label)} :
  lts.saturate.MTr s (μs.map (some ·)) = lts.saturate.noε.MTr s μs := by
  ext s'
  induction μs generalizing s
  case nil => grind
  case cons μ μs ih =>
    apply Iff.intro <;> intro h
    case mp =>
      simp only [LTS.noε]
      cases h
      rename_i sb htr hmtr
      apply LTS.MTr.stepL (s1 := s) (s2 := sb) (s3 := s') <;> grind
    case mpr =>
      simp only [LTS.noε] at h
      grind


/-- Correctness of `toNAWithoutEpsilon`. -/
@[grind]
theorem toNAWithoutEpsilon_language_eq {enfa : εNFA State Symbol} :
  enfa.toNFA.language = enfa.language := by
  ext xs
  apply Iff.intro
  case mp =>
    rw [← εNFA.accepts_mem_language, ← NFA.accepts_mem_language]
    simp only [NFA.Accepts, toNFA, Accepts, forall_exists_index, and_imp]
    intro s hs s' hs' hmtr
    exists s
    apply And.intro hs
    exists s'
    apply And.intro hs'
    rw [LTS.noε_saturate_mTr]
    assumption
  case mpr =>
    rw [← εNFA.accepts_mem_language, ← NFA.accepts_mem_language]
    simp only [NFA.Accepts, toNFA, Accepts, forall_exists_index, and_imp]
    intro s hs s' hs' hmtr
    exists s
    apply And.intro hs
    exists s'
    apply And.intro hs'
    rw [← LTS.noε_saturate_mTr]
    assumption

end NFA

end εNFA
