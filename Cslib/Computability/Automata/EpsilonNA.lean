/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.NA

/-! # Nondeterministic automata with ε-transitions. -/

/-- A nondeterministic automaton with ε-transitions (`εNA`) is an `NA` with an `Option` symbol
type. The special symbol ε is represented by the `Option.none` case.

Internally, ε (`Option.none`) is treated as the `τ` label of the underlying transition system,
allowing for reusing the definitions and results on saturated transitions of `LTS` to deal with
ε-closure. -/
structure εNA (State : Type _) (Symbol : Type _) extends NA State (Option Symbol)

@[grind]
private instance : HasTau (Option α) := ⟨.none⟩

/-- The `ε`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `ε`-transitions. We use `LTS.τClosure` since `ε` (`Option.none`) is an instance
of `HasTau.τ`. -/
abbrev εNA.εClosure (ena : εNA State Symbol) (S : Set State) := ena.τClosure S

/-- Converts an `LTS` with Option labels into an `LTS` on the carried label type, by removing all
ε-transitions. -/
@[grind]
private def LTS.noε (lts : LTS State (Option Label)) :
  LTS State Label := {
  Tr := fun s μ s' => lts.Tr s (some μ) s'
}

namespace εNA

/-- An εNA accepts a string if there is a saturated multistep accepting derivative with that trace
from the start state. -/
@[grind]
def Accepts (ena : εNA State Symbol) (xs : List Symbol) :=
  ∃ s ∈ ena.εClosure ena.start, ∃ s' ∈ ena.accept,
  ena.saturate.MTr s (xs.map (some ·)) s'

/-- The language of an εDA is the set of strings that it accepts. -/
@[grind]
def language (ena : εNA State Symbol) : Set (List Symbol) :=
  { xs | ena.Accepts xs }

/-- A string is accepted by an εNA iff it is in the language of the NA. -/
@[grind]
theorem accepts_mem_language (ena : εNA State Symbol) (xs : List Symbol) :
  ena.Accepts xs ↔ xs ∈ ena.language := by rfl

section NA

/-- Any εNA can be converted into an NA that does not use ε-transitions. -/
@[grind]
def toNAWithoutEpsilon (ena : εNA State Symbol) : NA State Symbol := {
  start := ena.εClosure ena.start
  accept := ena.accept
  Tr := ena.saturate.noε.Tr
}

@[grind]
lemma LTS.noε_saturate_tr
  {lts : LTS State (Option Label)} {h : μ = some μ'} :
  lts.saturate.Tr s μ s' ↔ lts.saturate.noε.Tr s μ' s' := by
  simp only [LTS.noε]
  grind

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
theorem toNAWithoutEpsilon_language_eq {ena : εNA State Symbol} :
  ena.toNAWithoutEpsilon.language = ena.language := by
  ext xs
  apply Iff.intro
  case mp =>
    rw [← εNA.accepts_mem_language, ← NA.accepts_mem_language]
    simp only [NA.Accepts, toNAWithoutEpsilon, Accepts, forall_exists_index, and_imp]
    intro s hs s' hs' hmtr
    exists s
    apply And.intro hs
    exists s'
    apply And.intro hs'
    rw [LTS.noε_saturate_mTr]
    assumption
  case mpr =>
    rw [← εNA.accepts_mem_language, ← NA.accepts_mem_language]
    simp only [NA.Accepts, toNAWithoutEpsilon, Accepts, forall_exists_index, and_imp]
    intro s hs s' hs' hmtr
    exists s
    apply And.intro hs
    exists s'
    apply And.intro hs'
    rw [← LTS.noε_saturate_mTr]
    assumption

end NA

end εNA
