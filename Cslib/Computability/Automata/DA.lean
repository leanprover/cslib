/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.NA

/-! # Deterministic Automaton

A Deterministic Automaton (DA) is an automaton defined by a transition function.
-/
structure DA (State : Type _) (Symbol : Type _) where
  /-- The initial state of the automaton. -/
  start : State
  /-- The set of accepting states of the automaton. -/
  accept : Set State
  /-- The transition function of the automaton. -/
  tr : State → Symbol → State

namespace DA

/-- Extended transition function.

Implementation note: compared to [Hopcroft2006], the definition consumes the input list of symbols
from the left (instead of the right), in order to match the way lists are constructed.
-/
@[grind]
def mtr (da : DA State Symbol) (s : State) (xs : List Symbol) := xs.foldl da.tr s
  -- match xs with
  -- | [] => s
  -- | x :: xs => da.mtr (da.tr s x) xs

@[grind]
theorem mtr_nil_eq {da : DA State Symbol} : da.mtr s [] = s := by rfl

/-- A DA accepts a string if there is a multi-step accepting derivative with that trace from
the start state. -/
@[grind]
def Accepts (da : DA State Symbol) (xs : List Symbol) :=
  (da.mtr da.start xs) ∈ da.accept

/-- The language of a DA is the set of strings that it accepts. -/
@[grind]
def language (da : DA State Symbol) : Set (List Symbol) :=
  { xs | da.Accepts xs }

/-- A string is accepted by a DA iff it is in the language of the DA. -/
@[grind]
theorem accepts_mem_language (da : DA State Symbol) (xs : List Symbol) :
  da.Accepts xs ↔ xs ∈ da.language := by rfl

/-! # From DA to NA -/

section NA

/-- `DA` is a special case of `NA`. -/
@[grind]
def toNA (da : DA State Symbol) : NA State Symbol := {
  start := {da.start}
  accept := da.accept
  Tr := fun s1 μ s2 => da.tr s1 μ = s2
}

@[grind]
lemma toNA_start {da : DA State Symbol} : da.toNA.start = {da.start} := rfl

instance : Coe (DA State Symbol) (NA State Symbol) where
  coe := toNA

/-- `DA.toNA` correctly characterises transitions. -/
@[grind]
theorem toNA_tr {da : DA State Symbol} :
  da.toNA.Tr s1 μ s2 ↔ da.tr s1 μ = s2 := by
  rfl

/-- Characterisation of multistep transitions. -/
@[grind]
theorem toNA_mtr {da : DA State Symbol} :
  da.toNA.MTr s1 xs s2 ↔ da.mtr s1 xs = s2 := by
  constructor <;> intro h
  case mp =>
    induction h <;> grind
  case mpr =>
    induction xs generalizing s1
    case nil => grind
    case cons x xs ih =>
      apply LTS.MTr.stepL (s2 := da.tr s1 x) <;> grind

/-- The transition system of a DA is deterministic. -/
@[grind]
theorem toNA_deterministic (da : DA State Symbol) : da.toNA.Deterministic := by grind

/-- The transition system of a DA is image-finite. -/
@[grind]
theorem toNA_imageFinite (da : DA State Symbol) : da.toNA.ImageFinite :=
  da.toNA.deterministic_imageFinite da.toNA_deterministic

/-- The `NA` constructed from a `DA` has the same language. -/
@[grind]
theorem toNA_language_eq {da : DA State Symbol} :
  da.toNA.language = da.language := by
  ext xs
  rw [← DA.accepts_mem_language, ← NA.accepts_mem_language]
  simp only [NA.Accepts, DA.Accepts]
  apply Iff.intro <;> intro h
  case mp =>
    grind
  case mpr =>
    exists da.start
    grind

end NA

end DA

/-! # Subset construction (conversion from NA to DA) -/
section SubsetConstruction

/-- Converts an `NA` into a `DA` using the subset construction. -/
@[grind]
def NA.toDA (na : NA State Symbol) : DA (Set State) Symbol := {
  start := na.start
  accept := { S | ∃ s ∈ S, s ∈ na.accept }
  tr := na.setImage
}

/-- Characterisation of transitions in `NA.toDA` wrt transitions in the original NA. -/
@[grind]
theorem NA.toDA_mem_tr {na : NA State Symbol} :
  s' ∈ na.toDA.tr S x ↔ ∃ s ∈ S, na.Tr s x s' := by
  simp only [NA.toDA, LTS.setImage, Set.mem_iUnion, exists_prop]
  grind

/-- Characterisation of multistep transitions in `NA.toDA` wrt multistep transitions in the
original NA. -/
@[grind]
theorem NA.toDA_mem_mtr {na : NA State Symbol} :
  s' ∈ na.toDA.mtr S xs ↔ ∃ s ∈ S, na.MTr s xs s' := by
  simp only [NA.toDA, DA.mtr]
  /- TODO: Grind does not catch a useful rewrite in the subset construction for automata

    A very similar issue seems to occur in the proof of `NA.toDA_language_eq`.

    labels: grind, lts, automata
  -/
  rw [← LTS.setImageMultistep_foldl_setImage]
  grind

/-- Characterisation of multistep transitions in `NA.toDA` as image transitions in `LTS`. -/
@[grind]
theorem NA.toDA_mtr_setImageMultistep {na : NA State Symbol} :
  na.toDA.mtr = na.setImageMultistep := by grind

/-- The `DA` constructed from an `NA` has the same language. -/
@[grind]
theorem NA.toDA_language_eq {na : NA State Symbol} :
  na.toDA.language = na.language := by
  ext xs
  rw [← DA.accepts_mem_language, ← NA.accepts_mem_language]
  grind

end SubsetConstruction
