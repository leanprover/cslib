/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic

@[expose] public section

/-! # Product of nondeterministic automata. -/

namespace Cslib.Automata.NA

open Set List Cslib.ωSequence
open scoped LTS

variable {Symbol I : Type*} {State : I → Type*}

/-- The product of an indexed family of nondeterministic automata. -/
@[scoped grind =]
def iProd (na : (i : I) → NA (State i) Symbol) : NA (Π i, State i) Symbol where
  Tr s x t := ∀ i, (na i).Tr (s i) x (t i)
  start := ⋂ i, (· i) ⁻¹' (na i).start

/-- Every run of the product automaton projects onto runs of its component automata,
and vice versa. -/
@[simp, scoped grind =]
theorem iProd_run_iff {na : (i : I) → NA (State i) Symbol}
    {xs : ωSequence Symbol} {ss : ωSequence (Π i, State i)} :
    (iProd na).Run xs ss ↔ ∀ i, (na i).Run xs (ss.map (· i)) := by
  rw [iProd]
  constructor
  · rintro ⟨h_start, h_trans⟩
    simp only [mem_iInter] at h_start
    grind [Run]
  · intro h
    constructor
    · simp only [mem_iInter]
      grind [Run]
    · intro n i
      exact (h i).trans n

end Cslib.Automata.NA
