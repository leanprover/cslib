/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic

/-! # Product of nondeterministic automata. -/

@[expose] public section

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
  constructor
  · intro h i
    exact ⟨mem_iInter.mp h.start i, fun n => h.trans n i⟩
  · intro h
    exact ⟨mem_iInter.mpr fun i => (h i).start, fun n i => (h i).trans n⟩

end Cslib.Automata.NA
