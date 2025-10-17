/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.DFA
import Cslib.Computability.Automata.NFA
import Mathlib.Data.Fintype.Powerset

/-! # Translation of NFA into DFA (subset construction) -/

namespace Cslib

namespace NFA
section SubsetConstruction

/-- Converts an `NFA` into a `DFA` using the subset construction. -/
@[scoped grind =]
def toDFA (nfa : NFA State Symbol) : DFA (Set State) Symbol := {
  start := nfa.start
  accept := { S | ∃ s ∈ S, s ∈ nfa.accept }
  tr := nfa.setImage
  finite_state := by
    haveI := nfa.finite_state
    infer_instance
  finite_symbol := nfa.finite_symbol
}

/-- Characterisation of transitions in `NFA.toDFA` wrt transitions in the original NA. -/
@[scoped grind =]
theorem toDFA_mem_tr {nfa : NFA State Symbol} :
  s' ∈ nfa.toDFA.tr S x ↔ ∃ s ∈ S, nfa.Tr s x s' := by
  simp only [NFA.toDFA, LTS.setImage, Set.mem_iUnion, exists_prop]
  grind

/-- Characterisation of multistep transitions in `NFA.toDFA` wrt multistep transitions in the
original NA. -/
@[scoped grind =]
theorem toDFA_mem_mtr {nfa : NFA State Symbol} :
  s' ∈ nfa.toDFA.mtr S xs ↔ ∃ s ∈ S, nfa.MTr s xs s' := by
  simp only [NFA.toDFA, DFA.mtr]
  /- TODO: Grind does not catch a useful rewrite in the subset construction for automata

    A very similar issue seems to occur in the proof of `NFA.toDFA_language_eq`.

    labels: grind, lts, automata
  -/
  rw [← LTS.setImageMultistep_foldl_setImage]
  grind

/-- Characterisation of multistep transitions in `NFA.toDFA` as image transitions in `LTS`. -/
@[scoped grind =]
theorem toDFA_mtr_setImageMultistep {nfa : NFA State Symbol} :
  nfa.toDFA.mtr = nfa.setImageMultistep := by grind

/-- The `DFA` constructed from an `NFA` has the same language. -/
@[scoped grind =]
theorem toDFA_language_eq {nfa : NFA State Symbol} :
  nfa.toDFA.language = nfa.language := by
  ext xs
  rw [← DFA.accepts_mem_language]
  open DFA in grind

end SubsetConstruction
end NFA

end Cslib
