/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.DFA
import Cslib.Computability.Automata.NFA

/-! # Translation of DFA into NFA -/

namespace DFA
section NFA

/-- `DFA` is a special case of `NFA`. -/
@[scoped grind =]
def toNFA (dfa : DFA State Symbol) : NFA State Symbol where
  start := {dfa.start}
  accept := dfa.accept
  Tr := fun s1 μ s2 => dfa.tr s1 μ = s2
  finite_state := dfa.finite_state
  finite_symbol := dfa.finite_symbol

@[scoped grind =]
lemma toNFA_start {dfa : DFA State Symbol} : dfa.toNFA.start = {dfa.start} := rfl

instance : Coe (DFA State Symbol) (NFA State Symbol) where
  coe := toNFA

/-- `DA.toNA` correctly characterises transitions. -/
@[scoped grind =]
theorem toNA_tr {dfa : DFA State Symbol} :
  dfa.toNFA.Tr s1 μ s2 ↔ dfa.tr s1 μ = s2 := by
  rfl

/-- The transition system of a DA is deterministic. -/
@[scoped grind ⇒]
theorem toNFA_deterministic (dfa : DFA State Symbol) : dfa.toNFA.Deterministic := by
  grind

/-- The transition system of a DA is image-finite. -/
@[scoped grind ⇒]
theorem toNFA_imageFinite (dfa : DFA State Symbol) : dfa.toNFA.ImageFinite :=
  dfa.toNFA.deterministic_imageFinite dfa.toNFA_deterministic

/-- Characterisation of multistep transitions. -/
@[scoped grind =]
theorem toNFA_mtr {dfa : DFA State Symbol} :
  dfa.toNFA.MTr s1 xs s2 ↔ dfa.mtr s1 xs = s2 := by
  have : ∀ x, dfa.toNFA.Tr s1 x (dfa.tr s1 x) := by grind
  constructor <;> intro h
  case mp => induction h <;> grind
  case mpr => induction xs generalizing s1 <;> grind

/-- The `NFA` constructed from a `DFA` has the same language. -/
@[scoped grind =]
theorem toNFA_language_eq {dfa : DFA State Symbol} :
  dfa.toNFA.language = dfa.language := by
  ext xs
  refine ⟨?_, fun _ => ⟨dfa.start, ?_⟩⟩ <;> open NFA in grind

end NFA
end DFA
