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
private def LTS.noε (lts : LTS State (Option Label)) : LTS State Label where
  Tr := fun s μ s' => lts.Tr s (some μ) s'

@[local grind]
private lemma LTS.noε_saturate_tr
  {lts : LTS State (Option Label)} {h : μ = some μ'} :
  lts.saturate.Tr s μ s' ↔ lts.saturate.noε.Tr s μ' s' := by
  simp only [LTS.noε]
  grind

namespace εNFA
section NFA

/-- Any εNFA can be converted into an NFA that does not use ε-transitions. -/
@[scoped grind]
def toNFA (enfa : εNFA State Symbol) : NFA State Symbol where
  start := enfa.εClosure enfa.start
  accept := enfa.accept
  Tr := enfa.saturate.noε.Tr
  finite_state := enfa.finite_state
  finite_symbol := enfa.finite_symbol

@[scoped grind]
lemma LTS.noε_saturate_mTr
  {lts : LTS State (Option Label)} :
  lts.saturate.MTr s (μs.map (some ·)) = lts.saturate.noε.MTr s μs := by
  ext s'
  induction μs generalizing s <;> grind [<= LTS.MTr.stepL]


/-- Correctness of `toNFA`. -/
@[scoped grind]
theorem toNFA_language_eq {enfa : εNFA State Symbol} :
  enfa.toNFA.language = enfa.language := by
  ext xs
  have : ∀ s s', enfa.saturate.MTr s (xs.map (some ·)) s' = enfa.saturate.noε.MTr s xs s' := by
    simp [LTS.noε_saturate_mTr]
  open NFA in grind

end NFA
end εNFA
