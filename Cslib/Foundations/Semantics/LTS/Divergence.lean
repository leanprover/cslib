/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.HasTau
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Divergence of LTS
-/

@[expose] public section

namespace Cslib.LTS

universe u v

/-- An infinite trace is divergent if every label within it is τ. -/
def DivergentTrace [HasTau Label] (μs : ωSequence Label) := ∀ i, μs i = HasTau.τ

/-- A state is divergent if there is a divergent execution from it. -/
def Divergent [HasTau Label] (lts : LTS State Label) (s : State) : Prop :=
  ∃ ss μs, lts.OmegaExecution ss μs ∧ ss 0 = s ∧ DivergentTrace μs

/-- If a trace is divergent, then any 'suffix' is also divergent. -/
@[scoped grind ⇒]
theorem divergentTrace_drop
    [HasTau Label] {μs : ωSequence Label}
    (h : DivergentTrace μs) (n : ℕ) :
    DivergentTrace (μs.drop n) := by
  intro m
  simp only [DivergentTrace] at h
  simp only [ωSequence.get_fun, ωSequence.drop]
  grind

/-- An LTS is divergence-free if it has no divergent state. -/
class DivergenceFree [HasTau Label] (lts : LTS State Label) where
  divergence_free : ¬∃ s, lts.Divergent s

end Cslib.LTS
