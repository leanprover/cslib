/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.NA

structure εNA (State : Type _) (Symbol : Type _) extends NA State (Option Symbol)

private instance : HasTau (Option α) := ⟨.none⟩

namespace εNA

/-- An εNA accepts a string if there is a saturated multistep accepting derivative with that trace
from the start state. -/
@[grind]
def Accepts (ena : εNA State Symbol) (xs : List Symbol) :=
  ∃ s ∈ ena.start, ∃ s' ∈ ena.accept, ena.saturate.MTr s xs s'

/-- The language of an εDA is the set of strings that it accepts. -/
@[grind]
def language (ena : εNA State Symbol) : Set (List Symbol) :=
  { xs | ena.Accepts xs }

/-- A string is accepted by an εNA iff it is in the language of the NA. -/
@[grind]
theorem accepts_mem_language (ena : εNA State Symbol) (xs : List Symbol) :
  ena.Accepts xs ↔ xs ∈ ena.language := by rfl

section NA

@[grind]
def toNAWithoutEpsilon (ena : εNA State Symbol) : NA State Symbol := {
  start := ena.setImage ena.start HasTau.τ
  accept := ena.accept
  Tr := fun s x s' => ena.saturate.Tr s (some x) s'
}

-- theorem toNAWithoutEpsilon_language_eq {ena : εNA State Symbol} :
--   ena.toNAWithoutEpsilon.language = ena.language := by
--   grind

end NA

end εNA
