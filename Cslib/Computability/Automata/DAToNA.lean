/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.Deterministic.ExactAcceptor
import Cslib.Computability.Automata.Nondeterministic.ExactAcceptor

/-! # Translation of a `DA.ExactAcceptor` into an `NA.ExactAcceptor`.

This is the general version of the standard translation of DFAs into NFAs. -/

namespace Cslib.Automata.DA

variable {State : Type _} {Symbol : Type _}

section NA

-- /-- `DA` is a special case of `NA`. -/
-- @[scoped grind =]
-- def toNA (da : DA State Symbol) : NA State Symbol where
--   start := {da.start}
--   Tr := fun s1 μ s2 => da.tr s1 μ = s2

-- @[scoped grind =]
-- lemma toNA_start {da : DA State Symbol} : da.toNA.start = {da.start} := rfl

-- instance : Coe (DA State Symbol) (NA State Symbol) where
--   coe := toNA


/-- The `NFA` constructed from a `DFA` has the same language. -/
@[scoped grind =]
theorem toNA_exactAcceptor_language_eq {da : DA State Symbol} {acc : Set State} :
    (da.exactAcceptor acc).language = (da.toNA.exactAcceptor acc).language := by
  ext xs
  apply Iff.intro <;> intro h
  case mp =>
    simp_all [NA.exactAcceptor, DA.exactAcceptor, Acceptor.language]

    open NA Acceptor DA in grind
  refine ⟨?_, fun _ => ⟨da.start, ?_⟩⟩ <;> open NA Acceptor in grind

end NA

end Cslib.Automata.DA
