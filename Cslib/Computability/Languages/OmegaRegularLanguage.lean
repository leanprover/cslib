/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DABuchi
import Cslib.Computability.Languages.ExampleEventuallyZero
import Cslib.Computability.Languages.RegularLanguage

/-!
# ω-Regular languages

This file defines ω-regular languages and proves some properties of them.
-/

open Set Function Filter Cslib.ωSequence Cslib.Automata ωAcceptor
open scoped Computability

namespace Cslib.ωLanguage

variable {Symbol : Type*}

/-- An ω-language is ω-regular iff it is accepted by a
finite-state nondeterministic Buchi automaton. -/
def IsRegular (p : ωLanguage Symbol) :=
  ∃ State : Type, ∃ _ : Finite State, ∃ na : NA.Buchi State Symbol, language na = p

/-- The ω-language accepted by a finite-state deterministic Buchi automaton is ω-regular. -/
theorem IsRegular.of_da_buchi {State : Type} [Finite State] (da : DA.Buchi State Symbol) :
    (language da).IsRegular :=
  ⟨State, inferInstance, da.toNABuchi, DA.Buchi.toNABuchi_language_eq⟩

/-- There is an ω-regular language that is not accepted by any deterministic Buchi automaton,
where the automaton is not even required to be finite-state. -/
theorem IsRegular.not_da_buchi :
  ∃ Symbol : Type, ∃ p : ωLanguage Symbol, p.IsRegular ∧
    ¬ ∃ State : Type, ∃ da : DA.Buchi State Symbol, language da = p := by
  refine ⟨Fin 2, Example.eventually_zero, ?_, ?_⟩
  · use Fin 2, inferInstance, Example.eventually_zero_na,
      Example.eventually_zero_accepted_by_na_buchi
  · rintro ⟨State, ⟨da, acc⟩, _⟩
    have := Example.eventually_zero_not_omegaLim
    grind [DA.buchi_eq_finAcc_omegaLim]

/-- The ω-limit of a regular language is ω-regular. -/
theorem IsRegular.regular_omegaLim {l : Language Symbol}
    (h : l.IsRegular) : (l↗ω).IsRegular := by
  obtain ⟨State, _, ⟨da, acc⟩, rfl⟩ := Language.IsRegular.iff_cslib_dfa.mp h
  grind [IsRegular.of_da_buchi, =_ DA.buchi_eq_finAcc_omegaLim]

/-- McNaughton's Theorem. -/
proof_wanted IsRegular.iff_da_muller {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ State : Type, ∃ _ : Finite State, ∃ da : DA.Muller State Symbol, language da = p

end Cslib.ωLanguage
