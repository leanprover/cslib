/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DA
import Cslib.Computability.Automata.NA
import Cslib.Computability.Automata.DAToNA
import Cslib.Computability.Automata.DABuchi
import Cslib.Computability.Languages.RegularLanguage
import Mathlib.Tactic

/-!
# ω-Regular languages

This file defines ω-regular languages and proves some properties of them.
-/

open Set Function Cslib.Automata.ωAcceptor
open scoped Computability
open Cslib.Automata

namespace Cslib.ωLanguage

variable {Symbol : Type*}

/-- An ω-language is ω-regular iff it is accepted by a
finite-state nondeterministic Buchi automaton. -/
def IsRegular (p : ωLanguage Symbol) :=
  ∃ State : Type, ∃ _ : Finite State, ∃ na : NA.Buchi State Symbol, language na = p

/-- The ω-language accepted by a finite-state deterministic Buchi automaton is ω-regular. -/
theorem IsRegular.of_da_buchi {State : Type} [Finite State] (da : DA.Buchi State Symbol) :
    (language da).IsRegular := by
  use State, inferInstance, da.toNABuchi
  simp

/-- The ω-limit of a regular language is ω-regular. -/
theorem IsRegular.regular_omegaLim {l : Language Symbol}
    (h : l.IsRegular) : (l↗ω).IsRegular := by
  obtain ⟨State, _, ⟨da, acc⟩, rfl⟩ := Language.IsRegular.iff_cslib_dfa.mp h
  rw [← DA.buchi_eq_finAcc_omegaLim]
  apply IsRegular.of_da_buchi

/-- There is an ω-regular language that is not accepted by any deterministic Buchi automaton. -/
proof_wanted IsRegular.not_da_buchi :
  ∃ p : ωLanguage Symbol, p.IsRegular ∧
    ¬ ∃ State : Type, ∃ _ : Finite State, ∃ da : DA.Buchi State Symbol, language da = p

/-- McNaughton's Theorem. -/
proof_wanted IsRegular.iff_da_muller {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ State : Type, ∃ _ : Finite State, ∃ da : DA.Muller State Symbol, language da = p

end Cslib.ωLanguage
