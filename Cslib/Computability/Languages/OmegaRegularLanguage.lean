/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DA
import Cslib.Computability.Automata.NA
import Mathlib.Tactic

/-!
# ω-Regular languages

This file defines ω-regular languages and proves some properties of them.
-/

open Set Function
open scoped Computability

namespace Cslib

namespace ωLanguage

variable {Symbol : Type*}

/-- An ω-regular language is one that is accepted by a finite-state Buchi automaton. -/
def IsRegular (p : ωLanguage Symbol) :=
  ∃ State : Type, ∃ _ : Finite State, ∃ na : NA.Buchi State Symbol, na.language = p

/-- There is an ω-regular language which is not accepted by any deterministic Buchi automaton. -/
proof_wanted IsRegular.not_det_buchi :
  ∃ p : ωLanguage Symbol, p.IsRegular ∧
    ¬ ∃ State : Type, ∃ _ : Finite State, ∃ da : DA.Buchi State Symbol, da.language = p

/-- McNaughton's Theorem. -/
proof_wanted IsRegular.iff_muller_lang {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ State : Type, ∃ _ : Finite State, ∃ da : DA.Muller State Symbol, da.language = p

end ωLanguage

end Cslib
