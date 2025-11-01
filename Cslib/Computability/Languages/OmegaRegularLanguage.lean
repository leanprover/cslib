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
-/

open Set Function
open scoped Computability

namespace Cslib

namespace ωLanguage

variable {Symbol : Type*}

def IsRegular (p : ωLanguage Symbol) :=
  ∃ State : Type, ∃ _ : Finite State, ∃ na : NA State Symbol, ∃ acc : Set State,
  na.buchiLanguage acc = p

-- /-- McNaughton's theorem, which will take a lot of work to reach. -/
-- theorem IsRegular.iff_muller_lang {p : ωLanguage Symbol} :
--     p.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
--       ∃ da : DA State Symbol, ∃ accSet : Set (Set State), da.mullerLanguage accSet = p := by
--   sorry

end ωLanguage

end Cslib
