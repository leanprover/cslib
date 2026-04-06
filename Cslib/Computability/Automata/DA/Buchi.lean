/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.DA.Basic

public section

/-! # Deterministic Buchi automata.
-/

open Filter

namespace Cslib.Automata.DA

open scoped FinAcc Buchi

variable {State Symbol : Type*}

open Acceptor ωAcceptor in
/-- The ω-language accepted by a deterministic Buchi automaton is the ω-limit
of the language accepted by the same automaton.
-/
@[scoped grind =]
theorem buchi_eq_finAcc_omegaLim {da : DA State Symbol} {acc : Set State} :
    language (Buchi.mk da acc) = (language (FinAcc.mk da acc))↗ω := by
  ext xs
  simp +instances

end Cslib.Automata.DA
