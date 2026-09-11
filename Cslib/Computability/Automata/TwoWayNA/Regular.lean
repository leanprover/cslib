/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.TwoWayNA.OfNA
public import Cslib.Computability.Automata.TwoWayNA.ToNA
public import Cslib.Computability.Languages.RegularLanguage

/-! # Two-way automata recognise exactly the regular languages

This is the combination of the results of `NA.FinAcc.toTwoWayNA` and `TwoWayNA.toNAComplement`
plus the fact that regular languages are closed under complementation.
-/

namespace Cslib.Language

open Automata Acceptor

/-- A language is regular if and only if it is accepted by some two-way nondeterministic
automaton with finitely many states. -/
public theorem IsRegular.iff_twoWayNA {Symbol : Type*} {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
      ∃ a : Automata.TwoWayNA State Symbol, language a = l := by
  constructor
  · intro h
    rw [IsRegular.iff_nfa] at h
    obtain ⟨State, hfin, na, rfl⟩ := h
    exact ⟨State, hfin, NA.FinAcc.toTwoWayNA na, TwoWayNA.language_toTwoWayNA na⟩
  · rintro ⟨State, hfin, a, rfl⟩
    have := hfin
    have hc : (language a)ᶜ.IsRegular := by
      rw [IsRegular.iff_nfa]
      exact ⟨Set State × Set State, inferInstance, a.toNAComplement, a.language_toNAComplement⟩
    simpa using hc.compl

end Cslib.Language
