/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri
-/

module

public import Cslib.Computability.Automata.NA.Basic

/-! # Reversal of nondeterministic automata. -/

@[expose] public section

namespace Cslib.Automata.NA

open Acceptor Language

variable {Symbol State : Type*}

namespace FinAcc

/-- `na.reverse` reverses every transition of `na` and swaps its start and accept states,
so that it accepts exactly the reversals of the words accepted by `na`. -/
def reverse (na : FinAcc State Symbol) : FinAcc State Symbol where
  Tr s x t := na.Tr t x s
  start := na.accept
  accept := na.start

/-- Reversing an automaton twice gives back the original automaton. -/
@[simp]
theorem reverse_reverse (na : FinAcc State Symbol) : na.reverse.reverse = na := rfl

/-- The multistep transitions of `na.reverse` are exactly the reversed multistep transitions
of `na`. -/
theorem reverse_mtr_iff (na : FinAcc State Symbol) {xs : List Symbol} {s s' : State} :
    na.reverse.MTr s' xs s ↔ na.MTr s xs.reverse s' := by
  induction xs generalizing s s' with
  | nil =>
    simp_all [eq_comm]
  | cons x xs ih =>
    simp only [List.reverse_cons]
    simp only [LTS.MTr.cons_iff]
    constructor
    · rintro ⟨mid, h1, h2⟩
      exact LTS.MTr.stepR na.toLTS (ih.mp h2) h1
    · intro hmtr
      obtain ⟨mid, h1, h2⟩ := LTS.MTr.split hmtr
      simp only [LTS.MTr.singleton_iff] at h2
      exact ⟨mid, h2, ih.mpr h1⟩

/-- `na.reverse` accepts exactly the reversals of the words accepted by `na`. -/
theorem reverse_language_eq (na : FinAcc State Symbol) :
    language na.reverse = (language na).reverse := by
  ext xs
  simp only [mem_language, mem_reverse]
  constructor
  · intro h
    simp only [Accepts] at h ⊢
    obtain ⟨s, hs, s', hs', hmtr⟩ := h
    exact ⟨s', hs', s, hs, (reverse_mtr_iff na).mp hmtr⟩
  · intro h_na
    simp only [Accepts] at h_na ⊢
    obtain ⟨s, hs, s', hs', hmtr⟩ := h_na
    exact ⟨s', hs', s, hs, (reverse_mtr_iff na).mpr hmtr⟩

/-- `na.reverse` accepts a word iff `na` accepts its reversal. -/
@[simp]
theorem accepts_reverse {na : FinAcc State Symbol} {xs : List Symbol} :
    Accepts na.reverse xs ↔ Accepts na xs.reverse := by
  exact Set.ext_iff.mp (reverse_language_eq na) xs

end FinAcc

end Cslib.Automata.NA
