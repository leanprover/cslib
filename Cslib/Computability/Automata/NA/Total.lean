/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic

@[expose] public section

/-! # Making a nondeterministic automaton total.
-/

namespace Cslib.Automata.NA

open Sum ωSequence Acceptor

variable {Symbol State : Type*}

/-- `NA.totalize` makes the original NA total by replacing its LTS with `LTS.totalize`
and its starting states with their lifted non-sink versions. -/
def totalize (na : NA State Symbol) : NA (State ⊕ Unit) Symbol where
  toLTS := na.toLTS.totalize
  start := inl '' na.start

variable {na : NA State Symbol}

/-- In an infinite execution of `NA.totalize`, as long as the NA stays in a non-sink state,
the execution so far corresponds to a finite execution of the original NA. -/
theorem totalize_run_mtr {xs : ωSequence Symbol} {ss : ωSequence (State ⊕ Unit)} {n : ℕ}
    (h : na.totalize.Run xs ss) (hl : (ss n).isLeft) :
    ∃ s t, na.MTr s (xs.take n) t ∧ s ∈ na.start ∧ ss 0 = inl s ∧ ss n = inl t := by
  obtain ⟨s, _, eq₁⟩ := h.start
  obtain ⟨t, eq₂⟩ := isLeft_iff.mp hl
  use s, t
  refine ⟨?_, by grind⟩
  -- TODO: `grind` does not use congruence relations with `na.totalize.MTr`
  rw [← LTS.totalize.mtr_left_iff, ← extract_eq_take, eq₁, ← eq₂]
  exact LTS.ωTr_mTr h.trans (by grind)

/-- Any finite execution of the original NA can be extended to an infinite execution of
`NA.totalize`, provided that the alphabet is inbabited. -/
theorem totalize_mtr_run [Inhabited Symbol] {xl : List Symbol} {s t : State}
    (hs : s ∈ na.start) (hm : na.MTr s xl t) :
    ∃ xs ss, na.totalize.Run (xl ++ω xs) ss ∧ ss 0 = inl s ∧ ss xl.length = inl t := by
  grind [totalize, Run, LTS.Total.mTr_ωTr <| LTS.totalize.mtr_left_iff.mpr hm]

namespace FinAcc

/-- `NA.totalize` and the original NA accept the same language of finite words,
as long as the accepting states are also lifted in the obvious way. -/
theorem totalize_language_eq {na : FinAcc State Symbol} :
    language (FinAcc.mk na.totalize (inl '' na.accept)) = language na := by
  ext xl
  simp +instances [totalize]

end FinAcc

end Cslib.Automata.NA
