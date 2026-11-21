/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Semantics.LTS.Total

/-! # Making a nondeterministic automaton total.
-/

@[expose] public section

namespace Cslib.Automata.NA

open Option ωSequence Acceptor
open scoped Run

variable {Symbol State : Type*}

/-- `NA.totalize` makes the original NA total by replacing its LTS with `LTS.totalize`
and its starting states with their lifted non-sink versions. -/
def totalize (na : NA State Symbol) : NA (Option State) Symbol where
  toLTS := na.toLTS.totalize
  start := some '' na.start

variable {na : NA State Symbol}

/-- The underlying LTS of `na.totalize` is `na.toLTS.totalize`. -/
@[scoped grind =]
theorem totalize_toLTS : na.totalize.toLTS = na.toLTS.totalize := rfl

/-- The automaton constructed by `NA.totalize` is total. -/
instance (na : NA State Symbol) : na.totalize.Total :=
  inferInstanceAs na.toLTS.totalize.Total

/-- Characterization of initial states in `na.totalize`. -/
@[simp, scoped grind =]
theorem mem_totalize_start {s' : Option State} :
    s' ∈ na.totalize.start ↔ ∃ s ∈ na.start, some s = s' :=
  Set.mem_image _ _ _

/-- Transitions between non-sink states in `na.totalize` correspond to transitions in `na`. -/
@[simp]
theorem totalize_tr_some_iff {x : Symbol} {s t : State} :
    na.totalize.Tr (some s) x (some t) ↔ na.Tr s x t :=
  LTS.totalize.nonsink_tr_iff

/-- Multistep transitions between non-sink states in `na.totalize` correspond to multistep
transitions in `na`. -/
@[simp, scoped grind =]
theorem totalize_mtr_some_iff {xl : List Symbol} {s t : State} :
    na.totalize.MTr (some s) xl (some t) ↔ na.MTr s xl t :=
  LTS.totalize.nonsink_mtr_iff

/-- In an infinite execution of `NA.totalize`, as long as the NA stays in a non-sink state,
the execution so far corresponds to a finite execution of the original NA. -/
theorem totalize_run_mtr {xs : ωSequence Symbol} {ss : ωSequence (Option State)} {n : ℕ}
    (h : na.totalize.Run xs ss) (hl : (ss n).isSome) :
    ∃ s t, na.MTr s (xs.take n) t ∧ s ∈ na.start ∧ ss 0 = some s ∧ ss n = some t := by
  grind [isSome_iff_exists, extract_eq_take, LTS.OmegaExecution.extract_mTr h.trans (Nat.zero_le n)]

/-- Any finite execution of the original NA can be extended to an infinite execution of
`NA.totalize`, provided that the alphabet is inbabited. -/
theorem totalize_mtr_run [Inhabited Symbol] {xl : List Symbol} {s t : State}
    (hs : s ∈ na.start) (hm : na.MTr s xl t) :
    ∃ xs ss, na.totalize.Run (xl ++ω xs) ss ∧ ss 0 = some s ∧ ss xl.length = some t := by
  grind [Run.intro, LTS.Total.extend_omegaExecution <| totalize_mtr_some_iff.mpr hm]

namespace FinAcc

/-- `NA.totalize` and the original NA accept the same language of finite words,
as long as the accepting states are also lifted in the obvious way. -/
theorem totalize_language_eq {na : FinAcc State Symbol} :
    language (FinAcc.mk na.totalize (some '' na.accept)) = language na := by
  ext xl
  simp +instances

end FinAcc

end Cslib.Automata.NA
