/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.RegularLanguage

@[expose] public section

/-! # Languages determined by pairs of states
-/

namespace Cslib

open Language Automata Acceptor

variable {Symbol : Type*} {State : Type}

/-- `LTS.pairLang s t` is the language of finite words that can take the LTS
from state `s` to state `t`. -/
def LTS.pairLang (lts : LTS State Symbol) (s t : State) : Language Symbol :=
  { xl | lts.MTr s xl t }

@[simp, scoped grind =]
theorem LTS.mem_pairLang (lts : LTS State Symbol) (s t : State) (xl : List Symbol) :
    xl ∈ (lts.pairLang s t) ↔ lts.MTr s xl t := Iff.rfl

/-- `LTS.pairLang s t` is a regular language if there are only finitely many states. -/
@[simp]
theorem LTS.pairLang_regular [Finite State] (lts : LTS State Symbol) (s t : State) :
    (lts.pairLang s t).IsRegular := by
  rw [IsRegular.iff_nfa]
  use State, inferInstance, (NA.FinAcc.mk ⟨lts, {s}⟩ {t})
  ext xl; simp [LTS.mem_pairLang]

namespace NA.Buchi

open Set Filter ωSequence ωLanguage ωAcceptor

/-- The ω-language accepted by a finite-state Büchi automaton is the finite union of ω-languages
of the form `L * M^ω`, where all `L`s and `M`s are regular languages. -/
theorem language_eq_fin_iSup_hmul_omegaPow
    [Inhabited Symbol] [Finite State] (na : NA.Buchi State Symbol) :
    language na = ⨆ s ∈ na.start, ⨆ t ∈ na.accept, (na.pairLang s t) * (na.pairLang t t)^ω := by
  ext xs
  simp only [NA.Buchi.instωAcceptor, ωAcceptor.mem_language,
    ωLanguage.mem_iSup, ωLanguage.mem_hmul, LTS.mem_pairLang]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨t, _, h_t⟩ := frequently_in_finite_type.mp h_inf
    refine ⟨ss 0, by grind [h_run.start], t, by assumption, ?_⟩
    obtain ⟨f, h_mono, h_f⟩ := frequently_iff_strictMono.mp h_t
    refine ⟨xs.take (f 0), ?_, xs.drop (f 0), ?_, by grind⟩
    · grind [extract_eq_drop_take, LTS.ωTr_mTr h_run.trans (Nat.zero_le (f 0))]
    · simp only [omegaPow_seq_prop, LTS.mem_pairLang]
      refine ⟨(f · - f 0), by grind [Nat.base_zero_strictMono], by simp, ?_⟩
      intro n
      grind [extract_drop, h_mono.monotone (Nat.zero_le n), h_mono.monotone (Nat.zero_le (n + 1)),
        LTS.ωTr_mTr h_run.trans <| h_mono.monotone (show n ≤ n + 1 by grind)]
  · rintro ⟨s, _, t, _, yl, h_yl, zs, h_zs, rfl⟩
    obtain ⟨zls, rfl, h_zls⟩ := mem_omegaPow.mp h_zs
    let ts := ωSequence.const t
    have h_mtr (n : ℕ) : na.MTr (ts n) (zls n) (ts (n + 1)) := by
      grind [Language.mem_sub_one, LTS.mem_pairLang]
    have h_pos (n : ℕ) : (zls n).length > 0 := by
      grind [Language.mem_sub_one, List.eq_nil_iff_length_eq_zero]
    obtain ⟨zss, h_zss, _⟩ := LTS.ωTr.flatten h_mtr h_pos
    have (n : ℕ) : zss (zls.cumLen n) = t := by grind
    obtain ⟨xss, _, _, _, _⟩ := LTS.ωTr.append h_yl h_zss (by grind [cumLen_zero (ls := zls)])
    refine ⟨xss, by grind [NA.Run.mk], ?_⟩
    apply (drop_frequently_iff_frequently yl.length).mp
    apply frequently_iff_strictMono.mpr
    use zls.cumLen
    grind [cumLen_strictMono]

end NA.Buchi

end Cslib
