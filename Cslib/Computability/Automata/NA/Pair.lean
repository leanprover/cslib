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
  { xs | lts.MTr s xs t }

@[simp, scoped grind =]
theorem LTS.mem_pairLang {lts : LTS State Symbol} {s t : State} {xs : List Symbol} :
    xs ∈ lts.pairLang s t ↔ lts.MTr s xs t := Iff.rfl

/-- `LTS.pairLang s t` is a regular language if there are only finitely many states. -/
@[simp]
theorem LTS.pairLang_regular [Finite State] {lts : LTS State Symbol} {s t : State} :
    (lts.pairLang s t).IsRegular := by
  rw [IsRegular.iff_nfa]
  use State, inferInstance, (NA.FinAcc.mk ⟨lts, {s}⟩ {t})
  ext
  simp +instances

/-- `LTS.pairViaLang via s t` is the language of finite words that can take the LTS
from state `s` to state `t` via a state in `via`. -/
def LTS.pairViaLang (lts : LTS State Symbol) (via : Set State) (s t : State) : Language Symbol :=
  ⨆ r ∈ via, lts.pairLang s r * lts.pairLang r t

@[simp, scoped grind =]
theorem LTS.mem_pairViaLang {lts : LTS State Symbol} {via : Set State}
    {s t : State} {xs : List Symbol} : xs ∈ lts.pairViaLang via s t ↔
      ∃ r ∈ via, ∃ xs1 xs2, lts.MTr s xs1 r ∧ lts.MTr r xs2 t ∧ xs1 ++ xs2 = xs := by
  simp [LTS.pairViaLang, Language.mem_mul]

/-- `LTS.pairViaLang via s t` is a regular language if there are only finitely many states. -/
@[simp]
theorem LTS.pairViaLang_regular [Inhabited Symbol] [Finite State] {lts : LTS State Symbol}
    {via : Set State} {s t : State} : (lts.pairViaLang via s t).IsRegular := by
  apply IsRegular.iSup
  grind [Language.IsRegular.mul, LTS.pairLang_regular]

theorem LTS.pairLang_append {lts : LTS State Symbol} {s0 s1 s2 : State} {xs1 xs2 : List Symbol}
    (h1 : xs1 ∈ lts.pairLang s0 s1) (h2 : xs2 ∈ lts.pairLang s1 s2) :
    xs1 ++ xs2 ∈ lts.pairLang s0 s2 := by
  grind [<= LTS.MTr.comp]

theorem LTS.pairLang_split {lts : LTS State Symbol} {s0 s2 : State} {xs1 xs2 : List Symbol}
    (h : xs1 ++ xs2 ∈ lts.pairLang s0 s2) :
    ∃ s1, xs1 ∈ lts.pairLang s0 s1 ∧ xs2 ∈ lts.pairLang s1 s2 := by
  obtain ⟨r, _, _⟩ := LTS.MTr.split <| LTS.mem_pairLang.mp h
  use r
  grind

theorem LTS.pairViaLang_append_pairLang {lts : LTS State Symbol}
    {s0 s1 s2 : State} {xs1 xs2 : List Symbol} {via : Set State}
    (h1 : xs1 ∈ lts.pairViaLang via s0 s1) (h2 : xs2 ∈ lts.pairLang s1 s2) :
    xs1 ++ xs2 ∈ lts.pairViaLang via s0 s2 := by
  obtain ⟨r, _, _, _, _, _, rfl⟩ := LTS.mem_pairViaLang.mp h1
  apply LTS.mem_pairViaLang.mpr
  use r
  grind [<= LTS.MTr.comp]

theorem LTS.pairLang_append_pairViaLang {lts : LTS State Symbol}
    {s0 s1 s2 : State} {xs1 xs2 : List Symbol} {via : Set State}
    (h1 : xs1 ∈ lts.pairLang s0 s1) (h2 : xs2 ∈ lts.pairViaLang via s1 s2) :
    xs1 ++ xs2 ∈ lts.pairViaLang via s0 s2 := by
  obtain ⟨r, _, _, _, _, _, rfl⟩ := LTS.mem_pairViaLang.mp h2
  apply LTS.mem_pairViaLang.mpr
  use r
  grind [<= LTS.MTr.comp]

theorem LTS.pairViaLang_split {lts : LTS State Symbol} {s0 s2 : State} {xs1 xs2 : List Symbol}
    {via : Set State} (h : xs1 ++ xs2 ∈ lts.pairViaLang via s0 s2) :
    ∃ s1, xs1 ∈ lts.pairViaLang via s0 s1 ∧ xs2 ∈ lts.pairLang s1 s2 ∨
          xs1 ∈ lts.pairLang s0 s1 ∧ xs2 ∈ lts.pairViaLang via s1 s2 := by
  obtain ⟨r, h_r, ys1, ys2, h_ys1, h_ys2, h_eq⟩ := LTS.mem_pairViaLang.mp h
  obtain ⟨zs1, rfl, rfl⟩ | ⟨zs2, rfl, rfl⟩ := List.append_eq_append_iff.mp h_eq
  · obtain ⟨s1, _, _⟩ := LTS.MTr.split h_ys2
    use s1
    grind
  · obtain ⟨s1, _, _⟩ := LTS.MTr.split h_ys1
    use s1
    grind

namespace Automata.NA.Buchi

open Set Filter ωSequence ωLanguage ωAcceptor

/-- The ω-language accepted by a finite-state Büchi automaton is the finite union of ω-languages
of the form `L * M^ω`, where all `L`s and `M`s are regular languages. -/
theorem language_eq_fin_iSup_hmul_omegaPow
    [Inhabited Symbol] [Finite State] (na : Buchi State Symbol) :
    language na = ⨆ s ∈ na.start, ⨆ t ∈ na.accept, (na.pairLang s t) * (na.pairLang t t)^ω := by
  ext xs
  simp only [ωAcceptor.mem_language, ωLanguage.mem_iSup, ωLanguage.mem_hmul, LTS.mem_pairLang]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨t, h_acc, h_t⟩ := frequently_in_finite_type.mp h_inf
    use ss 0, by grind [NA.Run], t, h_acc
    obtain ⟨f, h_mono, h_f⟩ := frequently_iff_strictMono.mp h_t
    refine ⟨xs.take (f 0), ?_, xs.drop (f 0), ?_, by grind⟩
    · have : na.MTr (ss 0) (xs.extract 0 (f 0)) (ss (f 0)) := by grind [LTS.ωTr_mTr, NA.Run]
      grind [extract_eq_drop_take]
    · simp only [omegaPow_seq_prop, LTS.mem_pairLang]
      use (f · - f 0)
      split_ands
      · grind [Nat.base_zero_strictMono]
      · simp
      · intro n
        have mono_f (k : ℕ) : f 0 ≤ f (n + k) := h_mono.monotone (by grind)
        grind [extract_drop, mono_f 0, LTS.ωTr_mTr h_run.trans <| h_mono.monotone (?_ : n ≤ n + 1)]
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
    use xss, by grind [NA.Run]
    apply (drop_frequently_iff_frequently yl.length).mp
    apply frequently_iff_strictMono.mpr
    use zls.cumLen
    grind [cumLen_strictMono]

end Automata.NA.Buchi

end Cslib
