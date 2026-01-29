/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Total
public import Cslib.Foundations.Data.OmegaSequence.Temporal

@[expose] public section

/-! # Loop construction on nondeterministic automata. -/

namespace Cslib.Automata.NA

open Nat Set Sum ωSequence Acceptor Language
open scoped Run LTS

variable {Symbol State : Type*}

/-- `na.loop` mimics `na`, but can nondeterministically decide to "loop back" by identifing
an accepting state of `na` with a starting state of `na`.  This identification is achieved
via a new dummy state `()`, which is the sole starting state and the sole accepting state
of `na.loop`. -/
def FinAcc.loop (na : FinAcc State Symbol) : NA (Unit ⊕ State) Symbol where
    Tr s' x t' := match s', t' with
      | inl (), inl () => ∃ s t, na.Tr s x t ∧ s ∈ na.start ∧ t ∈ na.accept
      | inl (), inr t => ∃ s, na.Tr s x t ∧ s ∈ na.start
      | inr s, inl () => ∃ t, na.Tr s x t ∧ t ∈ na.accept
      | inr s, inr t => na.Tr s x t
    start := {inl ()}

variable {na : FinAcc State Symbol}

lemma loop_run_left_left {xs : ωSequence Symbol} {ss : ωSequence (Unit ⊕ State)}
    (h : na.loop.Run xs ss) (h1 : (ss 1).isLeft) : [xs 0] ∈ language na := by
  have h_init := h.start
  simp only [FinAcc.loop, Set.mem_singleton_iff] at h_init
  have h_step := h.trans 0
  obtain ⟨t, h_t⟩ := isLeft_iff.mp h1
  simp only [FinAcc.loop, h_init, h_t] at h_step
  obtain ⟨s, t, _⟩ := h_step
  refine ⟨s, ?_, t, ?_⟩ <;> grind

lemma loop_run_left_right {xs : ωSequence Symbol} {ss : ωSequence (Unit ⊕ State)}
    (h : na.loop.Run xs ss) (n : ℕ) (h1 : 0 < n) (h2 : ∀ k, 0 < k → k ≤ n → (ss k).isRight) :
    ∃ s t, na.MTr s (xs.take n) t ∧ s ∈ na.start ∧ ss n = inr t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.mpr h1
  induction m
  case zero =>
    obtain ⟨t, _⟩ := isRight_iff.mp <| h2 1 (by grind) (by grind)
    obtain ⟨s, _⟩ : ∃ s, na.Tr s (xs 0) t ∧ s ∈ na.start := by
      grind [FinAcc.loop, h.start, h.trans 0]
    grind
  case succ m h_ind =>
    obtain ⟨s, t, h_mtr, _⟩ := h_ind (by grind) (by grind)
    obtain ⟨t', _⟩ := isRight_iff.mp <|h2 (m + 1 + 1) (by grind) (by grind)
    have h_tr : na.Tr t (xs (m + 1)) t' := by grind [FinAcc.loop, h.trans (m + 1)]
    grind [LTS.MTr.stepR na.toLTS h_mtr h_tr]

lemma loop_run_left_right_left {xs : ωSequence Symbol} {ss : ωSequence (Unit ⊕ State)}
    (h : na.loop.Run xs ss) (n : ℕ) (h1 : 0 < n ∧ (ss n).isLeft)
    (h2 : ∀ k, 0 < k → k < n → (ss k).isRight) : xs.take n ∈ language na := by
  by_cases n = 1
  · grind [loop_run_left_left]
  · obtain ⟨s, t, h_mtr, _⟩ := loop_run_left_right h (n - 1) (by grind) (by grind)
    obtain ⟨t', h_tr, _⟩ : ∃ t', na.Tr t (xs (n - 1)) t' ∧ t' ∈ na.accept := by
      grind [FinAcc.loop, h.trans (n - 1)]
    refine ⟨s, ?_, t', ?_⟩ <;> grind [LTS.MTr.stepR na.toLTS h_mtr h_tr]

lemma loop_run_from_left {xs : ωSequence Symbol} {ss : ωSequence (Unit ⊕ State)}
    (h : na.loop.Run xs ss) (n : ℕ) (h1 : (ss n).isLeft) :
    na.loop.Run (xs.drop n) (ss.drop n) := by
  apply Run.mk
  · grind [FinAcc.loop, isLeft_iff.mp h1]
  · grind [FinAcc.loop, h.trans]

/-- A run of `na.loop` containing at least one non-initial `()` state is the concatenation
of a nonempty finite run of `na` followed by a run of `na.loop`. -/
theorem loop_run_one_iter {xs : ωSequence Symbol} {ss : ωSequence (Unit ⊕ State)} {k : ℕ}
    (h : na.loop.Run xs ss) (h1 : 0 < k) (h2 : (ss k).isLeft) :
    ∃ n, n ≤ k ∧ xs.take n ∈ language na - 1 ∧ na.loop.Run (xs.drop n) (ss.drop n) := by
  have h1' : ∃ k, 0 < k ∧ (ss k).isLeft := by grind
  let n := Nat.find h1'
  have : 0 < n ∧ (ss n).isLeft := Nat.find_spec h1'
  have : ∀ k, 0 < k → k < n → (ss k).isRight := by grind [Nat.find_min h1']
  refine ⟨n, by grind, ⟨?_, ?_⟩, ?_⟩
  · grind [loop_run_left_right_left]
  · have neq : (ωSequence.take n xs).length ≠ 0 := by grind
    exact neq.imp (congrArg List.length)
  · grind [loop_run_from_left]

/-- For any finite word in `language na`, there is a corresponding finite run of `na.loop`. -/
theorem loop_fin_run_exists {xl : List Symbol} (h : xl ∈ language na) :
    ∃ sl : List (Unit ⊕ State), ∃ _ : sl.length = xl.length + 1,
    sl[0] = inl () ∧ sl[xl.length] = inl () ∧
    ∀ k, (_ : k < xl.length) → na.loop.Tr sl[k] xl[k] sl[k + 1] := by
  obtain ⟨_, _, _, _, h_mtr⟩ := h
  obtain ⟨sl, _, _, _, _⟩ := LTS.mTr_isExecution h_mtr
  by_cases xl.length = 0
  · use [inl ()]
    grind
  · use [inl ()] ++ (sl.extract 1 xl.length).map inr ++ [inl ()]
    grind [FinAcc.loop, → LTS.tr_setImage]

/-- For any finite word in `language na`, there is a corresponding multistep transition
of `na.loop`. -/
theorem loop_fin_run_mtr {xl : List Symbol} (h : xl ∈ language na) :
    na.loop.MTr (inl ()) xl (inl ()) := by
  obtain ⟨sl, _, _, _, h_run⟩ := loop_fin_run_exists h
  suffices ∀ k, (_ : k ≤ xl.length) → na.loop.MTr (inl ()) (xl.take k) sl[k] by grind
  intro k
  induction k <;> grind [LTS.MTr.stepR, List.take_add_one]

/-- For any infinite sequence `xls` of nonempty finite words from `language na`,
there is an infinite run of `na.loop` corresponding to `xls.flatten` in which
the state `()` marks the boundaries between the finite words in `xls`. -/
theorem loop_run_exists [Inhabited Symbol] {xls : ωSequence (List Symbol)}
    (h : ∀ k, (xls k) ∈ language na - 1) :
    ∃ ss, na.loop.Run xls.flatten ss ∧ ∀ k, ss (xls.cumLen k) = inl () := by
  let ts := ωSequence.const (inl () : Unit ⊕ State)
  have h_mtr (k : ℕ) : na.loop.MTr (ts k) (xls k) (ts (k + 1)) := by grind [loop_fin_run_mtr]
  have h_pos (k : ℕ) : (xls k).length > 0 := by grind
  obtain ⟨ss, _, _⟩ := LTS.ωTr.flatten h_mtr h_pos
  use ss
  grind [Run.mk, FinAcc.loop, cumLen_zero (ls := xls)]

namespace Buchi

open Filter ωAcceptor ωLanguage

/-- The Buchi ω-language accepted by `na.loop` is the ω-power of the language accepted by `na`. -/
@[simp]
theorem loop_language_eq [Inhabited Symbol] :
    language (Buchi.mk na.loop {inl ()}) = (language na)^ω := by
  apply le_antisymm
  · apply omegaPow_coind
    rintro xs ⟨ss, h_run, h_acc⟩
    obtain ⟨k, h1, h2⟩ : ∃ k > 0, (ss k).isLeft :=
      by grind [FinAcc.loop, frequently_atTop'.mp h_acc 0]
    obtain ⟨n, _⟩ := loop_run_one_iter h_run h1 h2
    refine ⟨xs.take n, by grind, xs.drop n, ?_, by simp⟩
    refine ⟨ss.drop n, by grind, ?_⟩
    apply (drop_frequently_iff_frequently n).mpr
    grind
  · rintro xls h_pow
    obtain ⟨xls, rfl, h_xls⟩ := mem_omegaPow.mp h_pow
    obtain ⟨ss, h_run, _⟩ := loop_run_exists h_xls
    use ss, h_run
    apply frequently_iff_strictMono.mpr
    use xls.cumLen, ?_, by grind
    grind [cumLen_strictMono, List.eq_nil_iff_length_eq_zero]

end Buchi

namespace FinAcc

open scoped Computability

/-- `finLoop na` is the loop construction applied to the "totalized" version of `na`. -/
def finLoop (na : FinAcc State Symbol) : NA (Unit ⊕ (State ⊕ Unit)) Symbol :=
  FinAcc.loop ⟨na.totalize, inl '' na.accept⟩

/-- `finLoop na` is total, assuming that `na` has at least one start state. -/
instance [h : Nonempty na.start] : na.finLoop.Total where
  total s x := match s with
    | inl _ => ⟨inr (inr ()), by simpa [finLoop, loop, NA.totalize, LTS.totalize] using h⟩
    | inr _ => ⟨inr (inr ()), by grind [finLoop, loop, NA.totalize, LTS.totalize]⟩

/-- `finLoop na` accepts the Kleene star of the language of `na`, assuming that
the latter is nonempty. -/
theorem loop_language_eq [Inhabited Symbol] (h : ¬ language na = 0) :
    language (FinAcc.mk na.finLoop {inl ()}) = (language na)∗ := by
  rw [Language.kstar_iff_mul_add]
  ext xl; constructor
  · rintro ⟨s, _, t, h_acc, h_mtr⟩
    by_cases h_xl : xl = []
    · grind [mem_add, mem_one]
    · have : Nonempty na.start := by
        obtain ⟨_, s0, _, _⟩ := nonempty_iff_ne_empty.mpr h
        use s0
      obtain ⟨xs, ss, h_ωtr, rfl, rfl⟩ := LTS.Total.mTr_ωTr h_mtr
      have h_run : na.finLoop.Run (xl ++ω xs) ss := by grind [Run]
      obtain ⟨h1, h2⟩ : 0 < xl.length ∧ (ss xl.length).isLeft := by
        simp only [mem_singleton_iff] at h_acc
        grind
      obtain ⟨n, h_n, _, _, h_ωtr'⟩ := loop_run_one_iter h_run h1 h2
      left; refine ⟨xl.take n, ?_, xl.drop n, ?_, ?_⟩
      · grind [totalize_language_eq, take_append_of_le_length]
      · refine ⟨ss n, by grind, ss xl.length, by grind, ?_⟩
        have := LTS.ωTr_mTr h_ωtr' (show 0 ≤ xl.length - n by grind)
        have : n + (xl.length - n) = xl.length := by grind
        have : ((xl ++ω xs).drop n).extract 0 (xl.length - n) = xl.drop n := by
          grind [extract_eq_take, drop_append_of_le_length, take_append_of_le_length]
        grind [finLoop]
      · exact xl.take_append_drop n
  · rintro (h | h)
    · obtain ⟨xl1, ⟨h_xl1, _⟩, xl2, h_xl2, rfl⟩ := h
      rw [← totalize_language_eq] at h_xl1
      have := loop_fin_run_mtr h_xl1
      obtain ⟨s1, _, s2, _, _⟩ := h_xl2
      obtain ⟨rfl⟩ : s1 = inl () := by grind [finLoop, loop]
      obtain ⟨rfl⟩ : s2 = inl () := by grind [finLoop, loop]
      refine ⟨inl (), ?_, inl (), ?_, LTS.MTr.comp _ this ?_⟩ <;> assumption
    · obtain ⟨rfl⟩ := (Language.mem_one xl).mp h
      refine ⟨inl (), ?_, inl (), ?_, ?_⟩ <;> grind [finLoop, loop]

end FinAcc

end Cslib.Automata.NA
