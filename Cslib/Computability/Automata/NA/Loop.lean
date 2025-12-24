/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.NA.Basic
import Cslib.Foundations.Data.OmegaSequence.Temporal

/-! # Loop construction on nondeterministic automata. -/

namespace Cslib.Automata.NA

open Nat List Sum ωSequence Acceptor Language
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
    use s, t
    grind
  case succ m h_ind =>
    obtain ⟨s, t, h_mtr, _⟩ := h_ind (by grind) (by grind)
    obtain ⟨t', _⟩ := isRight_iff.mp <|h2 (m + 1 + 1) (by grind) (by grind)
    have h_tr : na.Tr t (xs (m + 1)) t' := by grind [FinAcc.loop, h.trans (m + 1)]
    use s, t'
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
theorem loop_run_one_iter {xs : ωSequence Symbol} {ss : ωSequence (Unit ⊕ State)}
    (h : na.loop.Run xs ss) (h1 : ∃ k, 0 < k ∧ (ss k).isLeft) :
    ∃ n, xs.take n ∈ language na - 1 ∧ na.loop.Run (xs.drop n) (ss.drop n) := by
  let n := Nat.find h1
  have : 0 < n ∧ (ss n).isLeft := Nat.find_spec h1
  have : ∀ k, 0 < k → k < n → (ss k).isRight := by grind [Nat.find_min h1]
  refine ⟨n, ⟨?_, ?_⟩, ?_⟩
  · grind [loop_run_left_right_left]
  · have neq : (ωSequence.take n xs).length ≠ 0 := by grind
    exact neq.imp (congrArg length)
  · grind [loop_run_from_left]

/-- For any finite word in `language na`, there is a corresponding finite run of `na.loop`. -/
theorem loop_fin_run_exists {xl : List Symbol} (h : xl ∈ language na) :
    ∃ sl : List (Unit ⊕ State), ∃ _ : sl.length = xl.length + 1,
    sl[0] = inl () ∧ sl[xl.length] = inl () ∧
    ∀ k, ∀ _ : k < xl.length, na.loop.Tr sl[k] xl[k] sl[k + 1] := by
  obtain ⟨_, _, _, _, h_mtr⟩ := h
  obtain ⟨sl, _, _, _, _⟩ := LTS.MTr.exists_states h_mtr
  by_cases xl.length = 0
  · use [inl ()]
    grind
  · use [inl ()] ++ (sl.extract 1 xl.length).map inr ++ [inl ()]
    grind [FinAcc.loop]

/-- For any infinite sequence `xls` of nonempty finite words from `language na`,
there is an infinite run of `na.loop` corresponding to `xls.flatten` in which
the state `()` marks the boundaries between the finite words in `xls`. -/
theorem loop_run_exists [Inhabited Symbol] {xls : ωSequence (List Symbol)}
    (h : ∀ k, (xls k) ∈ language na - 1) :
    ∃ ss, na.loop.Run xls.flatten ss ∧ ∀ k, ss (xls.cumLen k) = inl () := by
  have : Inhabited State := by
    choose s0 _ using (h 0).left
    exact { default := s0 }
  choose sls h_sls using fun k ↦ loop_fin_run_exists <| (h k).left
  let segs := ωSequence.mk fun k ↦ (sls k).take (xls k).length
  have h_len : xls.cumLen = segs.cumLen := by ext k; induction k <;> grind
  have h_pos (k : ℕ) : (segs k).length > 0 := by grind [eq_nil_iff_length_eq_zero]
  have h_mono := cumLen_strictMono h_pos
  have h_zero := cumLen_zero (ls := segs)
  have h_seg0 (k : ℕ) : (segs k)[0]! = inl () := by grind
  refine ⟨segs.flatten, Run.mk ?_ ?_, ?_⟩
  · simp [h_seg0, flatten_def, FinAcc.loop]
  · intro n
    simp only [h_len, flatten_def]
    have := segment_lower_bound h_mono h_zero n
    by_cases h_n : n + 1 < segs.cumLen (segment segs.cumLen n + 1)
    · grind [segment_range_val h_mono (by grind) h_n]
    · have h1 : segs.cumLen (segment segs.cumLen n + 1) = n + 1 := by
        grind [segment_upper_bound h_mono h_zero n]
      have h2 : segment segs.cumLen (n + 1) = segment segs.cumLen n + 1 := by
        simp [← h1, segment_idem h_mono]
      simp [h1, h2, h_seg0]
      grind
  · simp [h_len, flatten_def, segment_idem h_mono, h_seg0]

namespace Buchi

open Filter ωAcceptor ωLanguage

/-- The Buchi ω-language accepted by `na.loop` is the ω-power of the language accepted by `na`. -/
@[simp]
theorem loop_language_eq [Inhabited Symbol] :
    language (Buchi.mk na.loop {inl ()}) = (language na)^ω := by
  apply le_antisymm
  · apply omegaPow_coind
    rintro xs ⟨ss, h_run, h_acc⟩
    have h1 : ∃ k > 0, (ss k).isLeft := by grind [FinAcc.loop, frequently_atTop'.mp h_acc 0]
    obtain ⟨n, _⟩ := loop_run_one_iter h_run h1
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
    grind [cumLen_strictMono, eq_nil_iff_length_eq_zero]

end Buchi

end Cslib.Automata.NA
