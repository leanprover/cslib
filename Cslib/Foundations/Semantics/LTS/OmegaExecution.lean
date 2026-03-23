/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Flatten
public import Cslib.Foundations.Semantics.LTS.Execution

@[expose] public section

/-!
# Infinite executions of LTS
-/

namespace Cslib

open ωSequence

/-- An infinite execution is conceptually an infinite sequence of transitions. But it is
technically more convenient to separate the states and the labels into two ω-sequences. -/
@[scoped grind]
def LTS.OmegaExecution (lts : LTS State Label)
    (ss : ωSequence State) (μs : ωSequence Label) : Prop :=
  ∀ i, lts.Tr (ss i) (μs i) (ss (i + 1))

variable {State Label : Type*} {lts : LTS State Label}

/-- Any finite execution extracted from an infinite execution is valid. -/
theorem LTS.OmegaExecution.extract_execution
    (h : lts.OmegaExecution ss μs) {n m : ℕ} (hnm : n ≤ m) :
    lts.Execution (ss n) (μs.extract n m) (ss m) (ss.extract n (m + 1)) := by
  grind

/-- Any multistep transition extracted from an infinite execution is valid. -/
theorem LTS.OmegaExecution.extract_mTr
    (h : lts.OmegaExecution ss μs) {n m : ℕ} (hnm : n ≤ m) :
    lts.MTr (ss n) (μs.extract n m) (ss m) := by
  grind [LTS.OmegaExecution.extract_execution h hnm]

/-- Prepends an infinite execution with a transition. -/
theorem LTS.OmegaExecution.cons (htr : lts.Tr s μ t)
    (hωtr : lts.OmegaExecution ss μs) (hm : ss 0 = t) :
    lts.OmegaExecution (s ::ω ss) (μ ::ω μs) := by
  intro i
  induction i <;> grind

/-- Prepends an infinite execution with a finite execution. -/
theorem LTS.OmegaExecution.append
    (hmtr : lts.MTr s μl t) (hωtr : lts.OmegaExecution ss μs) (hm : ss 0 = t) :
    ∃ ss', lts.OmegaExecution ss' (μl ++ω μs) ∧
      ss' 0 = s ∧ ss' μl.length = t ∧ ss'.drop μl.length = ss := by
  obtain ⟨sl, _, _, _, _⟩ := LTS.Execution.of_mTr hmtr
  use sl.take μl.length ++ω ss
  split_ands
  · intro n
    by_cases n < μl.length
    · grind [get_append_left]
    · by_cases n = μl.length
      · grind [get_append_left, get_append_right']
      · grind [get_append_right', hωtr (n - μl.length - 1)]
  · grind [get_append_left]
  · grind [get_append_left]
  · grind [drop_append_of_ge_length]

open Nat in
/-- Concatenating an infinite sequence of finite executions. -/
theorem LTS.OmegaExecution.flatten_execution [Inhabited Label]
    {ts : ωSequence State} {μls : ωSequence (List Label)} {sls : ωSequence (List State)}
    (hexec : ∀ k, lts.Execution (ts k) (μls k) (ts (k + 1)) (sls k))
    (hpos : ∀ k, (μls k).length > 0) :
    ∃ ss, lts.OmegaExecution ss μls.flatten ∧
      ∀ k, ss.extract (μls.cumLen k) (μls.cumLen (k + 1)) = (sls k).take (μls k).length := by
  have : Inhabited State := by exact {default := ts 0}
  let segs := ωSequence.mk fun k ↦ (sls k).take (μls k).length
  have h_len : μls.cumLen = segs.cumLen := by ext k; induction k <;> grind
  have h_pos (k : ℕ) : (segs k).length > 0 := by grind [List.eq_nil_iff_length_eq_zero]
  have h_mono := cumLen_strictMono h_pos
  have h_zero := cumLen_zero (ls := segs)
  have h_seg0 (k : ℕ) : (segs k)[0]! = ts k := by grind
  use segs.flatten
  split_ands
  · intro n
    simp only [h_len, flatten_def]
    simp only [LTS.Execution] at hexec
    have := segment_lower_bound h_mono h_zero n
    by_cases h_n : n + 1 < segs.cumLen (segment segs.cumLen n + 1)
    · have := segment_range_val h_mono (by grind) h_n
      have : n + 1 - segs.cumLen (segment segs.cumLen n) < (μls (segment segs.cumLen n)).length :=
        by grind
      grind
    · have h1 : segs.cumLen (segment segs.cumLen n + 1) = n + 1 := by
        grind [segment_upper_bound h_mono h_zero n]
      have h2 : segment segs.cumLen (n + 1) = segment segs.cumLen n + 1 := by
        simp [← h1, segment_idem h_mono]
      have : n + 1 - segs.cumLen (segment segs.cumLen n) = (μls (segment segs.cumLen n)).length :=
        by grind
      have h3 : ts (segment segs.cumLen n + 1) =
          (sls (segment segs.cumLen n))[n + 1 - segs.cumLen (segment segs.cumLen n)]! := by
        grind
      simp [h1, h2, h_seg0, h3]
      grind
  · simp [h_len, extract_flatten h_pos, segs]

/-- Concatenating an infinite sequence of multistep transitions. -/
theorem LTS.OmegaExecution.flatten_mTr [Inhabited Label]
    {ts : ωSequence State} {μls : ωSequence (List Label)}
    (hmtr : ∀ k, lts.MTr (ts k) (μls k) (ts (k + 1))) (hpos : ∀ k, (μls k).length > 0) :
    ∃ ss, lts.OmegaExecution ss μls.flatten ∧ ∀ k, ss (μls.cumLen k) = ts k := by
  choose sls h_sls using fun k ↦ LTS.Execution.of_mTr (hmtr k)
  obtain ⟨ss, h_ss, h_seg⟩ := LTS.OmegaExecution.flatten_execution h_sls hpos
  use ss, h_ss
  intro k
  have h1 : 0 < (ss.extract (μls.cumLen k) (μls.cumLen (k + 1))).length := by grind
  grind [List.getElem_of_eq (h_seg k) h1]

end Cslib
