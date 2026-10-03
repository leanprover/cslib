/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Flatten
public import Cslib.Foundations.Semantics.LTS.Execution

/-!
# Infinite executions of LTS
-/

@[expose] public section

namespace Cslib.LTS

open ωSequence

/-- An infinite execution is conceptually an infinite sequence of transitions. But it is
technically more convenient to separate the states and the labels into two ω-sequences. -/
@[scoped grind]
def OmegaExecution (lts : LTS State Label)
    (ss : ωSequence State) (μs : ωSequence Label) : Prop :=
  ∀ i, lts.Tr (ss i) (μs i) (ss (i + 1))

variable {State Label : Type*} {lts : LTS State Label}

/-- Any finite execution extracted from an infinite execution is valid. -/
theorem OmegaExecution.extract_execution
    (h : lts.OmegaExecution ss μs) {n m : ℕ} (hnm : n ≤ m) :
    lts.Execution (ss n) (μs.extract n m) (ss m) (ss.extract n (m + 1)) := by
  grind

/-- Any multistep transition extracted from an infinite execution is valid. -/
theorem OmegaExecution.extract_mTr
    (h : lts.OmegaExecution ss μs) {n m : ℕ} (hnm : n ≤ m) :
    lts.MTr (ss n) (μs.extract n m) (ss m) := by
  grind [OmegaExecution.extract_execution h hnm]

/-- Prepends an infinite execution with a transition. -/
theorem OmegaExecution.cons (htr : lts.Tr s μ t)
    (hωtr : lts.OmegaExecution ss μs) (hm : ss 0 = t) :
    lts.OmegaExecution (s ::ω ss) (μ ::ω μs) := by
  intro i
  induction i <;> grind

theorem OmegaExecution.prepend_execution (he_head : lts.Execution s μl t sl)
    (he_tail : lts.OmegaExecution ss μs) (hm : ss 0 = t) :
    lts.OmegaExecution (sl ++ω ss.tail) (μl ++ω μs) := by
  intro n
  obtain (hn | rfl | hn) := n.lt_trichotomy μl.length
  · grind [get_append_left]
  · convert he_tail 0 using 1
    · rw [hm, ← he_head.last', get_append_left]
    · exact get_append_right 0 μl μs
    · have := get_append_right 0 sl ss.tail
      simpa [he_head.length]
  · obtain ⟨n, rfl⟩ : ∃ n', n = sl.length + n' := by
      have ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hn
      exact ⟨k, by grind [he_head.length]⟩
    simp_rw [add_assoc, get_append_right, he_head.length, add_assoc,
      get_append_right, add_comm, ωSequence.tail, get_fun,]
    exact he_tail (n + 1)

/-- Prepends an infinite execution with a finite execution. -/
theorem OmegaExecution.append
    (hmtr : lts.MTr s μl t) (hωtr : lts.OmegaExecution ss μs) (hm : ss 0 = t) :
    ∃ ss', lts.OmegaExecution ss' (μl ++ω μs) ∧
      ss' 0 = s ∧ ss' μl.length = t ∧ ss'.drop μl.length = ss := by
  obtain ⟨sl, he⟩ := Execution.of_mTr hmtr
  refine ⟨sl ++ω ss.tail, hωtr.prepend_execution he hm, ?_, ?_, ?_⟩
  · rw [get_append_left _ _ _ he.length_ss_pos, he.start]
  · rw [← he.last', get_append_left]
  · rw [← ss.eta, drop_append_of_le_length _ _ _ (by grind), tail_cons,
      ← singleton_append_ωSequence]
    congr
    rw [head, hm, ← sl.take_append_getLast he.ss_ne_nil, sl.take_append_getLast,
      he.length', sl.drop_length_sub_one he.ss_ne_nil, he.getLast]

open Nat in
/-- Concatenating an infinite sequence of finite executions, with an explicit expression for the
state sequence. -/
theorem OmegaExecution.flatten_execution' [Inhabited Label] [Inhabited State]
    {ts : ωSequence State} {μls : ωSequence (List Label)} {sls : ωSequence (List State)}
    (hexec : ∀ k, lts.Execution (ts k) (μls k) (ts (k + 1)) (sls k))
    (hpos : ∀ k, 0 < (μls k).length) :
    lts.OmegaExecution (sls.map List.dropLast).flatten μls.flatten := by
  intro n
  obtain ⟨n, k, hk, rfl⟩ : ∃ n' k, k < (μls n').length ∧ n = μls.cumLen n' + k := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le <|
      segment_lower_bound (cumLen_strictMono hpos) cumLen_zero n
    refine ⟨segment μls.cumLen n, k, ?_, hk⟩
    have := segment_upper_bound (cumLen_strictMono hpos) cumLen_zero n
    simp [cumLen_succ] at this
    grind
  have hlen (k : ℕ) : (μls k).length = (sls.map List.dropLast k).length := by grind
  have hclen : μls.cumLen = (sls.map List.dropLast).cumLen := by ext k; induction k <;> grind
  have hspos (k : ℕ) : 0 < (sls.map List.dropLast k).length := hlen k ▸ hpos k
  convert (hexec n).trans k hk
  · rw [hlen] at hk
    simp [hclen, flatten_get_add _ hk hspos]
  · exact flatten_get_add _ hk hpos
  · obtain (hk | hk) : k + 1 < (μls n).length ∨ k + 1 = (μls n).length := by lia
    · rw [hlen] at hk
      simp [hclen, add_assoc, flatten_get_add _ hk hspos]
    · rw! [add_assoc, hk, ← cumLen_succ, (hexec n).last', hclen, flatten_get_cumLen _ hspos]
      simp [(hexec (n + 1)).start]

open Nat in
/-- Concatenating an infinite sequence of finite executions. -/
theorem OmegaExecution.flatten_execution [Inhabited Label]
    {ts : ωSequence State} {μls : ωSequence (List Label)} {sls : ωSequence (List State)}
    (hexec : ∀ k, lts.Execution (ts k) (μls k) (ts (k + 1)) (sls k))
    (hpos : ∀ k, 0 < (μls k).length) :
    ∃ ss, lts.OmegaExecution ss μls.flatten ∧
      ∀ k, ss.extract (μls.cumLen k) (μls.cumLen (k + 1)) = (sls k).take (μls k).length := by
  have : Inhabited State := {default := ts 0}
  use (sls.map List.dropLast).flatten, .flatten_execution' hexec hpos
  intro k
  have hlen : μls.cumLen = (sls.map List.dropLast).cumLen := by ext k; induction k <;> grind
  rw [hlen, extract_flatten, get_map, (sls k).dropLast_eq_take, ← (hexec k).length']
  grind

/-- Concatenating an infinite sequence of multistep transitions. -/
theorem OmegaExecution.flatten_mTr [Inhabited Label]
    {ts : ωSequence State} {μls : ωSequence (List Label)}
    (hmtr : ∀ k, lts.MTr (ts k) (μls k) (ts (k + 1))) (hpos : ∀ k, 0 < (μls k).length) :
    ∃ ss, lts.OmegaExecution ss μls.flatten ∧ ∀ k, ss (μls.cumLen k) = ts k := by
  choose sls h_sls using fun k ↦ Execution.of_mTr (hmtr k)
  obtain ⟨ss, h_ss, h_seg⟩ := OmegaExecution.flatten_execution h_sls hpos
  use ss, h_ss
  intro k
  have : ss.extract (μls.cumLen k) (μls.cumLen (k + 1)) ≠ [] := by grind
  have h1 : 0 < (ss.extract (μls.cumLen k) (μls.cumLen (k + 1))).length :=
    List.length_pos_iff.mpr this
  grind [List.getElem_of_eq (h_seg k) h1]

end Cslib.LTS
