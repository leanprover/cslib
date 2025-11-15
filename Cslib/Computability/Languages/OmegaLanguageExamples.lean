/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DA
import Cslib.Computability.Automata.NA
import Cslib.Foundations.Data.OmegaSequence.InfOcc
import Mathlib.Tactic

/-!
# ω-Regular languages

This file defines ω-regular languages and proves some properties of them.
-/

open Set Function Filter Cslib.ωSequence Cslib.Automata ωAcceptor
open scoped Computability

namespace Cslib.ωLanguage.Example

section EventuallyZero

/-- A sequence `xs` is in `eventually_zero` iff `xs k = 0` for all large `k`. -/
@[scoped grind =]
def eventually_zero : ωLanguage (Fin 2) :=
  { xs : ωSequence (Fin 2) | ∀ᶠ k in atTop, xs k = 0 }

/-- `eventually_zero` is accepted by a 2-state nondeterministic Buchi automaton. -/
theorem eventually_zero_accepted_by_na_buchi :
    ∃ a : NA.Buchi (Fin 2) (Fin 2), language a = eventually_zero := by
  let a : NA.Buchi (Fin 2) (Fin 2) := {
    -- Once state 1 is reached, only symbol 0 is accepted and the next state is still 1
    Tr s x s' := s = 1 → x = 0 ∧ s' = 1
    start := {0}
    accept := {1} }
  use a ; ext xs ; constructor
  · rintro ⟨ss, h_run, h_acc⟩
    obtain ⟨m, h_m⟩ := Frequently.exists h_acc
    apply eventually_atTop.mpr
    use m ; intro n h_n
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h_n
    suffices h1 : xs (m + k) = 0 ∧ ss (m + k) = 1 by grind
    induction k
    case zero =>
      have := h_run.2 m
      grind
    case succ k h_ind =>
      have := h_run.2 (m + k)
      have := h_run.2 (m + k + 1)
      grind
  · intro h
    obtain ⟨m, h_m⟩ := eventually_atTop.mp h
    let ss : ωSequence (Fin 2) := fun k ↦ if k ≤ m then (0 : Fin 2) else 1
    refine ⟨ss, ?_, ?_⟩
    · simp [a, ss, NA.Run]
      grind
    · apply Eventually.frequently
      apply eventually_atTop.mpr
      use (m + 1) ; intro k _
      simp [a, ss, show m < k by omega]

private lemma extend_by_zero (u : List (Fin 2)) :
    u ++ω const 0 ∈ eventually_zero := by
  apply eventually_atTop.mpr
  use u.length
  intro k h_k
  rw [get_append_right' h_k]
  simp

private lemma extend_by_one (u : List (Fin 2)) :
    ∃ v, 1 ∈ v ∧ u ++ v ++ω const 0 ∈ eventually_zero := by
  refine ⟨[1], ?_, ?_⟩
  · simp
  · apply extend_by_zero

private lemma extend_by_hyp {l : Language (Fin 2)} (h : l↗ω = eventually_zero)
    (u : List (Fin 2)) : ∃ v, 1 ∈ v ∧ u ++ v ∈ l := by
  obtain ⟨v, _, h_pfx⟩ := extend_by_one u
  rw [← h] at h_pfx
  obtain ⟨m, h_m, h_uv⟩ := frequently_atTop.mp h_pfx (u ++ v).length
  use (v ++ω ωSequence.const 0).extract 0 (m - u.length)
  rw [extract_append_zero_right (show v.length ≤ m - u.length by grind)]
  constructor
  · simp_all
  · rw [extract_append_zero_right h_m] at h_uv
    grind

private noncomputable def oneSegs {l : Language (Fin 2)} (h : l↗ω = eventually_zero) (n : ℕ) :=
  Classical.choose <| extend_by_hyp h (List.ofFn (fun k : Fin n ↦ oneSegs h k)).flatten

private lemma oneSegs_lemma {l : Language (Fin 2)} (h : l↗ω = eventually_zero) (n : ℕ) :
    1 ∈ oneSegs h n ∧ (List.ofFn (fun k : Fin (n + 1) ↦ oneSegs h k)).flatten ∈ l := by
  let P u v := 1 ∈ v ∧ u ++ v ∈ l
  have : P ((List.ofFn (fun k : Fin n ↦ oneSegs h k)).flatten) (oneSegs h n) := by
    unfold oneSegs
    exact Classical.choose_spec <| extend_by_hyp h (List.ofFn (fun k : Fin n ↦ oneSegs h k)).flatten
  obtain ⟨h1, h2⟩ := this
  refine ⟨h1, ?_⟩
  rw [List.ofFn_succ_last]
  simpa

theorem eventually_zero_not_omegaLim :
    ¬ ∃ l : Language (Fin 2), l↗ω = eventually_zero := by
  rintro ⟨l, h⟩
  let ls := ωSequence.mk (oneSegs h)
  have h_segs := oneSegs_lemma h
  have h_pos : ∀ k, (ls k).length > 0 := by grind
  have h_ev : ls.flatten ∈ eventually_zero := by
    rw [← h, mem_omegaLim, frequently_iff_strictMono]
    use (fun k ↦ ls.cumLen (k + 1))
    constructor
    · intro j k h_jk
      have := cumLen_strictMono h_pos (show j + 1 < k + 1 by omega)
      grind
    · intro n
      rw [extract_eq_take, ← flatten_take h_pos]
      suffices _ : ls.take (n + 1) = List.ofFn (fun k : Fin (n + 1) ↦ oneSegs h k) by grind
      simp [← extract_eq_take, extract_eq_ofFn, ls]
  obtain ⟨m, _⟩ := eventually_atTop.mp h_ev
  have h_inf : ∃ᶠ n in atTop, n ∈ range ls.cumLen := by
    apply frequently_iff_strictMono.mpr
    have := cumLen_strictMono h_pos
    grind
  obtain ⟨n, h_n, k, rfl⟩ := frequently_atTop.mp h_inf m
  have h_k : 1 ∈ ls k := by grind
  simp only [← extract_flatten h_pos k, List.mem_iff_getElem, length_extract] at h_k
  grind

end EventuallyZero

end Cslib.ωLanguage.Example
