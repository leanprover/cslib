/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

open Function Set

/-!
Given a strictly monotonic function `φ : ℕ → ℕ` and `k : ℕ` with `k ≥ ϕ 0`,
`Nat.segment φ k` is the unique `m : ℕ` such that `φ m ≤ k < φ (k + 1)`.
`Nat.segment φ k` is defined to be 0 for `k < ϕ 0`.
This file defines `Nat.segment` and proves various properties aboout it.
-/

noncomputable def Nat.segment (φ : ℕ → ℕ) (k : ℕ) : ℕ :=
  open scoped Classical in
  count (· ∈ range φ) (k + 1) - 1

variable {φ : ℕ → ℕ}

theorem Nat.strict_mono_infinite (hm : StrictMono φ) :
    (range φ).Infinite := by
  exact infinite_range_of_injective hm.injective

theorem Nat.infinite_strict_mono {ns : Set ℕ} (h : ns.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ range φ = ns := by
  use nth (· ∈ ns) ; constructor
  · exact nth_strictMono h
  · exact range_nth_of_infinite h

open scoped Classical in
theorem Nat.nth_succ_gap {p : ℕ → Prop} (hf : (setOf p).Infinite) (n : ℕ) :
    ∀ k < nth p (n + 1) - nth p n, k > 0 → ¬ p (k + nth p n) := by
  intro k h_k1 h_k0 h_p_k
  let m := count p (k + nth p n)
  have h_k_ex : nth p m = k + nth p n := by simp [m, nth_count h_p_k]
  have h_n_m : n < m := by apply (nth_lt_nth hf).mp ; omega
  have h_m_n : m < n + 1 := by apply (nth_lt_nth hf).mp ; omega
  omega

theorem Nat.nth_of_strict_mono (hm : StrictMono φ) (n : ℕ) :
    φ n = nth (· ∈ range φ) n := by
  rw [← nth_comp_of_strictMono hm (by simp)]
  · simp
  intro hf ; exfalso
  have : (range φ).Infinite := strict_mono_infinite hm
  exact absurd hf this

open scoped Classical in
theorem Nat.count_notin_range_pos (h0 : φ 0 = 0) (n : ℕ) (hn : n ∉ range φ) :
    count (· ∈ range φ) n > 0 := by
  have h0' : 0 ∈ range φ := by use 0
  have h1 : n ≠ 0 := by rintro ⟨rfl⟩ ; contradiction
  have h2 : 1 ≤ n := by omega
  have h3 := count_monotone (· ∈ range φ) h2
  simp only [count_succ, count_zero, h0', ↓reduceIte, zero_add, gt_iff_lt] at h3 ⊢
  omega

theorem Nat.strict_mono_range_gap (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m < k) (hu : k < φ (m + 1)) : k ∉ range φ := by
  rw [nth_of_strict_mono hm m] at hl
  rw [nth_of_strict_mono hm (m + 1)] at hu
  have h_inf := strict_mono_infinite hm
  have h_gap := nth_succ_gap (p := (· ∈ range φ)) h_inf m
    (k - nth (· ∈ range φ) m) (by omega) (by omega)
  rw [(show k - nth (· ∈ range φ) m + nth (· ∈ range φ) m = k by omega)] at h_gap
  exact h_gap

open scoped Classical in
theorem Nat.segment_idem (hm : StrictMono φ) (k : ℕ) :
    segment φ (φ k) = k := by
  have h1 : count (· ∈ range φ) (φ k + 1) = count (· ∈ range φ) (φ k) + 1 := by
    apply count_succ_eq_succ_count ; simp
  rw [segment, h1, Nat.add_one_sub_one, nth_of_strict_mono hm]
  have h_eq := count_nth_of_infinite (p := (· ∈ range φ)) <| strict_mono_infinite hm
  rw [h_eq]

open scoped Classical in
theorem Nat.segment_pre_zero (hm : StrictMono φ) {k : ℕ} (h : k < φ 0) :
    segment φ k = 0 := by
  have h1 : count (· ∈ range φ) (k + 1) = 0 := by
    apply count_of_forall_not
    rintro n h_n ⟨i, rfl⟩
    have := StrictMono.monotone hm <| zero_le i
    omega
  rw [segment, h1]

theorem Nat.segment_zero (hm : StrictMono φ) (h0 : φ 0 = 0) :
    segment φ 0 = 0 := by
  calc _ = segment φ (φ 0) := by simp [h0]
       _ = _ := by simp [segment_idem hm]

open scoped Classical in
theorem Nat.segment_plus_one (h0 : φ 0 = 0) (k : ℕ) :
    segment φ k + 1 = count (· ∈ range φ) (k + 1) := by
  suffices _ : count (· ∈ range φ) (k + 1) ≠ 0 by unfold segment ; omega
  apply count_ne_iff_exists.mpr ; use 0 ; grind

open scoped Classical in
theorem Nat.segment_upper_bound (hm : StrictMono φ) (h0 : φ 0 = 0) (k : ℕ) :
    k < φ (segment φ k + 1) := by
  rw [nth_of_strict_mono hm (segment φ k + 1), segment_plus_one h0 k]
  suffices _ : k + 1 ≤ nth (· ∈ range φ) (count (· ∈ range φ) (k + 1)) by omega
  apply le_nth_count
  exact strict_mono_infinite hm

open scoped Classical in
theorem Nat.segment_lower_bound (hm : StrictMono φ) (h0 : φ 0 = 0) (k : ℕ) :
    φ (segment φ k) ≤ k := by
  rw [nth_of_strict_mono hm (segment φ k), segment]
  rcases Classical.em (k ∈ range φ) with h_k | h_k
  · have h1 : count (· ∈ range φ) (k + 1) = count (· ∈ range φ) k + 1 := by
      exact count_succ_eq_succ_count h_k
    rw [h1, Nat.add_one_sub_one, nth_count h_k]
  · have h2 : count (· ∈ range φ) (k + 1) = count (· ∈ range φ) k := by
      exact count_succ_eq_count h_k
    rw [h2]
    suffices _ : nth (· ∈ range φ) (count (· ∈ range φ) k - 1) < k by omega
    apply nth_lt_of_lt_count
    have : count (· ∈ range φ) k > 0 := by exact count_notin_range_pos h0 k h_k
    omega

open scoped Classical in
theorem Nat.segment_range_val (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m ≤ k) (hu : k < φ (m + 1)) : segment φ k = m := by
  obtain (rfl | hu') := show φ m = k ∨ φ m < k by omega
  · exact segment_idem hm m
  obtain ⟨j, h_j, rfl⟩ : ∃ j < φ (m + 1) - φ m - 1, k = j + φ m + 1 := by use (k - φ m - 1) ; omega
  induction' j with j h_ind
  · have h1 : count (· ∈ range φ) (φ m + 1) = count (· ∈ range φ) (φ m) + 1 := by
      apply count_succ_eq_succ_count ; use m
    have h2 : count (· ∈ range φ) (φ m + 1 + 1) = count (· ∈ range φ) (φ m + 1) := by
      apply count_succ_eq_count
      apply strict_mono_range_gap hm (show φ m < φ m + 1 by omega) ; omega
    have h3 := nth_of_strict_mono hm m
    rw [segment, zero_add, h2, h1, Nat.add_one_sub_one, h3]
    apply count_nth_of_infinite (strict_mono_infinite hm)
  specialize h_ind (by omega) (by omega) (by omega) (by omega)
  have h1 : count (· ∈ range φ) (j + 1 + φ m + 1) = count (· ∈ range φ) (j + 1 + φ m) := by
    apply count_succ_eq_count
    apply strict_mono_range_gap hm (show φ m < j + 1 + φ m by omega) ; omega
  have h2 : count (· ∈ range φ) (j + 1 + φ m + 1 + 1) =
    count (· ∈ range φ) (j + 1 + φ m + 1) := by
    apply count_succ_eq_count
    apply strict_mono_range_gap hm (show φ m < j + 1 + φ m + 1 by omega) ; omega
  rw [segment, (show j + «φ» m + 1 = j + 1 + φ m by omega), h1] at h_ind
  rw [segment, h2, h1, h_ind]

theorem Nat.segment_galois_connection (hm : StrictMono φ) (h0 : φ 0 = 0) :
    GaloisConnection φ (segment φ) := by
  intro m k ; constructor
  · intro h
    by_contra! h_con
    have h1 : segment φ k + 1 ≤ m := by omega
    have := (StrictMono.le_iff_le hm).mpr h1
    have := segment_upper_bound hm h0 k
    omega
  · intro h
    by_contra! h_con
    have := (StrictMono.le_iff_le hm).mpr h
    have := segment_lower_bound hm h0 k
    omega

/-- Nat.segment' is a helper function that will be proved to be equal to `Nat.segment`.
It facilitates the proofs of some theorems below. -/
noncomputable def Nat.segment' (φ : ℕ → ℕ) (k : ℕ) : ℕ :=
  segment (φ · - φ 0) (k - φ 0)

private lemma base_zero_shift (φ : ℕ → ℕ) :
    (φ · - φ 0) 0 = 0 := by
  simp

private lemma base_zero_strict_mono (hm : StrictMono φ) :
    StrictMono (φ · - φ 0) := by
  intro m n h_m_n ; simp
  have := hm h_m_n
  have : φ 0 ≤ φ m := by simp [StrictMono.le_iff_le hm]
  have : φ 0 ≤ φ n := by simp [StrictMono.le_iff_le hm]
  omega

open scoped Classical in
theorem Nat.segment'_eq_segment (hm : StrictMono φ) :
    segment' φ = segment φ := by
  ext k ; unfold segment'
  rcases (show k < φ 0 ∨ k ≥ φ 0 by omega) with h_k | h_k
  · have h0 : segment (φ · - φ 0) (k - φ 0) = 0 := by
      rw [show k - φ 0 = 0 by omega]
      exact segment_zero (base_zero_strict_mono hm) (base_zero_shift φ)
    rw [h0, segment_pre_zero hm h_k]
  unfold segment ; congr 1
  simp only [count_eq_card_filter_range]
  suffices h : ∃ f, BijOn f
      ({x ∈ Finset.range (k - φ 0 + 1) | x ∈ range fun x => φ x - φ 0}).toSet
      ({x ∈ Finset.range (k + 1) | x ∈ range φ}).toSet by
    obtain ⟨f, h_bij⟩ := h
    exact BijOn.finsetCard_eq f h_bij
  use (fun n ↦ n + φ 0) ; unfold BijOn ; constructorm* _ ∧ _
  · intro n ; simp only [mem_range, Finset.coe_filter, Finset.mem_range, mem_setOf_eq]
    rintro ⟨h_n, i, rfl⟩
    have := StrictMono.monotone hm <| zero_le i
    constructor
    · omega
    · use i ; omega
  · apply injOn_of_injective ; intro i j ; grind
  · intro n ; simp only [mem_range, Finset.coe_filter, Finset.mem_range, mem_setOf_eq, mem_image]
    rintro ⟨h_n, i, rfl⟩
    have := StrictMono.monotone hm <| zero_le i
    use (φ i - φ 0) ; constructorm* _ ∧ _
    · omega
    · use i
    · omega

theorem Nat.segment_zero' (hm : StrictMono φ) {k : ℕ} (h : k ≤ φ 0) :
    segment φ k = 0 := by
  rw [← segment'_eq_segment hm, segment', (show k - φ 0 = 0 by omega)]
  exact segment_zero (base_zero_strict_mono hm) (base_zero_shift φ)

theorem Nat.segment_upper_bound' (hm : StrictMono φ) {k : ℕ} (h : φ 0 ≤ k) :
    k < φ (segment φ k + 1) := by
  rw [← segment'_eq_segment hm, segment']
  have := segment_upper_bound (base_zero_strict_mono hm) (base_zero_shift φ) (k - φ 0)
  omega

theorem Nat.segment_lower_bound' (hm : StrictMono φ) {k : ℕ} (h : φ 0 ≤ k) :
    φ (segment φ k) ≤ k := by
  rw [← segment'_eq_segment hm, segment']
  have := segment_lower_bound (base_zero_strict_mono hm) (base_zero_shift φ) (k - φ 0)
  omega
