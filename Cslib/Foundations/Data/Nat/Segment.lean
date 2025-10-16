/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
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
@[scoped grind]
noncomputable def Nat.segment (φ : ℕ → ℕ) (k : ℕ) : ℕ :=
  open scoped Classical in
  Nat.count (· ∈ range φ) (k + 1) - 1

variable {φ : ℕ → ℕ}

/-- Any strictly monotonic function `φ : ℕ → ℕ` has an infinite range. -/
theorem Nat.strict_mono_infinite (hm : StrictMono φ) :
    (range φ).Infinite :=
  infinite_range_of_injective hm.injective

/-- Any infinite suset of `ℕ` is the range of a strictly monotonic function. -/
theorem Nat.infinite_strict_mono {ns : Set ℕ} (h : ns.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ range φ = ns :=
  ⟨Nat.nth (· ∈ ns), Nat.nth_strictMono h, Nat.range_nth_of_infinite h⟩

/-- There is a gap between two successive occurrences of a predicate `p : ℕ → Prop`,
assuming `p` (as a set) is infinite. -/
theorem Nat.nth_succ_gap {p : ℕ → Prop} (hf : (setOf p).Infinite) (n : ℕ) :
    ∀ k < Nat.nth p (n + 1) - Nat.nth p n, k > 0 → ¬ p (k + Nat.nth p n) := by
  classical
  intro k h_k1 h_k0 h_p_k
  let m := Nat.count p (k + Nat.nth p n)
  have h_k_ex : Nat.nth p m = k + Nat.nth p n := by simp [m, Nat.nth_count h_p_k]
  have h_n_m : n < m := by apply (Nat.nth_lt_nth hf).mp ; omega
  have h_m_n : m < n + 1 := by apply (Nat.nth_lt_nth hf).mp ; omega
  omega

/-- For a strictly monotonic function `φ : ℕ → ℕ`, `φ n` is exactly the n-th
element of the range of `φ`. -/
theorem Nat.nth_of_strict_mono (hm : StrictMono φ) (n : ℕ) :
    φ n = Nat.nth (· ∈ range φ) n := by
  have (hf : (range φ).Finite) : False := hf.not_infinite (strict_mono_infinite hm)
  rw [←Nat.nth_comp_of_strictMono hm] <;> first | grind | simp

open scoped Classical in
/-- If `φ 0 = 0`, then `0` is below any `n` not in the range of `φ`. -/
theorem Nat.count_notin_range_pos (h0 : φ 0 = 0) (n : ℕ) (hn : n ∉ range φ) :
    Nat.count (· ∈ range φ) n > 0 := by
  have := Nat.count_monotone (· ∈ range φ) (show 1 ≤ n by grind)
  grind

/-- For a strictly monotonic function `φ : ℕ → ℕ`, no number (strictly) between
`φ m` and ` φ (m + 1)` is in the range of `φ`. -/
theorem Nat.strict_mono_range_gap (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m < k) (hu : k < φ (m + 1)) : k ∉ range φ := by
  rw [nth_of_strict_mono hm m] at hl
  rw [nth_of_strict_mono hm (m + 1)] at hu
  have h_inf := strict_mono_infinite hm
  have h_gap := nth_succ_gap (p := (· ∈ range φ)) h_inf m
    (k - Nat.nth (· ∈ range φ) m) (by omega) (by omega)
  rw [(show k - Nat.nth (· ∈ range φ) m + Nat.nth (· ∈ range φ) m = k by omega)] at h_gap
  exact h_gap

/-- For a strictly monotonic function `φ : ℕ → ℕ`, the segment of `φ k` is `k`. -/
@[simp]
theorem Nat.segment_idem (hm : StrictMono φ) (k : ℕ) :
    segment φ (φ k) = k := by
  classical
  have := Nat.count_nth_of_infinite (p := (· ∈ range φ)) <| strict_mono_infinite hm
  have := nth_of_strict_mono hm
  grind [segment]

/-- For a strictly monotonic function `φ : ℕ → ℕ`, `segment φ k = 0` for all `k < φ 0`. -/
@[scoped grind =]
theorem Nat.segment_pre_zero (hm : StrictMono φ) {k : ℕ} (h : k < φ 0) :
    segment φ k = 0 := by
  classical
  have h1 : Nat.count (· ∈ range φ) (k + 1) = 0 := by
    apply Nat.count_of_forall_not
    rintro n h_n ⟨i, rfl⟩
    have := StrictMono.monotone hm <| zero_le i
    omega
  rw [segment, h1]

/-- For a strictly monotonic function `φ : ℕ → ℕ` with `φ 0 = 0`, `segment φ 0 = 0`. -/
@[scoped grind =]
theorem Nat.segment_zero (hm : StrictMono φ) (h0 : φ 0 = 0) :
    segment φ 0 = 0 := by
  calc _ = segment φ (φ 0) := by simp [h0]
       _ = _ := by simp [segment_idem hm]

open scoped Classical in
/-- A slight restatement of the definition of `segment` which has proven useful. -/
theorem Nat.segment_plus_one (h0 : φ 0 = 0) (k : ℕ) :
    segment φ k + 1 = Nat.count (· ∈ range φ) (k + 1) := by
  suffices _ : Nat.count (· ∈ range φ) (k + 1) ≠ 0 by unfold segment ; omega
  apply Nat.count_ne_iff_exists.mpr ; use 0 ; grind

/-- For a strictly monotonic function `φ : ℕ → ℕ` with `φ 0 = 0`,
`k < φ (segment φ k + 1)` for all `k : ℕ`. -/
theorem Nat.segment_upper_bound (hm : StrictMono φ) (h0 : φ 0 = 0) (k : ℕ) :
    k < φ (segment φ k + 1) := by
  classical
  rw [nth_of_strict_mono hm (segment φ k + 1), segment_plus_one h0 k]
  suffices _ : k + 1 ≤ Nat.nth (· ∈ range φ) (Nat.count (· ∈ range φ) (k + 1)) by omega
  apply Nat.le_nth_count
  exact strict_mono_infinite hm

/-- For a strictly monotonic function `φ : ℕ → ℕ` with `φ 0 = 0`,
`φ (segment φ k) ≤ k` for all `k : ℕ`. -/
theorem Nat.segment_lower_bound (hm : StrictMono φ) (h0 : φ 0 = 0) (k : ℕ) :
    φ (segment φ k) ≤ k := by
  classical
  rw [nth_of_strict_mono hm (segment φ k), segment]
  rcases Classical.em (k ∈ range φ) with h_k | h_k
  · simp_all [Nat.count_succ_eq_succ_count]
  · have h1 : Nat.count (· ∈ range φ) k > 0 := count_notin_range_pos h0 k h_k
    have h2 : Nat.count (· ∈ range φ) (k + 1) = Nat.count (· ∈ range φ) k :=
      Nat.count_succ_eq_count h_k
    rw [h2]
    suffices _ : Nat.nth (· ∈ range φ) (Nat.count (· ∈ range φ) k - 1) < k by omega
    apply Nat.nth_lt_of_lt_count
    omega

/-- For a strictly monotonic function `φ : ℕ → ℕ`, all `k` satisfying `φ m ≤ k < φ (m + 1)`
has `segment φ k = m`. -/
theorem Nat.segment_range_val (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m ≤ k) (hu : k < φ (m + 1)) : segment φ k = m := by
  classical
  obtain (rfl | hu') := show φ m = k ∨ φ m < k by omega
  · exact segment_idem hm m
  · obtain ⟨j, h_j, rfl⟩ : ∃ j < φ (m + 1) - φ m - 1, k = j + φ m + 1 := ⟨k - φ m - 1, by omega⟩
    induction j
    case zero =>
      have : Nat.count (· ∈ range φ) (φ m + 1 + 1) = Nat.count (· ∈ range φ) (φ m + 1) := by
        have := strict_mono_range_gap hm (show φ m < φ m + 1 by grind)
        grind
      have := nth_of_strict_mono hm m
      grind [Nat.count_nth_of_infinite, strict_mono_infinite]
    case succ j _ =>
      have := strict_mono_range_gap hm (show φ m < j + 1 + φ m     by grind)
      have := strict_mono_range_gap hm (show φ m < j + 1 + φ m + 1 by grind)
      grind

/-- For a strictly monotonic function `φ : ℕ → ℕ` with `φ 0 = 0`,
`φ` and `segment φ` form a Galois connection. -/
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

/-- For a strictly monotonic function `φ : ℕ → ℕ`,
`segment' φ` and `segment φ` are actually equal. -/
theorem Nat.segment'_eq_segment (hm : StrictMono φ) :
    segment' φ = segment φ := by
  classical
  ext k ; unfold segment'
  rcases (show k < φ 0 ∨ k ≥ φ 0 by omega) with h_k | h_k
  · have : k - φ 0 = 0 := by grind
    grind
  unfold segment ; congr 1
  simp only [Nat.count_eq_card_filter_range]
  suffices h : ∃ f, BijOn f
      ({x ∈ Finset.range (k - φ 0 + 1) | x ∈ range fun x => φ x - φ 0}).toSet
      ({x ∈ Finset.range (k + 1) | x ∈ range φ}).toSet by
    obtain ⟨f, h_bij⟩ := h
    exact BijOn.finsetCard_eq f h_bij
  refine ⟨fun n ↦ n + φ 0, ?_, ?_, ?_⟩
  · intro n ; simp only [mem_range, Finset.coe_filter, Finset.mem_range, mem_setOf_eq]
    rintro ⟨h_n, i, rfl⟩
    have := StrictMono.monotone hm <| zero_le i
    refine ⟨?_, i, ?_⟩ <;> omega
  · grind [injOn_of_injective, Injective]
  · intro n ; simp only [mem_range, Finset.coe_filter, Finset.mem_range, mem_setOf_eq, mem_image]
    rintro ⟨h_n, i, rfl⟩
    have := StrictMono.monotone hm <| zero_le i
    refine ⟨φ i - φ 0, ⟨by omega, i, rfl⟩, by omega⟩

/-- For a strictly monotonic function `φ : ℕ → ℕ`, `segment φ k = 0` for all `k ≤ φ 0`. -/
theorem Nat.segment_zero' (hm : StrictMono φ) {k : ℕ} (h : k ≤ φ 0) :
    segment φ k = 0 := by
  rw [← segment'_eq_segment hm, segment', (show k - φ 0 = 0 by omega)]
  grind

/-- For a strictly monotonic function `φ : ℕ → ℕ`, `k < φ (segment φ k + 1)` for all `k ≥ φ 0`. -/
theorem Nat.segment_upper_bound' (hm : StrictMono φ) {k : ℕ} (h : φ 0 ≤ k) :
    k < φ (segment φ k + 1) := by
  rw [← segment'_eq_segment hm, segment']
  have := segment_upper_bound (base_zero_strict_mono hm) (base_zero_shift φ) (k - φ 0)
  omega

/-- For a strictly monotonic function `φ : ℕ → ℕ`, `φ (segment φ k) ≤ k` for all `k ≥ φ 0`. -/
theorem Nat.segment_lower_bound' (hm : StrictMono φ) {k : ℕ} (h : φ 0 ≤ k) :
    φ (segment φ k) ≤ k := by
  rw [← segment'_eq_segment hm, segment']
  have := segment_lower_bound (base_zero_strict_mono hm) (base_zero_shift φ) (k - φ 0)
  omega
