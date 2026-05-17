/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Nat.Nth

@[expose] public section

open Function Set

/-!
# Segments defined by a strictly monotonic function on Nat

Given a strictly monotonic function `f : ℕ → ℕ` and `k : ℕ` with `k ≥ f 0`,
`Nat.segment f k` is the unique `m : ℕ` such that `f m ≤ k < f (k + 1)`.
`Nat.segment f k` is defined to be 0 for `k < f 0`.
This file defines `Nat.segment` and proves various properties aboout it.
-/

/-- The `f`-segment of `k`, where `f : ℕ → ℕ` will be assumed to be at least StrictMono. -/
@[scoped grind]
noncomputable def Nat.segment (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  open scoped Classical in
  Nat.count (· ∈ range f) (k + 1) - 1

namespace Nat

variable {f : ℕ → ℕ}

/-- Any strictly monotonic function `f : ℕ → ℕ` has an infinite range. -/
theorem strictMono_infinite (hm : StrictMono f) :
    (range f).Infinite :=
  infinite_range_of_injective hm.injective

/-- Any infinite subset of `ℕ` is the range of a strictly monotonic function. -/
theorem infinite_strictMono {ns : Set ℕ} (h : ns.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ range f = ns :=
  ⟨nth (· ∈ ns), nth_strictMono h, range_nth_of_infinite h⟩

/-- There is a gap between two successive occurrences of a predicate `p : ℕ → Prop`,
assuming `p` (as a set) is infinite. -/
theorem nth_succ_gap {p : ℕ → Prop} (hf : (setOf p).Infinite) (n : ℕ) :
    ∀ k < nth p (n + 1) - nth p n, k > 0 → ¬ p (k + nth p n) := by
  classical
  intro k h_k1 h_k0 h_p_k
  let m := count p (k + nth p n)
  have h_k_ex : nth p m = k + nth p n := by simp [m, nth_count h_p_k]
  have h_n_m : n < m := by apply (nth_lt_nth hf).mp; omega
  have h_m_n : m < n + 1 := by apply (nth_lt_nth hf).mp; omega
  omega

/-- For a strictly monotonic function `f : ℕ → ℕ`, `f n` is exactly the n-th
element of the range of `f`. -/
theorem nth_of_strictMono (hm : StrictMono f) (n : ℕ) :
    f n = nth (· ∈ range f) n := by
  have (hf : (range f).Finite) : False := hf.not_infinite (strictMono_infinite hm)
  rw [←nth_comp_of_strictMono hm] <;> first | grind | simp

open scoped Classical in
/-- If `f 0 = 0`, then `0` is below any `n` not in the range of `f`. -/
theorem count_notMem_range_pos (h0 : f 0 = 0) (n : ℕ) (hn : n ∉ range f) :
    count (· ∈ range f) n > 0 := by
  have := count_monotone (· ∈ range f) (show 1 ≤ n by grind)
  grind

/-- For a strictly monotonic function `f : ℕ → ℕ`, no number (strictly) between
`f m` and ` f (m + 1)` is in the range of `f`. -/
theorem strictMono_range_gap (hm : StrictMono f) {m k : ℕ}
    (hl : f m < k) (hu : k < f (m + 1)) : k ∉ range f := by
  rw [nth_of_strictMono hm m] at hl
  rw [nth_of_strictMono hm (m + 1)] at hu
  have h_inf := strictMono_infinite hm
  have h_gap := nth_succ_gap (p := (· ∈ range f)) h_inf m
    (k - nth (· ∈ range f) m) (by omega) (by omega)
  rw [(show k - nth (· ∈ range f) m + nth (· ∈ range f) m = k by omega)] at h_gap
  exact h_gap

/-- For a strictly monotonic function `f : ℕ → ℕ`, the segment of `f k` is `k`. -/
@[simp]
theorem segment_idem (hm : StrictMono f) (k : ℕ) :
    segment f (f k) = k := by
  classical
  have := count_nth_of_infinite (p := (· ∈ range f)) <| strictMono_infinite hm
  have := nth_of_strictMono hm
  grind [segment]

/-- For a strictly monotonic function `f : ℕ → ℕ`, `segment f k = 0` for all `k < f 0`. -/
@[scoped grind =]
theorem segment_pre_zero (hm : StrictMono f) {k : ℕ} (h : k < f 0) :
    segment f k = 0 := by
  classical
  have h1 : count (· ∈ range f) (k + 1) = 0 := by
    apply count_of_forall_not
    rintro n h_n ⟨i, rfl⟩
    have := StrictMono.monotone hm <| zero_le i
    omega
  rw [segment, h1]

/-- For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`, `segment f 0 = 0`. -/
@[scoped grind =]
theorem segment_zero (hm : StrictMono f) (h0 : f 0 = 0) :
    segment f 0 = 0 := by
  calc _ = segment f (f 0) := by simp [h0]
       _ = _ := by simp [segment_idem hm]

open scoped Classical in
/-- A slight restatement of the definition of `segment` which has proven useful. -/
theorem segment_plus_one (h0 : f 0 = 0) (k : ℕ) :
    segment f k + 1 = count (· ∈ range f) (k + 1) := by
  suffices _ : count (· ∈ range f) (k + 1) ≠ 0 by unfold segment; omega
  apply count_ne_iff_exists.mpr; use 0; grind

/-- For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`,
`k < f (segment f k + 1)` for all `k : ℕ`. -/
theorem segment_upper_bound (hm : StrictMono f) (h0 : f 0 = 0) (k : ℕ) :
    k < f (segment f k + 1) := by
  classical
  rw [nth_of_strictMono hm (segment f k + 1), segment_plus_one h0 k]
  suffices _ : k + 1 ≤ nth (· ∈ range f) (count (· ∈ range f) (k + 1)) by omega
  apply le_nth_count
  exact strictMono_infinite hm

/-- For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`,
`f (segment f k) ≤ k` for all `k : ℕ`. -/
theorem segment_lower_bound (hm : StrictMono f) (h0 : f 0 = 0) (k : ℕ) :
    f (segment f k) ≤ k := by
  classical
  rw [nth_of_strictMono hm (segment f k), segment]
  rcases Classical.em (k ∈ range f) with h_k | h_k
  · simp_all [count_succ_eq_succ_count]
  · have h1 : count (· ∈ range f) k > 0 := count_notMem_range_pos h0 k h_k
    have h2 : count (· ∈ range f) (k + 1) = count (· ∈ range f) k :=
      count_succ_eq_count h_k
    rw [h2]
    suffices _ : nth (· ∈ range f) (count (· ∈ range f) k - 1) < k by omega
    apply nth_lt_of_lt_count
    omega

/-- For a strictly monotonic function `f : ℕ → ℕ`, all `k` satisfying `f m ≤ k < f (m + 1)`
has `segment f k = m`. -/
theorem segment_range_val (hm : StrictMono f) {m k : ℕ}
    (hl : f m ≤ k) (hu : k < f (m + 1)) : segment f k = m := by
  classical
  obtain (rfl | hu') := show f m = k ∨ f m < k by omega
  · exact segment_idem hm m
  · obtain ⟨j, h_j, rfl⟩ : ∃ j < f (m + 1) - f m - 1, k = j + f m + 1 := ⟨k - f m - 1, by omega⟩
    induction j
    case zero =>
      have : count (· ∈ range f) (f m + 1 + 1) = count (· ∈ range f) (f m + 1) := by
        have := strictMono_range_gap hm (show f m < f m + 1 by grind)
        grind
      have := nth_of_strictMono hm m
      grind [count_nth_of_infinite, strictMono_infinite]
    case succ j _ =>
      have := strictMono_range_gap hm (show f m < j + 1 + f m     by grind)
      have := strictMono_range_gap hm (show f m < j + 1 + f m + 1 by grind)
      grind

/-- For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`,
`f` and `segment f` form a Galois connection. -/
theorem segment_galois_connection (hm : StrictMono f) (h0 : f 0 = 0) :
    GaloisConnection f (segment f) := by
  intro m k; constructor
  · intro h
    by_contra! h_con
    have h1 : segment f k + 1 ≤ m := by omega
    have := (StrictMono.le_iff_le hm).mpr h1
    have := segment_upper_bound hm h0 k
    omega
  · intro h
    by_contra! h_con
    have := (StrictMono.le_iff_le hm).mpr h
    have := segment_lower_bound hm h0 k
    omega

/-- `segment'` is a helper function that will be proved to be equal to `segment`.
It facilitates the proofs of some theorems below. -/
noncomputable def segment' (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  segment (f · - f 0) (k - f 0)

private lemma base_zero_shift (f : ℕ → ℕ) :
    (f · - f 0) 0 = 0 := by
  simp

theorem base_zero_strictMono (hm : StrictMono f) :
    StrictMono (f · - f 0) := by
  intro m n h_m_n; simp
  have := hm h_m_n
  have : f 0 ≤ f m := by simp [StrictMono.le_iff_le hm]
  have : f 0 ≤ f n := by simp [StrictMono.le_iff_le hm]
  omega

/-- For a strictly monotonic function `f : ℕ → ℕ`,
`segment' f` and `segment f` are actually equal. -/
theorem segment'_eq_segment (hm : StrictMono f) :
    segment' f = segment f := by
  classical
  ext k; unfold segment'
  rcases (show k < f 0 ∨ k ≥ f 0 by omega) with h_k | h_k
  · grind
  unfold segment; congr 1
  simp only [count_eq_card_filter_range]
  suffices h : ∃ g, BijOn g
      ({x ∈ Finset.range (k - f 0 + 1) | x ∈ range fun x => f x - f 0})
      ({x ∈ Finset.range (k + 1) | x ∈ range f}) by
    grind [BijOn.finsetCard_eq, Finset.coe_filter]
  refine ⟨fun n ↦ n + f 0, ?_, ?_, ?_⟩
  · intro n; simp only [mem_range, Finset.mem_range, mem_setOf_eq]
    rintro ⟨h_n, i, rfl⟩
    have := StrictMono.monotone hm <| zero_le i
    refine ⟨?_, i, ?_⟩ <;> omega
  · grind [injOn_of_injective, Injective]
  · intro n; simp only [mem_range, Finset.mem_range, mem_setOf_eq, mem_image]
    rintro ⟨h_n, i, rfl⟩
    have := StrictMono.monotone hm <| zero_le i
    grind

/-- For a strictly monotonic function `f : ℕ → ℕ`, `segment f k = 0` for all `k ≤ f 0`. -/
theorem segment_zero' (hm : StrictMono f) {k : ℕ} (h : k ≤ f 0) :
    segment f k = 0 := by
  rw [← segment'_eq_segment hm, segment', (show k - f 0 = 0 by omega)]
  grind

/-- For a strictly monotonic function `f : ℕ → ℕ`, `k < f (segment f k + 1)` for all `k ≥ f 0`. -/
theorem segment_upper_bound' (hm : StrictMono f) {k : ℕ} (h : f 0 ≤ k) :
    k < f (segment f k + 1) := by
  rw [← segment'_eq_segment hm, segment']
  have := segment_upper_bound (base_zero_strictMono hm) (base_zero_shift f) (k - f 0)
  omega

/-- For a strictly monotonic function `f : ℕ → ℕ`, `f (segment f k) ≤ k` for all `k ≥ f 0`. -/
theorem segment_lower_bound' (hm : StrictMono f) {k : ℕ} (h : f 0 ≤ k) :
    f (segment f k) ≤ k := by
  rw [← segment'_eq_segment hm, segment']
  have := segment_lower_bound (base_zero_strictMono hm) (base_zero_shift f) (k - f 0)
  omega

end Nat
