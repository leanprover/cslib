/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Nat.Nth

/-!
# Segments defined by a strictly monotonic function on Nat

Given a strictly monotonic function `f : ℕ → ℕ` and `k : ℕ` with `k ≥ f 0`,
`Nat.segment f k` is the unique `m : ℕ` such that `f m ≤ k < f (m + 1)`.
`Nat.segment f k` is defined to be 0 for `k < f 0`.
This file defines `Nat.segment` and proves various properties about it.
-/

@[expose] public section

open Function Set

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
theorem nth_succ_gap {p : ℕ → Prop} (hf : (ofPred p).Infinite) (n : ℕ) :
    ∀ k < nth p (n + 1) - nth p n, 0 < k → ¬ p (k + nth p n) := by
  intro k hk hk0 hp
  have := (nth_add_one_le_iff hf (n := n) hp).2 (by omega)
  omega

/-- For a strictly monotonic function `f : ℕ → ℕ`, `f n` is exactly the n-th
element of the range of `f`. -/
theorem nth_of_strictMono (hm : StrictMono f) (n : ℕ) :
    f n = nth (· ∈ range f) n := by
  simpa using nth_comp_of_strictMono (p := (· ∈ range f)) (n := n) hm
    (fun _ h => h) (fun hf => (strictMono_infinite hm hf).elim)

open scoped Classical in
/-- If `f 0 = 0`, then `0` is below any `n` not in the range of `f`. -/
theorem count_notMem_range_pos (h0 : f 0 = 0) (n : ℕ) (hn : n ∉ range f) :
    0 < count (· ∈ range f) n := by
  have := count_monotone (· ∈ range f) (show 1 ≤ n by grind)
  grind

/-- For a strictly monotonic function `f : ℕ → ℕ`, no number (strictly) between
`f m` and ` f (m + 1)` is in the range of `f`. -/
theorem strictMono_range_gap (hm : StrictMono f) {m k : ℕ}
    (hl : f m < k) (hu : k < f (m + 1)) : k ∉ range f := by
  rintro ⟨i, rfl⟩
  have := hm.lt_iff_lt.mp hl
  have := hm.lt_iff_lt.mp hu
  omega

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
  have h := nth_lt_of_lt_count (p := (· ∈ range f))
    (show segment f k < count (· ∈ range f) (k + 1) by rw [← segment_plus_one h0]; omega)
  rwa [← nth_of_strictMono hm, Nat.lt_succ_iff] at h

/-- For a strictly monotonic function `f : ℕ → ℕ`, all `k` satisfying `f m ≤ k < f (m + 1)`
has `segment f k = m`. -/
theorem segment_range_val (hm : StrictMono f) {m k : ℕ}
    (hl : f m ≤ k) (hu : k < f (m + 1)) : segment f k = m := by
  classical
  -- Exactly `m + 1` values in the range of `f` are at most `k`.
  have h_inf := strictMono_infinite hm
  have h_lower : m < count (· ∈ range f) (k + 1) :=
    (lt_nth_iff_count_lt (p := (· ∈ range f)) h_inf).2
      (by rwa [← nth_of_strictMono hm, Nat.lt_succ_iff])
  have h_upper : count (· ∈ range f) (k + 1) ≤ m + 1 :=
    (count_le_iff_le_nth (p := (· ∈ range f)) h_inf).2
      (by rwa [← nth_of_strictMono hm, Nat.succ_le_iff])
  unfold segment
  omega

/-- For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`,
`f` and `segment f` form a Galois connection. -/
theorem segment_galois_connection (hm : StrictMono f) (h0 : f 0 = 0) :
    GaloisConnection f (segment f) := by
  intro m k
  constructor
  · intro h
    exact Nat.le_of_lt_succ (hm.lt_iff_lt.mp (h.trans_lt (segment_upper_bound hm h0 k)))
  · intro h
    exact (hm.monotone h).trans (segment_lower_bound hm h0 k)

/-- `segment'` is a helper function that will be proved to be equal to `segment`.
It facilitates the proofs of some theorems below. -/
noncomputable def segment' (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  segment (f · - f 0) (k - f 0)

private lemma base_zero_shift (f : ℕ → ℕ) :
    (f · - f 0) 0 = 0 := by
  simp

theorem base_zero_strictMono (hm : StrictMono f) :
    StrictMono (f · - f 0) := by
  intro m n h
  exact Nat.sub_lt_sub_right (hm.monotone (Nat.zero_le m)) (hm h)

/-- For a strictly monotonic function `f : ℕ → ℕ`,
`segment' f` and `segment f` are actually equal. -/
theorem segment'_eq_segment (hm : StrictMono f) :
    segment' f = segment f := by
  ext k
  unfold segment'
  by_cases hk : k < f 0
  · rw [segment_pre_zero hm hk, Nat.sub_eq_zero_of_le (by omega)]
    exact segment_zero (base_zero_strictMono hm) (by simp)
  · have h_lower := segment_lower_bound (base_zero_strictMono hm) (by simp) (k - f 0)
    have h_upper := segment_upper_bound (base_zero_strictMono hm) (by simp) (k - f 0)
    symm
    apply segment_range_val hm <;> omega

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
