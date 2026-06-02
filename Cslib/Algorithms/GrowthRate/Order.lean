/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

module

public import Cslib.Algorithms.GrowthRate.Closure

/-!
# Ordering of Growth Rates

-/

@[expose] public section

namespace CSLib

open scoped Topology

namespace GrowthRate

theorem const_subset_log : const ⊆ log := by
  refine fun _ h ↦ h.trans ?_
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨1, 2, fun _ hn ↦ ?_⟩
  exact one_le_mul_of_one_le_of_one_le le_rfl (mod_cast Nat.le_log_of_pow_le one_lt_two hn)

theorem const_ssubset_log : const ⊂ log := by
  simp only [const, log, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset,
    Pi.one_apply, Nat.cast_one]
  use const_subset_log
  simp only [Asymptotics.isBigO_one_iff, Int.norm_natCast, not_forall]
  use Nat.log 2, Asymptotics.isBigO_refl _ _
  norm_num [Filter.IsBoundedUnder, Filter.IsBounded]
  intro x n
  rcases exists_nat_gt x with ⟨k, hk⟩
  refine ⟨2 ^ (n + k + 1), ?_, ?_⟩
  · linarith [(n + k + 1).lt_two_pow_self]
  · rw [Nat.log_pow (by norm_num)]
    push_cast
    linarith

theorem log_ssubset_polylog : log ⊂ polylog := by
  rw [log, polylog, ssubset_iff_subset_not_subset]
  simp only [bigO, Set.setOf_subset_setOf, forall_exists_index, not_forall]
  use fun f h ↦ ⟨1, by simpa [pow_one] using h⟩
  use fun n ↦ (Nat.log 2 n) ^ 2, 2, Asymptotics.isBigO_refl ..
  simp only [Classical.not_imp, Nat.cast_pow, Asymptotics.isBigO_iff, norm_pow, norm_natCast,
    Filter.eventually_atTop, not_exists, not_forall, not_le]
  intro x y
  obtain ⟨n, hn⟩ := exists_nat_gt x
  refine ⟨2 ^ (y + n + 1), ?_, ?_⟩
  · linarith [(y + n + 1).lt_two_pow_self]
  · simp only [one_lt_two, Nat.log_pow, Nat.cast_add, Nat.cast_one]
    nlinarith

/--
For f ∈ polylog, there exists k with f = O((log n)^k). We need f ∈ sqrt = bigO(Nat.sqrt).
Since (log n)^k / √n → 0 as n → ∞ (any power of log grows slower than √n), eventually
(log n)^k ≤ √n. From f(n) ≤ c * (log n)^k and (log n)^k ≤ √n eventually, we get
f(n) ≤ c * √n eventually.
-/
theorem polylog_subset_sqrt : polylog ⊆ sqrt := by
  intro f hf
  suffices h : ∃ N, ∀ n ≥ N, (f n : ℝ) ≤ (Nat.sqrt n : ℝ) by
    obtain ⟨N, hN⟩ := h
    simp_rw [sqrt, bigO, Set.mem_setOf, Asymptotics.isBigO_iff, Filter.eventually_atTop]
    exact ⟨1, N, (by simpa using hN · ·)⟩
  rcases hf with ⟨C, hC⟩
  have h_bound : Filter.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / √n) .atTop (𝓝 0) := by
    -- We can convert this statement into a form that allows us to apply the squeeze theorem.
    suffices h_convert : Filter.atTop.Tendsto (fun n : ℕ ↦ (Real.logb 2 n) ^ C / √n) (𝓝 0) by
      refine squeeze_zero_norm' ?_ h_convert
      norm_num [abs_div, abs_of_nonneg, Real.sqrt_nonneg]
      refine ⟨2, fun n hn ↦ ?_⟩
      gcongr
      rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
      exact Real.log_le_log (by positivity) (mod_cast Nat.pow_log_le_self _ <| by positivity)
    -- We apply the squeeze theorem by substituting `y = log n`.
    suffices h_convert : Filter.atTop.Tendsto (fun y ↦ (y / Real.log 2) ^ C / (y / 2).exp) (𝓝 0) by
      have := h_convert.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      apply this.congr'
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [Real.logb, Function.comp_apply, Function.comp_apply, Real.sqrt_eq_rpow,
        Real.rpow_def_of_pos (by positivity)]
      ring_nf
    -- We simplify the expression inside the limit further by substituting `z = y / 2`.
    suffices h_simp : Filter.atTop.Tendsto (fun z ↦ (2 * z / Real.log 2) ^ C / z.exp) (𝓝 0) by
      convert h_simp.comp (Filter.tendsto_id.atTop_mul_const (by norm_num : 0 < (2⁻¹ : ℝ))) using 2
      norm_num
      ring_nf
    suffices h_factor : Filter.atTop.Tendsto (fun z : ℝ ↦ z ^ C / z.exp) (𝓝 0) by
      convert h_factor.const_mul ((2 / Real.log 2) ^ C) using 2
      · ring
      · ring
    simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C
  obtain ⟨k, hk⟩ : ∃ k, ∀ᶠ n in .atTop, (f n : ℝ) ≤ k * (Nat.log 2 n : ℝ) ^ C := by
    rw [Asymptotics.isBigO_iff'] at hC; aesop
  have h_combined : ∃ N, ∀ n ≥ N, (k * (Nat.log 2 n : ℝ) ^ C) / √n ≤ 1 := by
    simpa [mul_div_assoc] using (h_bound.const_mul k).eventually (ge_mem_nhds <| by simp)
  obtain ⟨N, hN⟩ := h_combined
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hk
  use N ⊔ M + 1
  intro n hn
  specialize hN n (by linarith [le_max_left N M, le_max_right N M])
  specialize hM n (by linarith [le_max_left N M, le_max_right N M])
  rw [div_le_iff₀] at hN
  · rw [Nat.cast_le, Nat.le_sqrt, ← @Nat.cast_le ℝ, Nat.cast_mul]
    nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg n)]
  · grind [Real.sqrt_pos, Nat.cast_pos]

theorem polylog_ssubset_sqrt : polylog ⊂ sqrt := by
  use polylog_subset_sqrt
  simp only [polylog, sqrt, bigO, Set.setOf_subset_setOf]
  push Not
  use Nat.sqrt, Asymptotics.isBigO_refl ..
  intro C
  refine Asymptotics.IsLittleO.not_isBigO ?_ (Filter.frequently_atTop.mpr (⟨· + 2, by simp⟩))
  rw [Asymptotics.isLittleO_iff]
  intro c a
  simp only [Nat.cast_pow, norm_pow, norm_natCast, Filter.eventually_atTop]
  have h_log_growth : Filter.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / √n) .atTop (𝓝 0) := by
    have h_log_growth : Filter.Tendsto (fun x : ℝ ↦ (Real.logb 2 x) ^ C / √x) .atTop (𝓝 0) := by
      suffices h : Filter.Tendsto (fun y : ℝ ↦ y ^ C / √(2 ^ y)) .atTop (𝓝 0) by
        have := h.comp (Real.tendsto_log_atTop.const_mul_atTop (by positivity : 0 < (Real.log 2)⁻¹))
        refine this.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop 0] with x hx
        field_simp
        simp only [Function.comp_apply, Real.logb]
        -- Simplify the denominator: `√(2^((log x) / log 2)) = √x`.
        field_simp
        erw [Real.rpow_logb] <;> linarith
      suffices hy : Filter.atTop.Tendsto (fun y ↦ y ^ C / (y * Real.log 2 / 2).exp) (𝓝 0) by
        convert hy using 2; norm_num [Real.sqrt_eq_rpow, Real.rpow_def_of_pos]
        ring_nf
        rw [← Real.exp_mul]
      suffices h_log : Filter.Tendsto (fun z ↦ (2 * z / Real.log 2) ^ C / z.exp) .atTop (𝓝 0) by
        have h_log : Filter.atTop.Tendsto (fun y : ℝ ↦
            ((2 * (y * Real.log 2 / 2)) / Real.log 2) ^ C / (y * Real.log 2 / 2).exp) (𝓝 0) := by
          exact h_log.comp <| Filter.Tendsto.atTop_mul_const (by positivity) <|
            Filter.tendsto_id.atTop_mul_const (by positivity)
        convert h_log using 3
        ring_nf
        norm_num
      suffices h_term : Filter.atTop.Tendsto (fun z : ℝ ↦ z ^ C / z.exp) (𝓝 0) by
        convert h_term.const_mul ((Real.log 2) ⁻¹ ^ C * 2 ^ C) using 2
        · ring
        · ring
      simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C
    refine squeeze_zero_norm' ?_ (h_log_growth.comp tendsto_natCast_atTop_atTop)
    refine Filter.eventually_atTop.mpr ⟨2, fun n hn ↦ ?_⟩
    rw [Function.comp_apply, Real.norm_of_nonneg (by positivity)]
    gcongr
    rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_rpow zero_lt_two]
    apply Real.log_le_log (by positivity)
    norm_cast
    exact Nat.pow_log_le_self _ (by positivity)
  have this := h_log_growth.eventually (gt_mem_nhds <| show 0 < c / 2 by positivity)
  rw [Filter.eventually_atTop] at this
  obtain ⟨w, h⟩ := this
  refine ⟨w + 4, fun n hn ↦ ?_⟩
  specialize h n (by linarith)
  rw [div_lt_iff₀ (by norm_num; linarith)] at h
  refine le_trans (le_of_lt h) ?_
  have _ : (√n:ℝ) ≤ Nat.sqrt n + 1 := Real.sqrt_le_iff.2
    ⟨by positivity, by norm_cast; nlinarith [Nat.lt_succ_sqrt n]⟩
  nlinarith [show (Nat.sqrt n:ℝ) ≥ 1 from Nat.one_le_cast.2 (n.sqrt_pos.2 (by linarith))]

theorem sqrt_subset_sublinear : sqrt ⊆ sublinear := by
  simp only [sqrt, bigO, sublinear]
  intro f hf
  refine hf.trans_isLittleO ?_; clear f hf
  erw [Asymptotics.isLittleO_iff]
  intro c a
  simp only [Int.norm_natCast, Filter.eventually_atTop, id_eq]
  use Nat.ceil ((1 / c) ^ 2)
  intro b hb
  have h : (1 : ℝ) / c ≤ √b := (Real.le_sqrt_of_sq_le <| by simpa using hb)
  rw [div_le_iff₀ (by positivity)] at h
  have _ : b.sqrt  ≤ √(b : ℝ) := Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' b
  nlinarith [Real.sq_sqrt <| Nat.cast_nonneg b]

theorem sqrt_ssubset_sublinear : sqrt ⊂ sublinear := by
  use sqrt_subset_sublinear
  simp only [sqrt, sublinear, bigO]
  norm_num [littleO]
  use fun n ↦ Nat.sqrt n * Nat.log 2 n
  simp only [Nat.cast_mul]
  constructor
  · refine Asymptotics.isLittleO_iff.2 fun ε hε ↦ ?_
    have h_log_div : Filter.Tendsto (fun x : ℕ ↦ (Nat.log 2 x : ℝ) / √x) .atTop (𝓝 0) := by
      -- We use the change of variables `u = log₂ x` to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun u : ℝ ↦ u / 2^(u/2)) .atTop (𝓝 0) by
        have h_log : Filter.Tendsto (fun x : ℕ ↦
            (Nat.log 2 x : ℝ) / 2 ^ (Nat.log 2 x / 2 : ℝ)) .atTop (𝓝 0) := by
          apply h_log.comp
          apply tendsto_natCast_atTop_atTop.comp
          rw [Filter.tendsto_atTop_atTop]
          exact fun n ↦ ⟨2 ^ n, fun x hx ↦ Nat.le_log_of_pow_le (by norm_num) hx⟩
        refine squeeze_zero_norm' ?_ h_log
        simp only [norm_div, RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop]
        refine ⟨2, fun n hn ↦ ?_⟩
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        gcongr
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos, Real.rpow_def_of_pos] <;> norm_num
        · have := Real.log_le_log (by positivity)
            (show (n : ℝ) ≥ 2 ^ Nat.log 2 n by exact_mod_cast Nat.pow_log_le_self 2 (by positivity))
          norm_num at *
          nlinarith [Real.log_pos one_lt_two]
        · linarith
      suffices h_exp : Filter.atTop.Tendsto (fun u ↦ u / (u * Real.log 2 / 2).exp) (𝓝 0) by
        convert h_exp using 2
        norm_num [Real.rpow_def_of_pos]
        ring_nf
      suffices h_y : Filter.Tendsto (fun y : ℝ ↦ 2 * y / Real.exp y) .atTop (𝓝 0) by
        have h := h_y.comp (Filter.tendsto_id.atTop_mul_const (by positivity : 0 < Real.log 2 / 2))
        convert h.div_const (Real.log 2) using 2 <;> norm_num
        ring_nf
        norm_num [mul_assoc, mul_comm, mul_left_comm]
      simpa [mul_div_assoc, Real.exp_neg] using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 2
    replace h_log_div := h_log_div.eventually (gt_mem_nhds <| show 0 < ε by positivity)
    simp only [Filter.eventually_atTop, norm_mul, norm_natCast] at h_log_div ⊢
    rcases h_log_div with ⟨w, h⟩
    refine ⟨w + 1, fun n hn ↦ ?_⟩
    specialize h n (by linarith)
    rw [div_lt_iff₀] at h
    · nlinarith [show (Nat.sqrt n : ℝ) ≤ √n from Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' n,
        Real.mul_self_sqrt <| Nat.cast_nonneg n,
        show (Nat.log 2 n : ℝ) ≥ 0 by positivity]
    · norm_num at *
      linarith
  · intro a
    contrapose! a
    rw [Asymptotics.isBigO_iff]
    simp only [norm_mul, norm_natCast, Filter.eventually_atTop, not_exists, not_forall,
      not_le]
    intro x x₁
    have h_log_growth : Filter.atTop.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) - x) .atTop := by
      refine Filter.tendsto_atTop_add_const_right _ _ <| tendsto_natCast_atTop_atTop.comp ?_
      rw [Filter.tendsto_atTop_atTop]
      exact (⟨2 ^ ·, fun _ ↦ Nat.le_log_of_pow_le one_lt_two⟩)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h_log_growth.eventually_gt_atTop 0)
    use x₁ + N + 1, by linarith
    have _ : (Nat.sqrt (x₁ + N + 1) : ℝ) ≥ 1 := mod_cast Nat.sqrt_pos.mpr (by linarith)
    specialize hN (x₁ + N + 1) (by linarith)
    nlinarith

theorem sublinear_ssubset_linear : sublinear ⊂ linear := by
  simp only [littleO, linear, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset]
  push Not
  use fun _ ↦ Asymptotics.IsLittleO.isBigO, id, Asymptotics.isBigO_refl ..
  apply Asymptotics.isLittleO_irrefl'
  apply Filter.Eventually.frequently
  rw [Filter.eventually_atTop]
  use 1
  intro b hb
  simp [Nat.ne_zero_of_lt hb]

theorem linear_subset_linearithmic : linear ⊆ linearithmic := by
  refine fun _ h ↦ h.trans ?_
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨1, 2, fun n hn ↦ ?_⟩
  rw [one_mul]
  exact_mod_cast Nat.le_mul_of_pos_right n (Nat.log_pos one_lt_two hn)

theorem linear_ssubset_linearithmic : linear ⊂ linearithmic := by
  use linear_subset_linearithmic
  simp only [linearithmic, bigO, Nat.cast_mul, linear, id_eq, Set.setOf_subset_setOf, not_forall]
  use fun n ↦ n * Nat.log 2 n
  use mod_cast Asymptotics.isBigO_refl ..
  norm_num [Asymptotics.isBigO_iff]
  intro x k
  have ⟨n, hn⟩ := exists_nat_gt (|x| + 1)
  use 2 ^ (k + n)
  norm_num [Nat.log_pow]
  constructor
  · linarith [(k + n).lt_two_pow_self]
  · nlinarith [abs_lt.mp (show |x| < n by linarith), pow_pos (M₀ := ℝ) two_pos (k + n)]

theorem linearithmic_subset_nearLinear : linearithmic ⊆ nearLinear :=
  fun _ _ ↦ ⟨1, by simpa⟩

theorem linearithmic_ssubset_nearLinear : linearithmic ⊂ nearLinear := by
  use linearithmic_subset_nearLinear
  simp only [nearLinear, bigO, Set.setOf_subset_setOf, not_forall, exists_prop]
  use fun n ↦ n * (Nat.log 2 n) ^ 2
  use ⟨2, mod_cast Asymptotics.isBigO_refl ..⟩
  norm_num [Asymptotics.isBigO_iff', ← mul_assoc]
  intro x _ y
  have ⟨n, _⟩ := exists_nat_gt x
  refine ⟨2 ^ (y + n + 1), le_trans (by linarith) Nat.lt_two_pow_self.le, ?_⟩
  rw [Nat.log_pow Nat.one_lt_ofNat]
  push_cast
  nlinarith [(by positivity : 0 < (2 : ℝ) ^ (y + n + 1) * (y + n + 1))]

theorem nearLinear_subset_almostLinear : nearLinear ⊆ almostLinear := by
  intro f hf ε hε
  obtain ⟨C, hC⟩ := hf
  have h_log : (fun n => (n : ℝ) * (Real.log n) ^ C) =o[Filter.atTop]
      (fun n => (n : ℝ) ^ (1 + ε)) := by
    have h_log : Filter.Tendsto (fun n => (Real.log n) ^ C / (n : ℝ) ^ ε)
        Filter.atTop (nhds 0) := by
      suffices h_log : Filter.Tendsto (fun y : ℝ => y ^ C / Real.exp (y * ε))
          Filter.atTop (nhds 0) by
        have := h_log.comp Real.tendsto_log_atTop
        apply this.congr'
        filter_upwards [Filter.eventually_gt_atTop 0] with x hx
        simp +decide [Real.rpow_def_of_pos hx, mul_comm]
      suffices h_z : Filter.Tendsto (fun z : ℝ => z ^ C / Real.exp z)
          Filter.atTop (nhds 0) by
        have := h_z.comp (Filter.tendsto_id.atTop_mul_const hε)
        convert this.div_const (ε ^ C) using 2 <;>
          norm_num [div_eq_mul_inv, mul_pow, mul_assoc, mul_comm, mul_left_comm, hε.ne']
      simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C
    rw [Asymptotics.isLittleO_iff_tendsto']
    · apply h_log.congr'
      filter_upwards [Filter.eventually_gt_atTop 0] with x hx
      rw [Real.rpow_add hx, Real.rpow_one]
      rw [mul_div_mul_left _ _ hx.ne']
    · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' <| by positivity
  have h_bound : ∃ D : ℝ, ∀ᶠ n in Filter.atTop,
      (n * (Nat.log 2 n) ^ C : ℝ) ≤ D * (n : ℝ) * (Real.log n) ^ C := by
    use 1 / (Real.log 2) ^ C
    have h_log_bound : ∀ n ≥ 2, (Nat.log 2 n : ℝ) ≤ (Real.log n) / (Real.log 2) := by
      intro n hn; rw [le_div_iff₀ (Real.log_pos one_lt_two)]
      nth_rw 1 [← Real.log_pow]
      exact Real.log_le_log (by positivity) (mod_cast Nat.pow_log_le_self _ <| by positivity)
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    convert mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (h_log_bound n hn) C) (Nat.cast_nonneg n) using 1
    ring
  have h_final : (fun n => (n * (Nat.log 2 n) ^ C : ℝ)) =O[Filter.atTop]
      (fun n => (n : ℝ) ^ (1 + ε)) := by
    refine Asymptotics.IsBigO.trans ?_ (h_log.isBigO.comp_tendsto tendsto_natCast_atTop_atTop)
    change _ =O[Filter.atTop] (fun n => (n : ℝ) * (Real.log n) ^ C : ℕ → ℝ)
    rw [Asymptotics.isBigO_iff]
    obtain ⟨D, hD⟩ := h_bound
    use D
    filter_upwards [hD] with n hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), ← mul_assoc]
    exact hn
  refine Asymptotics.IsBigO.trans ?_ h_final
  simpa [Asymptotics.isBigO_iff] using hC

theorem nearLinear_ssubset_almostLinear : nearLinear ⊂ almostLinear := by
  refine ⟨nearLinear_subset_almostLinear, ?_⟩
  rw [Set.not_subset]
  use fun n => n * 2 ^ Nat.sqrt (Nat.log 2 n)
  constructor
  · intro ε hε
    have h_exp : ∃ N : ℕ, ∀ n ≥ N, (2 : ℝ) ^ Nat.sqrt (Nat.log 2 n) ≤ (n : ℝ) ^ ε := by
      have h_exp : ∃ N : ℕ, ∀ n ≥ N,
          (Nat.sqrt (Nat.log 2 n) : ℝ) ≤ ε * Real.logb 2 n := by
        have h_sqrt_log : ∃ N : ℕ, ∀ n ≥ N,
            (Nat.sqrt (Nat.log 2 n) : ℝ) ≤ ε * (Nat.log 2 n) := by
          have h_sqrt_log_aux : ∃ N : ℕ, ∀ n ≥ N, (Nat.sqrt n : ℝ) ≤ ε * n := by
            exact ⟨⌈ε⁻¹ ^ 2⌉₊ + 1, fun n hn => by
              nlinarith [Nat.le_ceil (ε⁻¹ ^ 2),
                show (n : ℝ) ≥ ⌈ε⁻¹ ^ 2⌉₊ + 1 by exact_mod_cast hn,
                inv_pos.2 hε, mul_inv_cancel₀ hε.ne',
                sq_nonneg (ε⁻¹ - Real.sqrt n),
                Real.mul_self_sqrt (Nat.cast_nonneg n),
                show (Nat.sqrt n : ℝ) ≤ Real.sqrt n by
                  exact Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' n]⟩
          exact ⟨2 ^ h_sqrt_log_aux.choose, fun n hn =>
            h_sqrt_log_aux.choose_spec _ <|
            Nat.le_log_of_pow_le (by norm_num) hn⟩
        refine ⟨h_sqrt_log.choose + 2, fun n hn =>
          le_trans (h_sqrt_log.choose_spec n (by linarith)) ?_⟩
        gcongr
        rw [Real.le_logb_iff_rpow_le] <;> norm_cast <;>
          linarith [Nat.pow_log_le_self 2 (by linarith : n ≠ 0)]
      obtain ⟨N, hN⟩ := h_exp; use N + 2; intro n hn
      specialize hN n (by linarith); rw [Real.logb] at hN
      rw [← Real.log_le_log_iff (by positivity)
        (by exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr <| by linarith) _), Real.log_pow]
      ring_nf at *
      rw [Real.log_rpow (by norm_cast; linarith)]
      nlinarith [Real.log_pos one_lt_two,
        mul_inv_cancel_left₀ (ne_of_gt (Real.log_pos one_lt_two)) (ε * Real.log n)]
    rw [Asymptotics.isBigO_iff]
    obtain ⟨N, hN⟩ := h_exp; use 1
    filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0] with n hn hn'
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    rw [Real.rpow_add <| by positivity, Real.rpow_one]; norm_cast
    simpa using mul_le_mul_of_nonneg_left (hN n hn) (Nat.cast_nonneg n)
  · rintro ⟨C, hC⟩
    have h_exp_growth : Filter.Tendsto
        (fun n => (2 ^ Nat.sqrt (Nat.log 2 n) : ℝ) / (Nat.log 2 n ^ C))
        Filter.atTop Filter.atTop := by
      suffices h_log : Filter.Tendsto (fun y : ℕ => (2 ^ Nat.sqrt y : ℝ) / (y ^ C))
          Filter.atTop Filter.atTop by
        exact h_log.comp (Filter.tendsto_atTop_atTop.mpr fun x =>
          ⟨2 ^ x, fun n hn => Nat.le_log_of_pow_le (by norm_num) hn⟩)
      suffices h_sqrt : Filter.Tendsto (fun z : ℕ => (2 ^ z : ℝ) / (z ^ (2 * C)))
          Filter.atTop Filter.atTop by
        have h_subst : Filter.Tendsto
            (fun y : ℕ => (2 ^ Nat.sqrt y : ℝ) / (Nat.sqrt y ^ (2 * C)))
            Filter.atTop Filter.atTop :=
          h_sqrt.comp <| Filter.tendsto_atTop_atTop.mpr fun x =>
            ⟨x ^ 2, fun y hy => by nlinarith [Nat.lt_succ_sqrt y]⟩
        have h_subst2 : ∀ᶠ y in Filter.atTop,
            (2 ^ Nat.sqrt y : ℝ) / (Nat.sqrt y ^ (2 * C)) ≤
            (2 ^ Nat.sqrt y : ℝ) / (y ^ C) * 2 ^ (2 * C) := by
          filter_upwards [Filter.eventually_gt_atTop 0] with y hy
          rw [div_mul_eq_mul_div, div_le_div_iff₀] <;> norm_cast <;> norm_num [pow_mul]
          · rw [mul_assoc, ← mul_pow]; gcongr; nlinarith [Nat.lt_succ_sqrt y]
          · positivity
          · positivity
        have h_subst3 : Filter.Tendsto
            (fun y : ℕ => (2 ^ Nat.sqrt y : ℝ) / (y ^ C) * 2 ^ (2 * C))
            Filter.atTop Filter.atTop := by
          rw [Filter.tendsto_atTop_atTop] at *
          intro b
          rcases ‹∀ b : ℝ, ∃ i : ℕ, ∀ a : ℕ, i ≤ a →
            b ≤ 2 ^ a.sqrt / (a.sqrt : ℝ) ^ (2 * C)› b with ⟨i, hi⟩
          rcases Filter.eventually_atTop.mp h_subst2 with ⟨j, hj⟩
          exact ⟨Max.max i j, fun n hn => le_trans (hi n (le_trans (le_max_left _ _) hn))
            (hj n (le_trans (le_max_right _ _) hn))⟩
        convert h_subst3.atTop_div_const
          (show (0 : ℝ) < 2 ^ (2 * C) by positivity) using 2
        norm_num [div_mul_eq_div_div]
      suffices h_log2 : Filter.Tendsto (fun w : ℝ => Real.exp w / w ^ (2 * C))
          Filter.atTop Filter.atTop by
        have h_subst4 : Filter.Tendsto
            (fun z : ℕ => Real.exp (z * Real.log 2) / (z * Real.log 2) ^ (2 * C))
            Filter.atTop Filter.atTop :=
          h_log2.comp <| tendsto_natCast_atTop_atTop.atTop_mul_const <| Real.log_pos one_lt_two
        convert h_subst4.const_mul_atTop
          (show 0 < (Real.log 2) ^ (2 * C) by positivity) using 2
        norm_num [Real.exp_nat_mul, Real.exp_log]
        ring_nf
        norm_num [mul_assoc, ne_of_gt, Real.log_pos]
      exact Real.tendsto_exp_div_pow_atTop _
    rw [Asymptotics.isBigO_iff] at hC
    contrapose! hC
    intro c; refine Filter.Eventually.frequently ?_
    filter_upwards [h_exp_growth.eventually_gt_atTop c, Filter.eventually_gt_atTop 1]
      with n hn hn'
    simp_all only [Nat.cast_mul, Nat.cast_pow, norm_mul, norm_natCast, norm_pow, Nat.cast_ofNat]
    rw [lt_div_iff₀ (by exact pow_pos (Nat.cast_pos.mpr <| Nat.log_pos one_lt_two hn') _)] at hn
    erw [Real.norm_of_nonneg] <;> norm_num
    nlinarith [(by norm_cast : (1 : ℝ) < n)]

theorem almostLinear_subset_poly : almostLinear ⊆ poly := by
  intro f hf
  use 2
  have := hf 1 zero_lt_one
  convert this using 1; norm_cast
  norm_num [Asymptotics.isBigO_iff]

attribute [refl] Asymptotics.isBigO_refl

theorem almostLinear_ssubset_poly : almostLinear ⊂ poly := by
  refine ⟨almostLinear_subset_poly, ?_⟩
  rw [Set.not_subset]
  refine ⟨fun n : ℕ => n ^ 2, ⟨2, Asymptotics.isBigO_refl ..⟩, ?_⟩
  norm_num [almostLinear]
  refine ⟨1 / 2, by simp, ?_⟩
  simp only [one_div, Asymptotics.isBigO_iff, norm_pow, RCLike.norm_natCast, Real.norm_eq_abs,
    Filter.eventually_atTop, not_exists, not_forall]
  intro x n
  rcases exists_nat_gt (x ^ 2) with ⟨m, hm⟩
  refine ⟨n + m + 1, ?_, ?_⟩
  · grind
  · rw [abs_of_nonneg (by positivity)]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show ((n : ℝ) + m + 1) ^ (1 + 2⁻¹ : ℝ) =
      ((n : ℝ) + m + 1) * Real.sqrt ((n : ℝ) + m + 1) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add'] <;> norm_num; positivity]
    nlinarith [sq_nonneg (x - Real.sqrt (n + m + 1)),
      Real.mul_self_sqrt (by positivity : 0 ≤ (n : ℝ) + m + 1),
      Real.sqrt_nonneg (n + m + 1),
      mul_self_nonneg (Real.sqrt (n + m + 1) - x),
      Real.mul_self_sqrt (by positivity : 0 ≤ (n : ℝ) + m + 1)]

theorem poly_subset_quasipoly : poly ⊆ quasipoly := by
  refine fun f ⟨c, hf⟩ ↦ ⟨c + 1, hf.trans ?_⟩
  simp only [Asymptotics.isBigO_iff, norm_pow, Int.norm_natCast, Filter.eventually_atTop]
  use 1, 2 ^ (c + 1)
  intro b hb
  erw [Real.norm_of_nonneg <| by positivity]
  have h : (b : ℝ) ^ c ≤ (2 : ℝ) ^ ((Nat.log 2 b) * (c + 1)) := by
    have h₁ : b ^ c ≤ 2 ^ ((Nat.log 2 b) * c) * 2 ^ c := by
      rw [pow_mul, ← mul_pow, ← pow_succ]
      exact_mod_cast Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self one_lt_two b).le c
    norm_cast
    rw [Nat.mul_succ, pow_add]
    refine h₁.trans <| Nat.mul_le_mul_left _ ?_
    refine pow_le_pow_right₀ one_le_two <| Nat.le_log_of_pow_le one_lt_two ?_
    linarith [pow_succ 2 c]
  apply h.trans
  rcases hk : Nat.log 2 b with (_ | k)
  · simp
  rcases c with (_ | c)
  · simp
  rw [one_mul]
  apply pow_le_pow_right₀ one_le_two
  norm_num [Nat.log_eq_iff, Nat.pow_succ, mul_comm (k + 1)] at *
  have h₂ : 1 < k + 1 := Nat.succ_lt_succ <| Nat.pos_of_ne_zero <| by
    rintro rfl
    linarith [c.lt_two_pow_self]
  nlinarith [c.lt_pow_self h₂, (2).lt_pow_self h₂]

theorem poly_ssubset_quasipoly : poly ⊂ quasipoly := by
  use poly_subset_quasipoly
  simp only [exists_and_right, Classical.not_imp, quasipoly, poly, Set.setOf_subset_setOf,
    forall_exists_index, not_forall, not_exists]
  use fun n ↦ 2 ^ (Nat.log 2 n) ^ 2
  use ⟨2, mod_cast Asymptotics.isBigO_refl ..⟩
  intro k hk
  rw [Asymptotics.isBigO_iff'] at hk
  simp only [Nat.cast_pow, Nat.cast_ofNat, norm_pow, norm_natCast, Filter.eventually_atTop] at hk
  rcases hk with ⟨c, hc₀, a, ha⟩
  -- Choose `b = 2^m` for some `m` large enough such that `2^(m^2) > c * (2^m)^k`.
  have ⟨m, hm⟩ : ∃ m : ℕ, m > a ∧ 2 ^ (m ^ 2) > c * (2 ^ m) ^ k := by
    -- We choose `m` large enough such that `2^(m^2) > c * 2^(mk)`
    have ⟨m, hm₁, hm₂⟩ : ∃ m : ℕ, m > a ∧ m^2 > m * k + Real.logb 2 c := by
      use a + k + ⌊Real.logb 2 c⌋₊ + 1, by linarith
      push_cast
      nlinarith [Nat.lt_floor_add_one (Real.logb 2 c)]
    use m
    rw [gt_iff_lt, Real.logb, add_div', div_lt_iff₀] at hm₂ <;> norm_num at *
    · use hm₁
      rw [← Real.log_lt_log_iff (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      norm_num
      linarith
    · positivity
  specialize ha (2 ^ m) (hm.1.le.trans m.lt_two_pow_self.le)
  norm_num [Norm.norm] at ha
  order

lemma polylog_is_littleO_sqrt {f : ℕ → ℕ} (hf : f ∈ polylog) :
    (fun n ↦ (f n : ℝ)) =o[.atTop] (√·) := by
  have h_log_poly : ∀ w : ℕ, (fun n ↦ (Nat.log 2 n : ℝ) ^ w) =o[.atTop] (√·) := by
    intro w
    have h_log : Filter.atTop.Tendsto (fun n ↦ (Real.log n / Real.log 2) ^ w / √n) (𝓝 0) := by
      suffices hs : Filter.Tendsto (fun n ↦ (Real.log n) ^ w / √n) .atTop (𝓝 0) by
        convert hs.div_const (Real.log 2 ^ w) using 2 <;> ring
      suffices h_log : Filter.Tendsto (fun y ↦ y ^ w / Real.exp (y / 2)) .atTop (𝓝 0) by
        have := h_log.comp (Real.tendsto_log_atTop)
        apply this.congr'
        filter_upwards [Filter.eventually_gt_atTop 0] with x hx
        rw [Function.comp_apply, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
        ring_nf
      suffices h_z : Filter.Tendsto (fun z ↦ (2 * z) ^ w / Real.exp z) .atTop (𝓝 0) by
        convert h_z.comp (Filter.tendsto_id.atTop_mul_const (by norm_num : 0 < (2⁻¹ : ℝ))) using 2
        norm_num
        ring_nf
      suffices h_factor : Filter.Tendsto (fun z ↦ z ^ w / Real.exp z) .atTop (𝓝 0) by
        convert h_factor.const_mul (2 ^ w) using 2 <;> ring
      simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero w
    rw [Asymptotics.isLittleO_iff_tendsto']
    · have h_log : Filter.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ w / √n) .atTop (𝓝 0) := by
        have : ∀ n : ℕ, n ≥ 2 → (Nat.log 2 n) ^ w / √n ≤ (Real.log n / Real.log 2) ^ w / √n := by
          intro n hn; gcongr
          rw [le_div_iff₀ (Real.log_pos (by norm_num)), ← Real.log_pow]
          exact Real.log_le_log (by positivity) (mod_cast Nat.pow_log_le_self _ (by positivity))
        refine squeeze_zero_norm' ?_ (h_log.comp tendsto_natCast_atTop_atTop)
        rw [Filter.eventually_atTop]
        use 2
        exact fun n ↦ by rw [Real.norm_of_nonneg (by positivity)]; exact this n
      convert h_log using 1
    · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' <| by positivity
  rcases hf with ⟨w, hw⟩
  have h_log_poly : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℝ) ^ w) := by
    rw [Asymptotics.isBigO_iff] at *
    aesop
  exact h_log_poly.trans_isLittleO (by aesop)

theorem quasipoly_subset_twoPow : quasipoly ⊆ twoPow := by
  rintro f ⟨C, hC⟩
  suffices h_exp :(fun n ↦ 2 ^ (Nat.log 2 n ^ C) : ℕ → ℤ) =O[.atTop] (fun n ↦ 2 ^ n : ℕ → ℤ) by
    simpa [twoPow, bigO] using hC.trans h_exp
  suffices h_exp : ∀ᶠ n in .atTop, (Nat.log 2 n ^ C : ℕ) ≤ n by
    rw [Asymptotics.isBigO_iff]
    norm_num +zetaDelta at *
    rcases h_exp with ⟨k, hk⟩
    refine ⟨1, k, fun n hn ↦ ?_⟩
    rw [one_mul]
    exact pow_le_pow_right₀ (by norm_num [Norm.norm]) (hk n hn)
  have h_log : Filter.atTop.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ C / n) (𝓝 0) := by
    -- We substitute `m = log₂ n`.
    suffices h_log : Filter.atTop.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ C / (2 ^ m : ℝ)) (𝓝 0) by
      have h_log : Filter.atTop.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / _) (𝓝 0) :=
        h_log.comp (Filter.tendsto_atTop_atTop.mpr <|
          (⟨2 ^ ·, fun n hn ↦ Nat.le_log_of_pow_le one_lt_two hn⟩))
      refine squeeze_zero_norm' ?_ h_log
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      norm_cast
      exact Nat.pow_log_le_self 2 hn.ne'
    -- We substitute `m = log₂ n` and use that `2^m` grows exponentially.
    suffices h_log : Filter.atTop.Tendsto (fun m : ℕ ↦ m ^ C / (m * Real.log 2).exp) (𝓝 0) by
      simpa [Real.exp_nat_mul, Real.exp_log] using h_log
    suffices h_log2 : Filter.atTop.Tendsto (fun y : ℝ ↦ y ^ C / Real.exp y) (𝓝 0) by
      have h := h_log2.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two))
      convert h.div_const (Real.log 2 ^ C) using 2 <;> ring_nf
      norm_num [Real.exp_ne_zero]
      exact eq_div_of_mul_eq (by positivity) (by ring_nf)
    simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C
  replace h_log := h_log.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [h_log, Filter.eventually_gt_atTop 0] with n hn hn'
  rw [div_lt_one (by positivity)] at hn
  exact_mod_cast hn.le


theorem quasipoly_ssubset_twoPow : quasipoly ⊂ twoPow := by
  use quasipoly_subset_twoPow
  simp only [quasipoly, bigO, twoPow, Nat.cast_pow, Nat.cast_ofNat, Set.setOf_subset_setOf,
    not_forall, exists_prop]
  use (2 ^ ·), mod_cast Asymptotics.isBigO_refl ..
  -- Assume for contradiction that there exists a constant `C` such that `2^n = O(2^((log n)^C))`.
  by_contra h_contra
  have ⟨C, hC⟩ := h_contra
  have h_exp : Filter.atTop.Tendsto (fun n ↦ (2 : ℝ) ^ (Nat.log 2 n ^ C) / 2 ^ n) (𝓝 0) := by
    -- We rewrite `2^((log n)^C) / 2^n = 2^((log n)^C - n)`.
    suffices h_exp : Filter.atTop.Tendsto (fun n ↦ (2 : ℝ) ^ ((Nat.log 2 n) ^ C - n : ℝ)) (𝓝 0) by
      convert h_exp using 2
      norm_num [Real.rpow_sub]
      norm_cast
    have h_log : Filter.atTop.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ C - n) Filter.atBot := by
      have h_log : Filter.atTop.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ C / n) (𝓝 0) := by
        -- We substitute `m = log₂ n`.
        suffices h_log : Filter.atTop.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ C / (2 ^ m)) (𝓝 0) by
          have h_log : Filter.atTop.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / _) (𝓝 0) :=
            h_log.comp (Filter.tendsto_atTop_atTop.mpr <|
              (⟨2 ^ ·, fun n hn ↦ Nat.le_log_of_pow_le one_lt_two hn⟩))
          refine squeeze_zero_norm' ?_ h_log
          filter_upwards [Filter.eventually_gt_atTop 0] with n hn
          rw [Real.norm_of_nonneg (by positivity)]
          gcongr
          norm_cast
          exact Nat.pow_log_le_self 2 hn.ne'
        -- We substitute `m = log₂ n` and use that `2^m` grows much faster than `m^C`.
        have h_log : Filter.atTop.Tendsto (fun m : ℕ ↦ m ^ C / (m * Real.log 2).exp) (𝓝 0) := by
          suffices h_log : Filter.atTop.Tendsto (fun y : ℝ ↦ y ^ C / y.exp) (𝓝 0) by
            have hs : Filter.atTop.Tendsto (fun m : ℕ ↦ (m * Real.log 2 : ℝ) ^ C / _) (𝓝 0) :=
              h_log.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two))
            convert hs.div_const (Real.log 2 ^ C) using 2
            · ring_nf
              norm_num [mul_right_comm, mul_assoc, mul_left_comm, ne_of_gt, Real.log_pos]
            · simp
          simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C
        simpa [Real.exp_nat_mul, Real.exp_log] using h_log
      -- We can rewrite the limit expression using the properties of limits.
      have h_rw : Filter.atTop.Tendsto (fun n ↦ ((Nat.log 2 n : ℝ) ^ C / n - 1) * n) .atBot := by
        apply Filter.Tendsto.neg_mul_atTop (C := -1)
        · norm_num
        · simpa using h_log.sub_const 1
        · exact tendsto_natCast_atTop_atTop
      apply h_rw.congr'
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [sub_mul, div_mul_cancel₀ _ (by positivity)]
      ring
    norm_num [Real.rpow_def_of_pos]
    exact Filter.Tendsto.const_mul_atBot (by positivity) h_log
  rw [Asymptotics.isBigO_iff] at hC
  simp only [Nat.cast_pow, Nat.cast_ofNat, norm_pow, Filter.eventually_atTop] at hC
  obtain ⟨c, a, hc⟩ := hC
  have h_div : ∀ b ≥ a, 1 ≤ c * (2 : ℝ) ^ (Nat.log 2 b ^ C) / (2 : ℝ) ^ b := by
    intro b hb
    specialize hc b hb
    rw [le_div_iff₀ (by positivity)]
    norm_num [Norm.norm] at hc ⊢
    omega
  refine absurd ?_ (show ¬1 ≤ c * 0 by norm_num)
  refine le_of_tendsto_of_tendsto tendsto_const_nhds (h_exp.const_mul c) ?_
  rw [Filter.EventuallyLE, Filter.eventually_atTop]
  exact ⟨a, (by simpa [mul_div_assoc] using h_div · ·)⟩

theorem twoPow_subset_ePow : twoPow ⊆ ePow := by
  -- `2^n ≤ e^n` since `2 < e`.
  have h_exp_bound : ∀ n : ℕ, 2 ^ n ≤ Real.exp n := by
    intro n
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos] <;> norm_num
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (Real.log_two_lt_d9.le.trans (by norm_num))
  have h_twoPow_ePow : (2 ^ · : ℕ → ℕ) ∈ bigO (fun n ↦ ⌈Real.exp n⌉₊ : ℕ → ℕ) := by
    apply Asymptotics.isBigO_iff.mpr
    use 1
    refine Filter.eventually_atTop.mpr ⟨0, fun n hn ↦ ?_⟩
    erw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast Nat.le_of_lt_succ <| by
      rw [← @Nat.cast_lt ℝ]
      push_cast
      linarith [Nat.le_ceil (Real.exp n), h_exp_bound n]
  convert h_twoPow_ePow using 1
  constructor <;> intro h <;> unfold twoPow ePow at *
  · aesop
  · exact fun f hf ↦ hf.trans h

theorem twoPow_ssubset_ePow : twoPow ⊂ ePow := by
  use twoPow_subset_ePow
  simp only [ePow, bigO, twoPow, Nat.cast_pow, Nat.cast_ofNat, Set.setOf_subset_setOf, not_forall,
    exists_prop]
  use (⌈Real.exp ·⌉₊), Asymptotics.isBigO_refl ..
  rw [Asymptotics.isBigO_iff']
  norm_num [Norm.norm]
  have h_exp : Filter.Tendsto (fun n : ℕ ↦ (Real.exp n : ℝ) / 2 ^ n) .atTop .atTop := by
    suffices h : Filter.Tendsto (fun n : ℕ ↦ (Real.exp 1 / 2 : ℝ) ^ n) .atTop .atTop by
      simpa [Real.exp_nat_mul, div_pow] using h
    exact tendsto_pow_atTop_atTop_of_one_lt <| by linarith [Real.exp_one_gt_two]
  intro x hx n
  replace h_exp := h_exp.eventually_gt_atTop (x + 1)
  replace h_exp := (Filter.eventually_ge_atTop n).and h_exp
  have ⟨m, hm⟩ := Filter.eventually_atTop.mp h_exp
  specialize hm m le_rfl
  refine ⟨m, hm.1, ?_⟩
  have hm₁ := hm.2
  rw [lt_div_iff₀ (by positivity)] at hm₁
  nlinarith [Nat.le_ceil (Real.exp m), show (2 : ℝ) ^ m > 0 by positivity]

theorem ePow_subset_exp : ePow ⊆ exp := by
  refine fun f h ↦ ⟨⌈Real.exp 1⌉₊, h.trans (Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩)⟩
  have h_exp_growth (x : ℕ) : Real.exp x ≤ ⌈Real.exp 1⌉₊ ^ x := by
    simpa using pow_le_pow_left₀ (by positivity) (Nat.le_ceil (Real.exp 1)) x
  simp only [Int.norm_natCast, Filter.eventually_atTop]
  use 1
  intros
  erw [Real.norm_of_nonneg (by positivity)]
  exact_mod_cast le_trans (Nat.ceil_mono <| h_exp_growth _) (by norm_num)

theorem ePow_ssubset_exp : ePow ⊂ exp := by
  use ePow_subset_exp
  rw [Set.not_subset]
  use (3 ^ ·), ⟨3, by simpa using Asymptotics.isBigO_refl ..⟩
  simp only [ePow, bigO, Set.mem_setOf_eq, Nat.cast_pow, Nat.cast_ofNat]
  intro h
  rw [Asymptotics.isBigO_iff'] at h
  contrapose h
  simp_rw [not_exists, not_and]
  intro c _
  have h_exp : Filter.Tendsto (fun x : ℕ ↦ (3 ^ x : ℝ) / ⌈(Real.exp x)⌉₊) .atTop .atTop := by
    have h_exp_approx : ∀ n : ℕ, (3 ^ n : ℝ) / ⌈(Real.exp n)⌉₊ ≥ (3 / Real.exp 1) ^ n / 2 := by
      intro n
      rw [div_pow, Real.exp_one_pow, div_div, ge_iff_le,
        div_le_div_iff₀ (by positivity) (by positivity)]
      grw [Nat.ceil_lt_add_one (by positivity),
        ← show Real.exp ↑n + 1 ≤ Real.exp ↑n * 2 by linarith [Real.add_one_le_exp n]]
    refine Filter.tendsto_atTop_mono h_exp_approx ?_
    refine Filter.Tendsto.atTop_div_const (by positivity) (tendsto_pow_atTop_atTop_of_one_lt ?_)
    rw [one_lt_div (by positivity)]
    exact Real.exp_one_lt_d9.trans_le <| by norm_num
  replace h_exp := h_exp.eventually_gt_atTop c
  simp only [Filter.eventually_atTop, Int.norm_natCast, not_exists, not_forall,
    not_le, exists_prop] at h_exp ⊢
  intro x
  rcases h_exp with ⟨w, h⟩
  refine ⟨_, Nat.le_add_left x w, ?_⟩
  erw [Real.norm_of_nonneg (by positivity)]
  specialize h (w + x) (by linarith)
  rw [lt_div_iff₀ (by positivity)] at h
  exact_mod_cast h

theorem exp_subset_primitiveRecursive : exp ⊆ primitiveRecursive := by
  rintro f ⟨k, hk⟩
  norm_cast at hk
  refine ⟨_, ?_, hk⟩
  simpa using Nat.Primrec.pow.comp (.pair (.const k) .id)

/-- The factorial function is not in `exp`. -/
theorem factorial_not_mem_exp : Nat.factorial ∉ exp := by
  rintro ⟨c, hc⟩
  rw [Asymptotics.isBigO_iff] at hc
  contrapose hc
  simp_rw [not_exists]
  simp only [Filter.eventually_atTop, not_exists, not_forall]
  intro y z
  -- We'll use the exponential property: the factorial grows faster than any exponential function.
  have hf_growth : Filter.Tendsto (fun n ↦ (y * (c ^ n) : ℝ) / n.factorial) .atTop (𝓝 0) := by
    have h := FloorSemiring.tendsto_pow_div_factorial_atTop (c : ℝ)
    simpa [mul_div_assoc] using h.const_mul y
  have ⟨w, h⟩ := Filter.eventually_atTop.mp <| hf_growth.eventually (gt_mem_nhds zero_lt_one)
  refine ⟨_, le_max_left z w, ?_⟩
  specialize h _ (le_max_right z w)
  rw [div_lt_one (by positivity)] at h
  simpa using h

--PR'ed in https://github.com/leanprover-community/mathlib4/pull/33864
/-- The factorial function is primitve recursive. -/
@[nolint topNamespace]
theorem _root_.Primrec.factorial : Primrec Nat.factorial := by
  convert Primrec.list_foldl (σ := ℕ) (h := fun n ⟨p, k⟩ ↦ p * (k + 1))
    Primrec.list_range (Primrec.const 1) ?_
  · rw [← Finset.prod_range_add_one_eq_factorial, ← List.foldl_map, ← List.prod_eq_foldl]
    rw [← List.prod_toFinset _ List.nodup_range, ← List.toFinset_range]
  · refine Primrec.comp₂ ?_ .right
    exact Primrec.nat_mul.comp₂ .left (Primrec.succ.comp₂ .right)

theorem exp_ssubset_primitiveRecursive : exp ⊂ primitiveRecursive := by
  use exp_subset_primitiveRecursive
  rw [Set.not_subset]
  use Nat.factorial
  constructor
  · use Nat.factorial
    rw [← Primrec.nat_iff]
    exact ⟨Primrec.factorial, Asymptotics.isBigO_refl ..⟩
  · exact factorial_not_mem_exp

theorem primitiveRecursive_subset_computable : primitiveRecursive ⊆ computable := by
  rintro f ⟨g, hg⟩
  rw [← Primrec.nat_iff] at hg
  exact ⟨g, hg.left.to_comp, hg.right⟩

theorem primitiveRecursive_ssubset_computable : primitiveRecursive ⊂ computable := by
  use primitiveRecursive_subset_computable
  rw [Set.not_subset]
  use (fun x ↦ ack x x)
  simp only [primitiveRecursive, bigO, Set.mem_setOf_eq, not_exists, not_and]
  constructor
  · use fun x ↦ ack x x
    constructor
    · exact Computable.comp computable₂_ack (Computable.id.pair Computable.id)
    · exact Asymptotics.isBigO_refl ..
  · intro x hx
    rw [Asymptotics.isBigO_iff']
    -- Since ack n n grows faster than any primrec, for any constant c,
    -- there exists an n such that ack n n > c * x n.
    have h_ineq : ∀ c > 0, ∃ N, ∀ n ≥ N, ack n n > c * x n := by
      intro c hc_pos
      -- There exists an m such that ack(m, n) > c * x(n) for all n.
      obtain ⟨m, hm⟩ : ∃ m, ∀ n, ack m n > c * x n := by
        apply exists_lt_ack_of_nat_primrec
        suffices h_poly : Nat.Primrec (fun n ↦ c * n) by
          exact h_poly.comp hx
        convert Nat.Primrec.mul.comp ((Nat.Primrec.const c).pair Nat.Primrec.id) using 2
        norm_num [Nat.unpaired]
      exact ⟨m, fun n hn ↦ by simpa using (hm n).trans_le (ack_le_ack hn le_rfl)⟩
    simp only [norm_natCast, Filter.eventually_atTop, not_exists, not_and, not_forall, not_le]
    intro c hc n
    obtain ⟨N, hN⟩ := h_ineq (⌈c⌉₊) (Nat.ceil_pos.mpr hc)
    use n + N, by omega
    grw [Nat.le_ceil c]
    exact_mod_cast hN _ (by omega)

end GrowthRate

end CSLib
