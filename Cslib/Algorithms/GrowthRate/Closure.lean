
/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

module

public import Cslib.Algorithms.GrowthRate.Special

/-!
# Named Growth Rates

-/

@[expose] public section

namespace CSLib

open scoped Topology

namespace GrowthRate
section closure_mul

variable {f g : ℕ → ℕ}

theorem polylog_mul (hf : f ∈ polylog) (hg : g ∈ polylog) : f * g ∈ polylog := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add]

theorem linear_of_sqrt_mul_sqrt (hf : f ∈ sqrt) (hg : g ∈ sqrt) : f * g ∈ linear := by
  convert (hf.mul hg).trans ?_
  rw [Asymptotics.isBigO_iff']
  simp only [norm_mul, norm_natCast, id_eq, Filter.eventually_atTop]
  exact ⟨1, by norm_num, 0, fun b hb ↦ by
    norm_cast; nlinarith [Nat.sqrt_le b]⟩

/-- The product of two square-root growth rates is linear. -/
@[simp]
theorem sqrt_mul_sqrt : sqrt * sqrt = linear := by
  apply le_antisymm
  · intro h
    rintro ⟨f, hf, g, hg, hle⟩
    exact Asymptotics.IsBigO.trans
      (show (fun n => (h n : ℤ)) =O[Filter.atTop] (fun n => (f n * g n : ℤ)) from
        Asymptotics.IsBigO.of_bound 1 <| Filter.Eventually.of_forall fun n => by
          simpa using mod_cast hle n)
      (linear_of_sqrt_mul_sqrt hf hg)
  · intro h hh
    simp only [GrowthRate.mem_mul]
    obtain ⟨C₀, N, hC⟩ : ∃ C₀ N, ∀ n ≥ N, h n ≤ C₀ * n := by
      obtain ⟨C₀, hC⟩ := hh.exists_nonneg
      simp only [Asymptotics.IsBigOWith, id_eq, norm_natCast, Filter.eventually_atTop] at hC
      exact ⟨⌈C₀⌉₊, hC.2.choose, fun n hn => by
        have := hC.2.choose_spec n hn
        exact_mod_cast this.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))⟩
    refine ⟨fun n => (C₀ + ∑ n ∈ Finset.range N, h n) * (Nat.sqrt n + 1), ?_,
            fun n => Nat.sqrt n + 1, ?_, ?_⟩
    · -- First factor is O(sqrt)
      refine Asymptotics.IsBigO.of_bound ((C₀ + ∑ n ∈ Finset.range N, h n) * 2) ?_
      simp only [norm_natCast, Filter.eventually_atTop]
      exact ⟨4, fun n hn => by
        simp
        nlinarith [show (n.sqrt : ℝ) ≥ 2 by exact_mod_cast Nat.le_sqrt.2 (by linarith),
          show (∑ x ∈ Finset.range N, (h x : ℝ)) ≥ 0 from
            Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _]⟩
    · -- Second factor is O(sqrt)
      refine Asymptotics.IsBigO.of_bound 2 ?_
      simp only [norm_natCast, Filter.eventually_atTop]
      exact ⟨1, fun n hn => by
        norm_cast
        linarith [Nat.sqrt_pos.2 hn]⟩
    · -- Pointwise bound
      intro n
      by_cases hn : n < N
      · simp only [Pi.mul_apply]
        nlinarith [Nat.zero_le (∑ n ∈ Finset.range N, h n),
          Finset.single_le_sum (fun a _ => Nat.zero_le (h a)) (Finset.mem_range.mpr hn),
          Nat.zero_le (Nat.sqrt n), Nat.zero_le (Nat.sqrt n * Nat.sqrt n)]
      · simp only [Pi.mul_apply]
        nlinarith [hC n (not_lt.mp hn), Nat.lt_succ_sqrt n,
          show ∑ n ∈ Finset.range N, h n ≥ 0 from Nat.zero_le _]

/-- The product of two polynomial growth rates is polynomial. -/
@[simp]
theorem poly_mul_poly : poly * poly = poly := by
  refine Set.Subset.antisymm ?_ ?_
  · intro h
    rintro ⟨f, hf, g, hg, hfg⟩
    obtain ⟨A, hA⟩ := hf
    obtain ⟨B, hB⟩ := hg
    have hfg_poly : (fun x => (f x * g x : ℤ)) =O[Filter.atTop] (fun x => (x : ℤ) ^ (A + B)) := by
      simpa only [pow_add] using hA.mul hB
    refine ⟨A + B, ?_⟩
    refine Asymptotics.IsBigO.trans ?_ hfg_poly
    exact Asymptotics.IsBigO.of_bound 1
      (Filter.eventually_atTop.mpr ⟨1, fun x _ => by simpa using mod_cast hfg x⟩)
  · intro f hf
    exact ⟨f, hf, 1, ⟨0, by norm_num [Asymptotics.isBigO_refl]⟩, fun n => by simp⟩

/-! ### Characterizations via operations -/

/-- `polylog` is `O(log n)^O(1)`. -/
theorem polylog_eq_log_pow_const : polylog = log ^ const := by
  apply Set.eq_of_subset_of_subset
  · intro h
    rintro ⟨C₀, hC⟩
    obtain ⟨D, N, hD⟩ : ∃ D N, ∀ n ≥ N, h n ≤ D * (Nat.log 2 n) ^ C₀ := by
      rw [Asymptotics.isBigO_iff'] at hC
      simp only [norm_natCast, Filter.eventually_atTop] at hC
      exact ⟨⌈hC.choose⌉₊, hC.choose_spec.2.choose, fun n hn => by
        exact_mod_cast le_trans (hC.choose_spec.2.choose_spec n hn)
          (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))⟩
    obtain ⟨M, hM⟩ : ∃ M, ∀ n < N, h n ≤ M :=
      ⟨Finset.sup (Finset.range N) h, fun n hn =>
        Finset.le_sup (f := h) (Finset.mem_range.mpr hn)⟩
    refine ⟨fun n => D + M + 1 + Nat.log 2 n, ?_,
            fun _ => C₀ + 1, ?_, ?_⟩
    · -- First factor is O(log)
      refine Asymptotics.IsBigO.of_bound (D + M + 1 + 1) ?_
      simp only [norm_natCast, Filter.eventually_atTop]
      exact ⟨2, fun n hn => by
        simp
        norm_cast
        nlinarith [Nat.log_pos one_lt_two hn]⟩
    · -- Second factor is in const
      simp only [const, bigO, Pi.one_apply, Nat.cast_one, Set.mem_setOf_eq]
      simp only [Nat.cast_add, Nat.cast_one, Asymptotics.isBigO_one_iff]
      use C₀ + 1
      refine Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
      grind only [Set.mem_setOf_eq, Int.norm_natCast (C₀ + 1)]
    · -- Pointwise bound
      intro n
      by_cases hn : n < N
      · simp only [pow_succ']
        nlinarith [hM n hn, pow_pos (show 0 < D + M + 1 + Nat.log 2 n by linarith) C₀]
      · refine le_trans (hD n (not_lt.mp hn)) ?_
        simp only [pow_succ']
        exact Nat.mul_le_mul (by linarith) (Nat.pow_le_pow_left (by linarith) _)
  · rintro _ ⟨f, hf, g, hg, hfg⟩
    obtain ⟨C₀, hC⟩ : ∃ C₀, ∀ n, g n ≤ C₀ := bounded_of_const hg
    obtain ⟨D, N_val, hN⟩ : ∃ D N, ∀ n ≥ N, f n ≤ D * Nat.log 2 n := by
      obtain ⟨D, hD⟩ := hf.exists_nonneg
      rw [Asymptotics.IsBigOWith] at hD
      simp only [norm_natCast, Filter.eventually_atTop] at hD
      exact ⟨⌈D⌉₊, hD.2.choose, fun n hn => by
        exact_mod_cast le_trans (hD.2.choose_spec n hn)
          (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))⟩
    use C₀ + 1
    simp only [Asymptotics.isBigO_iff, norm_natCast, Filter.eventually_atTop]
    refine ⟨(D + 1) ^ (C₀ + 1), N_val + 2, fun n hn => ?_⟩
    norm_cast
    simp only [pow_succ'] at *
    refine le_trans (hfg n) ?_
    refine le_trans (Nat.pow_le_pow_left (hN n (by linarith)) _) ?_
    refine le_trans (Nat.pow_le_pow_left
      (show D * Nat.log 2 n ≤ (D + 1) * Nat.log 2 n by nlinarith) _) ?_
    refine le_trans (Nat.pow_le_pow_right
      (Nat.mul_pos (Nat.succ_pos _) (Nat.log_pos one_lt_two (by linarith))) (hC n)) ?_
    ring_nf
    simp only [add_comm, mul_comm, mul_left_comm]
    exact le_add_of_le_of_nonneg
      (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.log_pos one_lt_two (by linarith))))
      (Nat.zero_le _)

/-- nearLinear growth is the same as linear times polylogarithmic. -/
theorem nearLinear_eq_linear_mul_polylog : nearLinear = linear * polylog := by
  apply Set.eq_of_subset_of_subset
  · intro h hh
    obtain ⟨C₀, D, N, hD⟩ : ∃ C₀ D N, ∀ n ≥ N, h n ≤ D * n * (Nat.log 2 n) ^ C₀ := by
      obtain ⟨C₀, hC⟩ := hh
      rw [Asymptotics.isBigO_iff] at hC
      simp only [norm_natCast, Filter.eventually_atTop] at hC
      obtain ⟨c, N, hC⟩ := hC
      exact ⟨C₀, ⌈c⌉₊, N, fun n hn => by
        have := hC n hn
        rw [← @Nat.cast_le ℝ]
        push_cast
        have := Nat.le_ceil c
        have : (n : ℝ) * Nat.log 2 n ^ C₀ ≥ 0 := by positivity
        simp at *
        nlinarith⟩
    obtain ⟨M, hM⟩ : ∃ M, ∀ n < N, h n ≤ M :=
      ⟨Finset.sup (Finset.range N) h, fun n hn =>
        Finset.le_sup (f := h) (Finset.mem_range.mpr hn)⟩
    refine ⟨fun n => (D + M + 1) * (n + 1), ?_,
            fun n => (Nat.log 2 n) ^ C₀ + 1, ?_, ?_⟩
    · -- First factor is O(id), hence in linear
      refine Asymptotics.IsBigO.of_bound (D + M + 1 + 1) ?_
      simp only [norm_natCast, id_eq, Filter.eventually_atTop]
      exact ⟨D + M + 2, fun n hn => by norm_cast; nlinarith⟩
    · -- Second factor is in polylog
      refine ⟨C₀, ?_⟩
      simp only [Asymptotics.isBigO_iff, norm_natCast, Filter.eventually_atTop]
      refine ⟨2, 2, fun n hn => ?_⟩
      norm_cast
      nlinarith [pow_pos (show 0 < Nat.log 2 n from Nat.log_pos one_lt_two hn) C₀]
    · -- Pointwise bound
      intro n
      by_cases hn : n < N
      · simp only [Pi.mul_apply, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm]
        have := hM n hn
        omega
      · simp only [Pi.mul_apply, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm]
        have := hD n (not_lt.mp hn)
        grind
  · rintro h ⟨f, hf, g, hg, hfg⟩
    obtain ⟨C₀, hC⟩ := hg
    use C₀
    refine Asymptotics.IsBigO.trans ?_ (Asymptotics.IsBigO.mul hf hC)
    exact Asymptotics.isBigO_iff.mpr
      ⟨1, Filter.eventually_atTop.mpr ⟨0, fun n _ => by simpa using mod_cast hfg n⟩⟩

/-- `linearithmic` is `O(n) * O(log n)`. -/
theorem linearithmic_eq_linear_mul_log : linearithmic = linear * log := by
  apply Set.eq_of_subset_of_subset;
  · intro f hf
    obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * n * Nat.log 2 n := by
      obtain ⟨C, hC₁, hC₂⟩ := hf.exists_pos;
      simp only [Asymptotics.IsBigOWith, norm_natCast, Filter.eventually_atTop] at hC₂ ⊢
      refine ⟨⌈C⌉₊, hC₂.choose, fun n hn ↦ ?_⟩
      rw [mul_assoc]
      exact_mod_cast (hC₂.choose_spec n hn).trans
        (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
    refine ⟨fun n => C * n + ∑ i ∈ Finset.range (N + 1), f i + 1, ?_,
            fun n => Nat.log 2 n + 1, ?_, ?_⟩
    · simp only [linear, bigO, id_eq, Asymptotics.isBigO_iff, norm_natCast,
        Filter.eventually_atTop, ge_iff_le, Set.mem_setOf_eq, Nat.cast_add, Nat.cast_mul,
        Nat.cast_sum, Nat.cast_one] ;
      refine ⟨C + ∑ x ∈ Finset.range (N + 1), f x + 1, 1, fun n hn ↦ ?_⟩
      norm_cast
      nlinarith [Nat.zero_le (∑ x ∈ Finset.range (N + 1), f x)]
    · apply Asymptotics.IsBigO.of_bound 2
      simp only [Nat.cast_add, Nat.cast_one, norm_natCast, Filter.eventually_atTop]
      refine ⟨2, fun n hn ↦ ?_⟩
      erw [Real.norm_of_nonneg (by positivity)]
      norm_cast
      grind only [Nat.log_pos one_lt_two hn]
    · intro n
      by_cases hn : n < N <;> simp_all [mul_add, add_assoc]
      · nlinarith [Finset.single_le_sum (fun i _ ↦ Nat.zero_le (f i))
          (Finset.mem_range.mpr (by lia : n < N + 1)),
          Nat.zero_le (C * n)]
      · grind
  · intro h ⟨f, hf, g, hg, hh'⟩
    refine .trans ?_ (hf.mul hg)
    rw [Asymptotics.isBigO_iff]
    exact ⟨1, Filter.eventually_atTop.mpr ⟨0, fun n _ ↦ by simpa using mod_cast hh' n⟩⟩

/-- `nearLinear` is `O(n) * O(log n)^O(1)`. -/
theorem nearLinear_eq_linear_mul_log_pow : nearLinear = linear * log ^ const := by
  rw [nearLinear_eq_linear_mul_polylog, polylog_eq_log_pow_const]

theorem linearithmic_of_linear_mul (hf : f ∈ linear) (hg : g ∈ log) : f * g ∈ linearithmic :=
  hf.mul hg

theorem nearLinear_mul_polylog (hf : f ∈ nearLinear) (hg : g ∈ polylog) :
    f * g ∈ nearLinear := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add, mul_assoc]

theorem poly_mul (hf : f ∈ poly) (hg : g ∈ poly) : f * g ∈ poly := by
  rw [← poly_mul_poly]
  exact mul_congr hf hg

theorem quasipoly_mul (hf : f ∈ quasipoly) (hg : g ∈ quasipoly) : f * g ∈ quasipoly := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  simp only [quasipoly, Set.mem_setOf_eq, Pi.mul_apply, Nat.cast_mul]
  use a + b
  convert (ha.mul hb).trans ?_
  norm_num [Asymptotics.isBigO_iff, Norm.norm]
  use 2, 2, fun k hk ↦ ?_
  have hl := Nat.log_pos one_lt_two hk
  rw [← pow_succ', Nat.pow_add, ← pow_add]
  apply pow_le_pow_right₀ one_le_two
  nlinarith [pow_pos hl a, pow_pos hl b]

theorem quasipoly_eq_const_pow_polylog : quasipoly = const ^ polylog := by
  apply Set.eq_of_subset_of_subset;
  · intro f hf
    obtain ⟨C, hC⟩ := hf;
    -- Choose $g$ to be the constant function $2D + M$.
    obtain ⟨D, M, hD⟩ : ∃ D M : ℕ, ∀ n, f n ≤ D * 2 ^ (Nat.log 2 n ^ C) + M := by
      rw [ Asymptotics.isBigO_iff ] at hC;
      norm_num [ Norm.norm ] at hC;
      obtain ⟨ c, a, hC ⟩ := hC;
      use Nat.ceil c, Finset.sup (Finset.range (a + 1)) (fun n => f n);
      intro n; by_cases hn : a ≤ n
      · exact le_add_of_le_of_nonneg ( Nat.le_of_lt_succ <| by {
          rw [ ← @Nat.cast_lt ℝ ]
          push_cast
          nlinarith [ Nat.le_ceil c, hC n hn, show ( 2:ℝ ) ^ Nat.log 2 n ^ C ≥ 1 from
            one_le_pow₀ ( by norm_num ) ] } ) ( Nat.zero_le _ )
      · exact le_add_of_nonneg_of_le (Nat.zero_le _) (Finset.le_sup (f := fun n ↦ f n)
          (Finset.mem_range.mpr (by linarith)))
    -- Choose $g$ to be the function $(Nat.log 2 n)^C + 1$.
    refine ⟨_, const_mem_const (2 * D + M), fun n => (Nat.log 2 n) ^ C + 1, ?_, ?_⟩
    · use C + 1
      simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, Asymptotics.isBigO_iff, norm_pow,
        norm_natCast, Filter.eventually_atTop, ge_iff_le]
      refine ⟨2, 2, fun n hn ↦ ?_⟩
      norm_num [Norm.norm]
      norm_cast
      ring_nf
      nlinarith [Nat.pow_le_pow_right (Nat.log_pos one_lt_two hn) (show 0 ≤ C by norm_num),
        Nat.log_pos one_lt_two hn]
    intro n
    specialize hD n
    rcases eq_or_ne D 0 with rfl | hD <;> rcases eq_or_ne M 0 with rfl | hM0
    · simp_all [ pow_succ' ]
    · simp only [mul_zero, zero_add, pow_succ', zero_mul] at hD ⊢
      exact hD.trans (Nat.le_mul_of_pos_right _ (by positivity))
    · simp only [add_zero, pow_succ']
      have _ : 2 ^ Nat.log 2 n ^ C ≤ (2 * D) ^ Nat.log 2 n ^ C := by gcongr; lia
      nlinarith
    · simp [pow_succ']
      nlinarith [pow_pos (show 0 < 2 by decide) (Nat.log 2 n ^ C),
        pow_le_pow_left' (show 2 * D + M ≥ 2 by lia) (Nat.log 2 n ^ C)]
  · intro h hh
    rw [mem_pow] at hh
    rcases hh with ⟨f, hf, g, hg, hh⟩
    simp only [quasipoly, Set.mem_setOf_eq]
    obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ n in Filter.atTop, g n ≤ (Nat.log 2 n) ^ C := by
      obtain ⟨C, hC⟩ := hg
      simp only [Nat.cast_pow, Asymptotics.isBigO_iff, norm, Int.cast_natCast, Nat.abs_cast,
        Int.cast_pow, abs_pow, Filter.eventually_atTop] at hC
      obtain ⟨c, a, hc⟩ := hC
      use C + 1
      -- Since $c$ is a constant, we can choose $N$ such that for all $n \geq N$, $c \leq \log_2 n$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, c ≤ Nat.log 2 n := by
        exact ⟨2 ^ ⌈c⌉₊, fun n hn ↦ (Nat.le_ceil _).trans
          (mod_cast Nat.le_log_of_pow_le one_lt_two hn)⟩
      filter_upwards [Filter.eventually_ge_atTop a, Filter.eventually_ge_atTop N] with n hn hn'
      have := hc n hn
      rw [← @Nat.cast_le ℝ]
      push_cast
      apply this.trans
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_right (hN n hn') (by positivity)
    obtain ⟨D, hD⟩ := bounded_of_const hf;
    -- Since $D$ is a constant, $D^{g(n)}$ is $O(2^{(\log_2 n)^{C+1}})$.
    have h_exp : ∃ C', ∀ᶠ n in Filter.atTop, (D : ℝ) ^ (g n) ≤ (2 : ℝ) ^ ((Nat.log 2 n) ^ C') := by
      have h_exp : ∃ C', ∀ᶠ n in Filter.atTop, (D : ℝ) ^ (g n) ≤
          (2 : ℝ) ^ ((Nat.log 2 n) ^ C' * (Nat.log 2 D + 1)) := by
        use C + 1
        filter_upwards [ hC, Filter.eventually_ge_atTop 2 ] with n hn hn'
        refine (pow_le_pow_left₀ (by positivity) (show (D : ℝ) ≤ 2 ^ (Nat.log 2 D + 1) from mod_cast
            (Nat.lt_pow_succ_log_self (by decide) _).le) _).trans ?_
        rw [ ← pow_mul ];
        apply pow_le_pow_right₀ (by norm_num)
        rw [mul_comm]
        exact Nat.mul_le_mul
          (hn.trans (Nat.pow_le_pow_right (Nat.log_pos one_lt_two hn') (Nat.le_succ _))) le_rfl
      obtain ⟨ C', hC' ⟩ := h_exp;
      use C' + 1;
      filter_upwards [ hC', Filter.eventually_gt_atTop ( 2 ^ ( Nat.log 2 D + 1 ) ) ] with n hn hn';
      refine le_trans hn ?_;
      gcongr <;> norm_num;
      rw [ pow_succ ] ; gcongr;
      exact Nat.le_log_of_pow_le ( by norm_num ) hn'.le;
    rcases h_exp with ⟨C', hC'⟩
    use C'
    rw [Asymptotics.isBigO_iff]
    simp only [Filter.eventually_atTop, ge_iff_le, norm_natCast, norm_pow] at hC' ⊢
    obtain ⟨a, ha⟩ := hC'
    use 1; use a
    intro n hn
    specialize hh n
    specialize ha n hn
    norm_num at *
    have h_pow : (↑(f n ^ g n : ℕ) : ℝ) ≤ D ^ g n := mod_cast Nat.pow_le_pow_left (hD n) _
    exact (Nat.cast_le.mpr hh) |>.trans (h_pow.trans ha) |>.trans (by simp [Norm.norm])

theorem ePow_of_twoPow_mul_quasipoly (hf : f ∈ twoPow) (hg : g ∈ quasipoly) : f * g ∈ ePow := by
  simp only [twoPow, bigO, Nat.cast_pow, Nat.cast_ofNat, Set.mem_setOf_eq, quasipoly, ePow,
    Pi.mul_apply, Nat.cast_mul] at *
  simp only [Asymptotics.isBigO_iff', norm_natCast, norm_pow, Filter.eventually_atTop] at hf hg
  simp only [Asymptotics.isBigO_iff, norm_mul, norm_natCast, Filter.eventually_atTop]
  obtain ⟨c₁, hc₁, k₁, h₁⟩ := hf
  obtain ⟨C, c₂, hc₂, k₂, h₂⟩ := hg
  use c₁
  suffices hs : ∃ k, ∀ b ≥ k, (2 ^ b) * (c₂ * 2 ^ Nat.log 2 b ^ C) ≤ ⌈Real.exp b⌉₊ by
    rcases hs with ⟨k, hk⟩
    use k ⊔ k₁ ⊔ k₂
    intro b hb
    specialize h₁ b ((le_max_right _ _).trans <| (le_max_left _ _).trans hb)
    specialize h₂ b ((le_max_right _ _).trans hb)
    specialize hk b ((le_max_left _ _).trans <| (le_max_left _ _).trans hb)
    simp only [norm, Int.cast_ofNat, Nat.abs_ofNat] at h₁ h₂
    trans (c₁ * 2 ^ b) * (c₂ * 2 ^ Nat.log 2 b ^ C)
    · gcongr
    · rw [mul_assoc]
      gcongr
  clear c₁ hc₁ k₁ h₁ k₂ h₂
  -- Simplifying the goal using properties of exponential functions and logs
  suffices h_exp_log : ∃ k : ℕ, ∀ b ≥ k, c₂ * 2 ^ (b + Nat.log 2 b ^ C) ≤ Nat.ceil (Real.exp b) by
    simpa only [mul_assoc, mul_comm, mul_left_comm, pow_add] using h_exp_log
  suffices h_exp_log : ∃ k : ℕ, ∀ b ≥ k, c₂ * 2 ^ (b + Nat.log 2 b ^ C) ≤ Real.exp b by
    exact ⟨h_exp_log.choose, fun n hn ↦ by
      simpa only [pow_add, mul_assoc] using (h_exp_log.choose_spec n hn).trans (Nat.le_ceil _)⟩
  -- By dividing both sides of the inequality by `2^b`, we reduce to showing
  -- `c₂ * 2 ^ ((log₂ b) ^ C) ≤ exp(b * (1 - log 2))`.
  suffices h₂ : ∃ k : ℕ, ∀ b ≥ k, c₂ * 2 ^ (Nat.log 2 b ^ C) ≤ Real.exp (b * (1 - Real.log 2)) by
    refine h₂.imp (fun k hk b hb ↦ ?_)
    rw [pow_add, ← mul_comm]
    specialize hk b hb
    convert mul_le_mul_of_nonneg_left hk <| pow_nonneg zero_le_two b using 1
    · ring
    · rw [mul_sub, mul_one, Real.exp_sub]
      norm_num [Real.exp_neg, Real.exp_nat_mul, Real.exp_log, mul_div_cancel₀]
  suffices h_exp_poly : Filter.atTop.Tendsto (fun b : ℕ ↦
      (2 ^ (Nat.log 2 b ^ C) : ℝ) / Real.exp (b * (1 - Real.log 2))) (𝓝 0) by
    have := h_exp_poly.eventually (gt_mem_nhds <| show 0 < c₂⁻¹ by positivity)
    rw [Filter.eventually_atTop] at this
    peel this with _ n _ this
    rw [div_lt_iff₀ (Real.exp_pos _)] at this
    nlinarith [Real.exp_pos (n * (1 - Real.log 2)), inv_mul_cancel₀ hc₂.ne']
  suffices h_log : Filter.atTop.Tendsto (fun y : ℕ ↦
      (2 ^ (y ^ C) : ℝ) / Real.exp (2 ^ y * (1 - Real.log 2))) (𝓝 0) by
    refine squeeze_zero_norm' ?_ (h_log.comp (f := Nat.log 2) ?_)
    · simp only [norm_div, norm_pow, Real.norm_ofNat, Real.norm_eq_abs, Real.abs_exp,
        Function.comp_apply, Filter.eventually_atTop]
      refine ⟨4, fun n hn ↦ ?_⟩
      gcongr
      · linarith [Real.log_le_sub_one_of_pos zero_lt_two]
      · exact_mod_cast Nat.pow_log_le_self 2 <| by linarith
    · rw [Filter.tendsto_atTop_atTop]
      exact fun b ↦ ⟨2 ^ b, fun a ha ↦ Nat.le_log_of_pow_le (by norm_num) ha⟩
  suffices h_ln : Filter.atTop.Tendsto (fun y : ℕ ↦
      y ^ C * Real.log 2 - 2 ^ y * (1 - Real.log 2)) .atBot by
    -- If the natural logarithm of the expression tends to `-∞`, then the expression tends to `0`.
    have h_exp_ln : Filter.Tendsto (fun y : ℕ ↦ Real.exp _) .atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h_ln
    convert h_exp_ln using 2
    norm_num [Real.exp_sub, Real.exp_nat_mul, Real.exp_log]
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
    norm_num [mul_comm]
  have h_exp_poly : Filter.Tendsto (fun y : ℕ ↦ (2 : ℝ) ^ y / y ^ C) .atTop .atTop := by
    suffices h_exp : Filter.Tendsto (fun x : ℝ ↦ Real.exp (x * Real.log 2) / x ^ C) .atTop .atTop by
      convert h_exp.comp tendsto_natCast_atTop_atTop using 2
      norm_num [Real.exp_nat_mul, Real.exp_log]
    suffices h_limit_y : Filter.Tendsto (fun y : ℝ ↦ Real.exp y / y ^ C) .atTop .atTop by
      have h_subst : Filter.Tendsto (fun x : ℝ ↦
          Real.exp (x * Real.log 2) / (x * Real.log 2) ^ C) .atTop .atTop := by
        exact h_limit_y.comp <| Filter.tendsto_id.atTop_mul_const <| Real.log_pos <| by norm_num
      have h_simplify : Filter.Tendsto (fun x : ℝ ↦
          Real.exp (x * Real.log 2) / x ^ C / (Real.log 2) ^ C) .atTop .atTop := by
        simpa only [mul_pow, div_div] using h_subst
      convert h_simplify.atTop_mul_const (pow_pos (Real.log_pos one_lt_two) C) using 2
      ring_nf
      norm_num [mul_assoc, mul_comm, mul_left_comm]
    exact Real.tendsto_exp_div_pow_atTop _
  have h_rewrite : Filter.atTop.Tendsto (fun y : ℕ ↦
      (y ^ C : ℝ) * (Real.log 2 - (2 ^ y * (1 - Real.log 2)) / y ^ C)) .atBot := by
    have h_ln_tendsto : Filter.atTop.Tendsto (fun y : ℕ ↦
        Real.log 2 - (2 ^ y * (1 - Real.log 2)) / y ^ C) .atBot := by
      have h_mul : Filter.atTop.Tendsto (fun y : ℕ ↦ 2 ^ y * (1 - Real.log 2) / y ^ C) .atTop := by
        simpa only [mul_div_right_comm] using h_exp_poly.atTop_mul_const (sub_pos.mpr <|
          Real.log_two_lt_d9.trans_le <| by norm_num)
      rw [Filter.tendsto_atTop_atBot]
      exact fun x ↦ Filter.eventually_atTop.mp (h_mul.eventually_gt_atTop (Real.log 2 - x)) |>
        fun ⟨N, hN⟩ ↦ ⟨N, fun n hn ↦ by linarith [hN n hn]⟩
    rw [Filter.tendsto_atTop_atBot] at *
    intro b
    obtain ⟨i, hi⟩ := h_ln_tendsto (b ⊓ 0)
    refine ⟨i + 1, fun j hj ↦ ?_⟩
    refine le_trans (mul_le_mul_of_nonneg_left (hi _ (by linarith)) (by positivity)) ?_
    nlinarith [min_le_left b 0, min_le_right b 0,
        show (j:ℝ) ^ C ≥ 1 from one_le_pow₀ (by norm_cast; linarith)]
  exact h_rewrite.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with y hy using (by
    rw [mul_sub, mul_div_cancel₀ _ (by positivity)]))

theorem exp_mul (hf : f ∈ exp) (hg : g ∈ exp) : f * g ∈ exp := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  use a * b
  simp only [Nat.cast_mul, mul_pow]
  exact ha.mul hb

@[simp]
theorem exp_mul_exp : exp * exp = exp := by
  apply le_antisymm
  · rintro _ ⟨f, hf, g, hg, hfg⟩
    exact mono (exp_mul hf hg) hfg
  · intro f hf
    exact ⟨f, hf, 1, one_mem, by simp⟩

theorem primitiveRecursive_mul (hf : f ∈ primitiveRecursive) (hg : g ∈ primitiveRecursive) :
    f * g ∈ primitiveRecursive := by
  rcases hf with ⟨a, ha₁, ha₂⟩
  rcases hg with ⟨b, hb₁, hb₂⟩
  use a * b
  rw [← Primrec.nat_iff] at *
  use Primrec.nat_mul.comp ha₁ hb₁
  exact ha₂.mul hb₂

@[simp]
theorem primitiveRecursive_mul_self :
    primitiveRecursive * primitiveRecursive = primitiveRecursive := by
  apply le_antisymm
  · rintro _ ⟨f, hf, g, hg, hfg⟩
    exact mono (primitiveRecursive_mul hf hg) hfg
  · intro h hh
    refine ⟨h, hh, 1, ?_, by simp⟩
    exact ⟨1, Nat.Primrec.const 1, Asymptotics.isBigO_refl _ _⟩

theorem computable_mul (hf : f ∈ computable) (hg : g ∈ computable) :
    f * g ∈ computable := by
  rcases hf with ⟨a, ha₁, ha₂⟩
  rcases hg with ⟨b, hb₁, hb₂⟩
  use a * b
  use Primrec.nat_mul.to_comp.comp ha₁ hb₁
  exact ha₂.mul hb₂

@[simp]
theorem computable_mul_self : computable * computable = computable := by
  apply le_antisymm
  · rintro _ ⟨f, hf, g, hg, hfg⟩
    exact mono (computable_mul hf hg) hfg
  · intro h
    simp only [mem_mul]
    refine fun hh => ⟨h, hh, 1, ?_, by simp⟩
    exact ⟨1, Computable.const 1, Asymptotics.isBigO_refl ..⟩

end closure_mul

section closure_comp

variable {f g : ℕ → ℕ}

/--
If a function `g` is polynomially bounded, then `log(g(n))` is `O(log n)`.
-/
private lemma isBigO_log_comp_poly_real {C : ℝ} (hg : (g · : ℕ → ℝ) =O[.atTop] (· ^ C : ℕ → ℝ)) :
    (Real.log <| g ·) =O[.atTop] (Real.log ·) := by
  rw [Asymptotics.isBigO_iff'] at hg ⊢
  obtain ⟨c, hc₀, hc⟩ := hg
  use |C| + 1, by positivity
  filter_upwards [hc, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ⌈c⌉₊] with x h₁ h₂ h₃
  by_cases hx₄ : g x = 0
  · simp_all only [RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop,
      CharP.cast_eq_zero, norm_zero, mul_nonneg_iff_of_pos_left, abs_nonneg, Real.log_zero]
    positivity
  · simp_all only [RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop]
    rw [
      abs_of_nonneg (Real.log_nonneg <| mod_cast Nat.one_le_iff_ne_zero.mpr hx₄),
      abs_of_nonneg (Real.log_nonneg <| mod_cast h₂.le)]
    have h := Real.log_le_log (by positivity) h₁
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_abs, Real.log_rpow (by positivity)] at h
    have _ := @Real.log_nonneg x (mod_cast h₂.le)
    cases abs_cases C
    · nlinarith [@Real.log_le_log c x hc₀ ((Nat.le_ceil c).trans (mod_cast h₃.le))]
    · nlinarith [@Real.log_le_log c x hc₀ ((Nat.le_ceil c).trans (mod_cast h₃.le))]

theorem log_comp_poly (hf : f ∈ log) (hg : g ∈ poly) : f ∘ g ∈ log := by
  -- Apply `poly_iff_rpow` on `hg` to get a constant `C` such that `g n =O n^C`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, (fun n ↦ (g n : ℝ)) =O[.atTop] (fun n ↦ (n : ℝ) ^ C) :=
    poly_iff_rpow.mp hg
  -- Apply `isBigO_log_comp_poly_real` to `hC` to deduce that `Real.log (g n) =O Real.log n`.
  have h_log_g : (fun n ↦ Real.log (g n)) =O[.atTop] (Real.log ·) :=
    isBigO_log_comp_poly_real hC
  -- Since `f` is bounded by `A + B * log x`, `f (g n) ≤ A + B * log (g n)` for large `g n`.
  have h_f_g : ∃ A B : ℝ, ∀ n, f (g n) ≤ A + B * Real.log (g n) := by
    obtain ⟨A, B, hAB⟩ : ∃ A B : ℝ, ∀ x : ℕ, x ≥ 1 → f x ≤ A + B * Real.log x := by
      have h_f_g : (fun x : ℕ ↦ (f x : ℝ)) =O[.atTop] (Real.log ·) := by
        exact log_iff_rlog.mp hf
      rw [Asymptotics.isBigO_iff] at h_f_g
      norm_num +zetaDelta at *
      obtain ⟨c, a, hc⟩ := h_f_g
      use (∑ x ∈ .range (a + 1), f x) + |c|, |c|
      intro x hx; by_cases hx' : x ≤ a
      · simp_all only [Nat.cast_sum]
        refine le_add_of_le_of_nonneg ?_ (by positivity)
        refine le_add_of_le_of_nonneg ?_ (by positivity)
        exact Finset.single_le_sum (fun x _ ↦ (f x).cast_nonneg) (Finset.mem_range.mpr (by omega))
      · simp_all only [not_le, Nat.cast_sum]
        have _ := Real.log_nonneg (show (x : ℝ) ≥ 1 by norm_cast)
        specialize hc x hx'.le
        cases abs_cases c <;>
        cases abs_cases (Real.log x) <;>
        nlinarith [show 0 ≤ ∑ i ∈ .range (a + 1), (f i : ℝ) by positivity]
    refine ⟨A ⊔ (f 0), B ⊔ 0, fun n ↦ ?_⟩
    by_cases hn : 1 ≤ g n
    · exact hAB _ hn |> le_trans <| by gcongr <;> norm_num
    · simp at hn; simp [hn]
  -- Since `Real.log (g n) =O Real.log n`, by transitivity `f (g n) =O Real.log n`.
  obtain ⟨A, B, hAB⟩ := h_f_g
  have h_trans : (fun n ↦ (f (g n) : ℝ)) =O[.atTop] (Real.log ·) := by
    have h_const : (fun n ↦ A : ℕ → ℝ) =O[.atTop] (Real.log ·) := by
      norm_num [Asymptotics.isBigO_iff]
      refine ⟨|A|, 3, fun n hn ↦ ?_⟩
      rw [abs_of_nonneg (Real.log_nonneg <| by norm_cast; linarith)]
      exact le_mul_of_one_le_right (abs_nonneg _) <| by
        rw [Real.le_log_iff_exp_le <| by positivity]
        exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [show (n : ℝ) ≥ 3 by norm_cast]
    refine Asymptotics.IsBigO.trans ?_ (h_const.add (h_log_g.const_mul_left B))
    rw [Asymptotics.isBigO_iff]
    simp only [RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop]
    exact ⟨1, 0, fun n hn ↦ by rw [one_mul]; exact le_trans (hAB n) (le_abs_self _)⟩
  exact log_iff_rlog.mpr h_trans

private lemma log_le_const_mul_log_add_const {f : ℕ → ℕ} (hf : f ∈ log) :
    ∃ (C D : ℝ), ∀ n, (f n : ℝ) ≤ C * (Nat.log 2 n) + D := by
  unfold log bigO at hf
  obtain ⟨C, N, hN⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * Nat.log 2 n := by
    norm_num [Asymptotics.isBigO_iff] at hf
    rcases hf with ⟨c, N, hc⟩
    refine ⟨⌈c⌉₊, N, fun n hn ↦ ?_⟩
    exact_mod_cast (hc n hn).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil _) <| Nat.cast_nonneg _)
  -- Let `D = max_{n < N} f(n)`.
  obtain ⟨D, hD⟩ : ∃ D, ∀ n < N, f n ≤ D := by
    exact ⟨Finset.sup (Finset.range N) f, fun n hn ↦ Finset.le_sup (Finset.mem_range.mpr hn)⟩
  exact ⟨C, D, fun n ↦ if hn : n < N
    then by exact (Nat.cast_le.mpr (hD n hn)).trans (by norm_cast; nlinarith)
    else by exact (Nat.cast_le.mpr (hN n (le_of_not_gt hn))).trans (by norm_cast; nlinarith)⟩

private lemma log_of_quasipoly_mem_polylog (hg : g ∈ quasipoly) : (Nat.log 2 <| g ·) ∈ polylog := by
  -- Since `g ∈ quasipoly`, we know that `g(n) = O(2^{(log n)^C})` for some `C`.
  obtain ⟨C, hC⟩ : ∃ C : ℕ, (fun n ↦ (g n : ℝ)) =O[.atTop]
      (fun n ↦ (2 : ℝ) ^ (Nat.log 2 n ^ C) : ℕ → ℝ) := by
    obtain ⟨C, hC⟩ := hg
    use C
    norm_num [Asymptotics.isBigO_iff, Asymptotics.IsBigOWith] at *
    rcases hC with ⟨c, a, hc⟩
    exact ⟨c, a, fun n hn ↦ le_trans (hc n hn) (by norm_num [Norm.norm])⟩
  -- Taking the logarithm, we get `log(g(n)) ≤ log(K * 2^{(log n)^C}) ≈ log K + (log n)^C`.
  obtain ⟨C', D, h_log⟩ : ∃ C' D : ℝ, ∀ n, (Nat.log 2 (g n) : ℝ) ≤ C' * (Nat.log 2 n) ^ C + D := by
    -- Since `g(n) = O(2^{(log n)^C})`, we have `g(n) ≤ K * 2^{(log n)^C}` for some constant `K`.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ n, g n ≤ K * 2 ^ (Nat.log 2 n ^ C) := by
      obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ n, g n ≤ K * 2 ^ (Nat.log 2 n ^ C) := by
        rw [Asymptotics.isBigO_iff'] at hC
        norm_num +zetaDelta at *
        obtain ⟨c, hc₀, a, ha⟩ := hC
        -- Let `K = max_{0 ≤ n < a} g(n) / 2^((log n)^C)`.
        obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ n < a, (g n : ℝ) ≤ K * 2 ^ (Nat.log 2 n ^ C) := by
          use ∑ n ∈ .range a, (g n : ℝ) / 2 ^ (Nat.log 2 n ^ C)
          intro n hn; rw [Finset.sum_mul _ _ _]
          rw [← Finset.mem_range] at hn
          refine le_trans ?_ (Finset.single_le_sum (by intros; positivity) hn)
          rw [div_mul_cancel₀ _ (by positivity)]
        use K ⊔ c
        intro n
        rcases lt_or_ge n a with hn | hn
        · exact le_trans (hK n hn) (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        · exact le_trans (ha n hn) (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      use ⌈K⌉₊
      intro n
      exact_mod_cast le_trans (hK n) (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
    -- Taking the logarithm, we get `log(g(n)) ≤ log(K * 2^{(log n)^C}) = log K + (log n)^C`.
    have h_log_bound : ∀ n, Nat.log 2 (g n) ≤ Real.log K / Real.log 2 + (Nat.log 2 n) ^ C := by
      intro n
      have h_log_bound : Nat.log 2 (g n) ≤ Real.log (K * 2 ^ (Nat.log 2 n ^ C)) / Real.log 2 := by
        rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
        by_cases hn : g n = 0
        · norm_num [hn]
          rcases K with (_ | K)
          · norm_num
          simp only [Nat.cast_add, Nat.cast_one]
          exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by simp) (one_le_pow₀ one_le_two))
        · exact Real.log_le_log (by positivity) (mod_cast (Nat.pow_log_le_self 2 hn).trans (hK n))
      by_cases hK : K = 0
      · simp_all
      · simp only [ne_eq, Nat.cast_eq_zero, not_false_eq_true, pow_eq_zero_iff',
          OfNat.ofNat_ne_zero, Nat.log_eq_zero_iff, Order.lt_two_iff,
          Nat.not_ofNat_le_one, or_false, not_and, Decidable.not_not, false_and, Real.log_mul,
          Real.log_pow, Nat.cast_pow, hK] at h_log_bound
        exact h_log_bound.trans_eq (by rw [add_div, mul_div_cancel_right₀ _ (by positivity)])
    exact ⟨1, Real.log K / Real.log 2, fun n ↦ by linarith [h_log_bound n]⟩
  have h_poly : (fun n ↦ (Nat.log 2 (g n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n ^ C : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound (|C'| + |D|)
    norm_num +zetaDelta at *
    refine ⟨2, fun n hn ↦ ?_⟩
    apply le_trans (h_log n)
    have _ : (Nat.log 2 n : ℝ) ^ C ≥ 1 :=
      one_le_pow₀ (mod_cast Nat.le_log_of_pow_le (by norm_num) (by linarith))
    cases abs_cases C' <;>
    cases abs_cases D <;>
    nlinarith
  use C
  rw [Asymptotics.isBigO_iff] at *
  aesop

theorem log_comp_quasipoly (hf : f ∈ log) (hg : g ∈ quasipoly) : f ∘ g ∈ polylog := by
  obtain ⟨K, hK⟩ := log_of_quasipoly_mem_polylog hg
  -- Since `f ∈ log`, by `log_le_const_mul_log_add_const`, `f(x) ≤ A * log x + B`.
  obtain ⟨A, B, hA⟩ : ∃ A B : ℝ, ∀ n, (f n : ℝ) ≤ A * (Nat.log 2 n) + B :=
    log_le_const_mul_log_add_const hf
  -- Since `h(n) = O((log n)^K)`, `A h(n) + B` is also `O((log n)^K)` (as `polylog` is
  -- closed under scalar multiplication and addition).
  have hp : (fun n ↦ A * Nat.log 2 (g n) + B) =O[.atTop] (fun n ↦ (Nat.log 2 n ^ K : ℝ)) := by
    -- Since `h(n) = O((log n)^K)`, multiplying by a constant `A` preserves the big-O.
    have h : (fun n ↦ A * Nat.log 2 (g n)) =O[.atTop] (fun n ↦ (Nat.log 2 n ^ K : ℝ)) := by
      have h : (fun n ↦ (Nat.log 2 (g n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n ^ K : ℝ)) := by
        convert hK using 1
        norm_num [Asymptotics.isBigO_iff, bigO]
      exact h.const_mul_left A
    refine h.add ?_ |> fun h ↦ h.trans ?_
    · rw [Asymptotics.isBigO_iff]
      use ‖B‖
      filter_upwards [Filter.eventually_gt_atTop 1] with n hn
      simp only [Real.norm_eq_abs, norm_pow, RCLike.norm_natCast]
      refine le_mul_of_one_le_right (abs_nonneg _) ?_
      exact one_le_pow₀ (mod_cast Nat.le_log_of_pow_le (by norm_num) (by linarith))
    · apply Asymptotics.isBigO_refl
  use K
  rw [Asymptotics.isBigO_iff] at *
  norm_num at *
  choose C D hC using hp
  exact ⟨C, D, fun n hn ↦ (hA _).trans <| (le_abs_self _).trans (hC n hn)⟩

lemma Nat.log2_pow_le (b n : ℕ) : Nat.log 2 (b ^ n) ≤ n * (Nat.log 2 b + 1) := by
  suffices Nat.log 2 (b ^ n) ≤ n * Nat.log 2 b + n by
    linarith
  suffices h : b ^ n ≤ 2 ^ (n * Nat.log 2 b + n) from
    (Nat.log_mono_right h).trans (by simp)
  rw [pow_add, pow_mul', ← mul_pow, ← pow_succ]
  exact Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self one_lt_two b).le n

private lemma exists_le_log_add_const {f : ℕ → ℕ} (hf : f ∈ log) :
    ∃ C D, ∀ n, f n ≤ C * Nat.log 2 n + D := by
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * Nat.log 2 n := by
    have h_bound : ∃ C, ∀ᶠ n in .atTop, f n ≤ C * Nat.log 2 n := by
      have := hf
      unfold log at this
      unfold bigO at this
      norm_num [Asymptotics.isBigO_iff] at this
      obtain ⟨C, a, hC⟩ := this
      refine ⟨⌈C⌉₊, Filter.eventually_atTop.mpr ⟨a, fun n hn ↦ ?_⟩⟩
      rw [← @Nat.cast_le ℝ]
      push_cast
      nlinarith [Nat.le_ceil C, hC n hn, show (Nat.log 2 n : ℝ) ≥ 0 by positivity]
    aesop
  -- Let `D` be the maximum of `f(n)` for `n < N`.
  obtain ⟨D, hD⟩ : ∃ D, ∀ n < N, f n ≤ D := by
    exact ⟨(Finset.range N).sup f, fun n hn ↦ Finset.le_sup (Finset.mem_range.mpr hn)⟩
  exact ⟨C, D, fun n ↦ if hn : n < N
    then (hD n hn).trans (Nat.le_add_left _ _)
    else (hC n (le_of_not_gt hn)).trans (Nat.le_add_right _ _)⟩

theorem log_comp_exp (hf : f ∈ log) (hg : g ∈ exp) : f ∘ g ∈ linear := by
  obtain ⟨B, K, hB⟩ : ∃ B K, ∀ᶠ n in .atTop, g n ≤ K * B ^ n := by
    unfold exp at hg
    norm_num [Asymptotics.isBigO_iff] at hg
    obtain ⟨C, c, a, hc⟩ := hg
    use C, ⌈c⌉₊
    filter_upwards [Filter.eventually_ge_atTop a] with n hn
    exact_mod_cast (hc n hn).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil _) <| by positivity)
  -- Using `Nat.log_mul_le`, `log(K * B^n) ≤ log K + log(B^n) + 1`.
  -- Using `Nat.log2_pow_le`, `log(B^n) ≤ n * (log B + 1)`.
  have h_log_bound : ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ Nat.log 2 K + n * (Nat.log 2 B + 1) + 1 := by
    filter_upwards [hB, Filter.eventually_gt_atTop 0] with n hn hn'
    rcases eq_or_ne K 0 with rfl | hK'
    · simp at hn
      simp [hn]
    rcases eq_or_ne B 0 with rfl | hB'
    · simp [hn'] at hn
      simp [hn]
    apply Nat.le_trans (Nat.log_mono_right hn)
    refine Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by positivity) ?_)
    have h_simp : K * B ^ n < 2 ^ (Nat.log 2 K + 1) * 2 ^ (n * (Nat.log 2 B + 1)) := by
      refine mul_lt_mul'' (Nat.lt_pow_succ_log_self one_lt_two _) ?_ (by positivity) (by positivity)
      rw [pow_mul']
      exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by decide) _) (by positivity)
    exact h_simp.trans_le (by rw [← pow_add]; exact pow_le_pow_right₀ (by decide) (by linarith))
  -- Using `exists_le_log_add_const`, there are `C_f, D_f` such that `f(x) ≤ C_f * log x + D_f`.
  obtain ⟨C_f, D_f, hC_f⟩ := exists_le_log_add_const hf
  have h_com : ∀ᶠ n in .atTop, f (g n) ≤ C_f * (Nat.log 2 K + n * (Nat.log 2 B + 1) + 1) + D_f := by
    filter_upwards [h_log_bound] with n hn using (hC_f _).trans (by gcongr)
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ n in .atTop, f (g n) ≤ C * n := by
    use C_f * (Nat.log 2 B + 1) + C_f * Nat.log 2 K + C_f + D_f + 1
    filter_upwards [h_com, Filter.eventually_gt_atTop 0] with n hn hn'
    nlinarith [show 0 ≤ C_f * Nat.log 2 K by positivity, show 0 ≤ C_f * Nat.log 2 B by positivity]
  apply Asymptotics.IsBigO.of_bound (C + 1)
  filter_upwards [hC, Filter.eventually_gt_atTop 0] with n hn hn'
  norm_num
  exact_mod_cast hn.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))

theorem sublinear_comp_linear (hf : f ∈ sublinear) (hg : g ∈ linear) : f ∘ g ∈ sublinear := by
  obtain ⟨c, hc⟩ : ∃ c > 0, ∀ᶠ x in .atTop, |(f x : ℝ)| ≤ c * x := by
    have h_sublinear : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(f n : ℝ)| ≤ ε * n := by
      intro ε hε_pos
      have := hf.def (show 0 < ε by positivity)
      simp_all
    refine ⟨1, zero_lt_one, ?_⟩
    obtain ⟨N, hN⟩ := h_sublinear 1 zero_lt_one
    filter_upwards [Filter.Ici_mem_atTop N] with n hn using hN n hn
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ x in .atTop, |(g x : ℝ)| ≤ C * x := by
    simp only [bigO, linear, id_eq, Asymptotics.isBigO_iff, norm_natCast,
      Filter.eventually_atTop, Set.mem_setOf_eq] at hg
    simp only [Filter.eventually_atTop, Nat.abs_cast]
    exact hg
  have h_sub : ∀ ε > 0, ∃ N_f, ∀ x ≥ N_f, (f x : ℝ) ≤ ε * x := by
    intro ε hε
    have := (hf.congr' (by aesop) (by aesop)).def hε
    aesop
  -- Since `g ∈ linear`, there exists `C > 0` such that for all `x ≥ N_g`, `g(x) ≤ C * x`.
  obtain ⟨C, hC⟩ : ∃ C > 0, ∀ᶠ x in .atTop, |(g x : ℝ)| ≤ C * x := by
    use C ⊔ 1, by positivity
    refine hC.mono fun x hx ↦ ?_
    grw [← le_max_left, hx]
  have h_eps : ∀ ε > 0, ∃ N, ∀ x ≥ N, (f (g x) : ℝ) ≤ ε * x := by
    intro ε hε_pos
    obtain ⟨N_f, hN_f⟩ : ∃ N_f, ∀ x ≥ N_f, (f x : ℝ) ≤ (ε / (C + 1)) * x :=
      h_sub (ε / (C + 1)) (div_pos hε_pos (add_pos hC.1 zero_lt_one))
    obtain ⟨N_g, hN_g⟩ := Filter.eventually_atTop.mp hC.2
    obtain ⟨M, hM⟩ : ∃ M, ∀ x < N_f, (f x : ℝ) ≤ M :=
      ⟨∑ x ∈ .range N_f, (f x : ℝ), fun x hx ↦
        Finset.single_le_sum (fun x _ ↦ Nat.cast_nonneg (f x)) (Finset.mem_range.mpr hx)⟩
    use N_g ⊔ (⌈M / ε⌉₊ + 1)
    intro x hx
    by_cases h_case : g x < N_f
    · apply (hM _ h_case).trans
      nlinarith [Nat.le_ceil (M / ε), mul_div_cancel₀ M hε_pos.ne',
        show (x : ℝ) ≥ ⌈M / ε⌉₊ + 1 by grw [hx, ← le_max_right]; norm_cast]
    · have := hN_f (g x) (by linarith)
      rw [div_mul_eq_mul_div, le_div_iff₀ (by cases hC; positivity)] at this
      specialize hN_g x (le_trans (le_max_left _ _) hx)
      nlinarith [abs_le.mp hN_g, Nat.le_ceil (M / ε), mul_div_cancel₀ M hε_pos.ne']
  refine Asymptotics.isLittleO_iff.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := h_eps ε hε
  filter_upwards [Filter.eventually_ge_atTop N] with x hx
  simpa [abs_of_nonneg, hε.le] using hN x hx

/--
If g is linear, then Nat.log(g(n)) is logarithmic.
-/
private lemma log_comp_linear {g : ℕ → ℕ} (hg : g ∈ linear) : (Nat.log 2 <| g ·) ∈ log := by
  have ⟨C, hC⟩ : ∃ C, ∀ᶠ n in .atTop, g n ≤ C * n := by
    have ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hg
    use ⌈C⌉₊
    filter_upwards [hC, Filter.eventually_gt_atTop 0] with x hx₁ hx₂
    have := (le_abs_self _).trans <| hx₁.trans <|
      mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
    simp only [Int.cast_natCast, id_eq, norm_natCast] at this
    exact_mod_cast this
  have ⟨D, hD⟩  : ∃ D, ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ Nat.log 2 C + Nat.log 2 n + D := by
    refine ⟨2, ?_⟩
    filter_upwards [hC] with n hn
    rcases eq_or_ne (g n) 0 with hn' | hn'
    · simp_all
    simp only [Filter.eventually_atTop] at hC
    refine Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow ?_ ?_)
    · aesop
    · have _ := Nat.lt_pow_succ_log_self one_lt_two C
      have _ := Nat.lt_pow_succ_log_self one_lt_two n
      simp only [ne_eq, Nat.succ_eq_add_one, Nat.pow_succ', Nat.pow_add] at *
      nlinarith
  apply Asymptotics.IsBigO.of_bound (Nat.log 2 C + D + 1)
  norm_num +zetaDelta at *
  obtain ⟨a, ha⟩ := hD
  refine ⟨a + 2, fun n hn ↦ ?_⟩
  norm_cast
  nlinarith [ha n (by linarith), Nat.log_pos one_lt_two (by linarith : 1 < n)]

/-- If g is linear, then g(n) * Nat.log(g(n)) is linearithmic. -/
private lemma linear_mul_log_comp_linear {g : ℕ → ℕ} (hg : g ∈ linear) :
    (fun n ↦ g n * Nat.log 2 (g n)) ∈ linearithmic := by
  exact linearithmic_of_linear_mul hg (log_comp_linear hg)

theorem linearithmic_comp (hf : f ∈ linearithmic) (hg : g ∈ linear) : f ∘ g ∈ linearithmic := by
  unfold linearithmic at *
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, g n ≤ C * n := by
    obtain ⟨C, N, hC⟩ := hg.exists_pos
    simp only [Asymptotics.IsBigOWith, norm_natCast, id_eq, Filter.eventually_atTop] at hC
    rcases hC with ⟨k, hK⟩
    use ⌈C⌉₊, k
    intro n hn
    exact_mod_cast (hK n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  obtain ⟨D, M, hD⟩ : ∃ D M, ∀ x ≥ M, f x ≤ D * x * Nat.log 2 x := by
    simp only [bigO, Nat.cast_mul, Asymptotics.isBigO_iff, norm_natCast, norm_mul,
      Filter.eventually_atTop, Set.mem_setOf_eq] at hf
    rcases hf with ⟨c, a, hc⟩
    refine ⟨⌈c⌉₊, a, fun x hx ↦ ?_⟩
    specialize hc x hx
    rw [← @Nat.cast_le ℝ]
    push_cast
    nlinarith [Nat.le_ceil c, show (x : ℝ) * Nat.log 2 x ≥ 0 by positivity]
  have hfg₀ : ∀ n ≥ N, f (g n) ≤ D * (C * n) * Nat.log 2 (C * n) + ∑ x ∈ .range M, f x := by
    intro n hn
    by_cases hmn : g n < M
    · apply le_add_of_nonneg_of_le (Nat.zero_le _)
      exact Finset.single_le_sum (fun x _ ↦ Nat.zero_le (f x)) (Finset.mem_range.mpr hmn)
    · refine le_add_of_le_of_nonneg ?_ (Nat.zero_le _)
      specialize hC n hn
      exact (hD _ (le_of_not_gt hmn)).trans (by gcongr)
  obtain ⟨K, hK⟩ : ∃ K, ∀ n ≥ N, f (g n) ≤ K * n * Nat.log 2 n + K := by
    use D * C * (Nat.log 2 C + 2) + ∑ x ∈ .range M, f x + 1
    intro n hn
    have hfg₁ : f (g n) ≤ D * C * n * (Nat.log 2 n + Nat.log 2 C + 1) + ∑ x ∈ .range M, f x := by
      specialize hfg₀ n hn
      have h_log_bound : Nat.log 2 (C * n) ≤ Nat.log 2 n + Nat.log 2 C + 1 := by
        by_cases hC : C = 0
        · simp [hC]
        by_cases hn : n = 0
        · simp [hn]
        refine Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow ?_ ?_)
        · positivity
        · have h₁ := Nat.lt_pow_succ_log_self one_lt_two n
          have h₂ := Nat.lt_pow_succ_log_self one_lt_two C
          simp [Nat.pow_succ', Nat.pow_add] at h₁ h₂ ⊢
          nlinarith [Nat.pos_of_ne_zero hC, Nat.pos_of_ne_zero hn]
      exact hfg₀.trans (by nlinarith [show 0 ≤ D * C * n by positivity])
    rcases k : Nat.log 2 n with (_ | k)
    · simp_all only [zero_add, Nat.log_eq_zero_iff, Order.lt_two_iff,
        Nat.not_ofNat_le_one, or_false, mul_zero]
      have _ : 0 ≤ D * C := by positivity
      interval_cases n <;> simp <;> nlinarith
    · simp_all only
      grind
  apply Asymptotics.IsBigO.of_bound (K + K)
  norm_num +zetaDelta at *
  refine ⟨N + 2, fun n hn ↦ ?_⟩
  norm_cast
  specialize hK n (by omega)
  have _ : n ≤ n * Nat.log 2 n := Nat.le_of_lt_succ <|
    by nlinarith [Nat.le_log_of_pow_le one_lt_two <| show 2 ^ 1 ≤ n by linarith]
  nlinarith

private lemma log_nearLinear_bound (D : ℕ) :
    (fun n ↦ (Nat.log 2 (n * (Nat.log 2 n)^D) : ℤ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℤ)) := by
  -- Using the lemma `Nat.log_mul_le_add`, we bound `log₂(n * log₂(n)^D)`.
  have h_log_mul_le_add : ∀ n ≥ 2, Nat.log 2 (n * Nat.log 2 n ^ D) ≤
      Nat.log 2 n + D * (Nat.log 2 (Nat.log 2 n) + 1) + 1 := by
    intro n hn
    have h_log_mul_le_add : Nat.log 2 (n * Nat.log 2 n ^ D) ≤
        Nat.log 2 n + Nat.log 2 (Nat.log 2 n ^ D) + 1 := by
      have h_log_mul_le_add : ∀ a b : ℕ, a ≥ 2 → b ≥ 2 →
          Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
        intro a b ha hb
        refine Nat.le_of_lt_succ <| Nat.log_lt_of_lt_pow ?_ ?_ <;> norm_num
        · aesop
        · have h_log_a : a < 2 ^ (Nat.log 2 a + 1) := by
            exact Nat.lt_pow_succ_log_self (by decide) _
          have h_log_b : b < 2 ^ (Nat.log 2 b + 1) := by
            exact Nat.lt_pow_succ_log_self (by decide) _
          convert mul_lt_mul'' h_log_a h_log_b (by positivity) (by positivity) using 1; ring
      by_cases h₂ : Nat.log 2 n ^ D ≥ 2
      · exact h_log_mul_le_add _ _ hn h₂
      · interval_cases _ : Nat.log 2 n ^ D <;> simp_all
    have h_log_pow_le : Nat.log 2 (Nat.log 2 n ^ D) ≤ D * (Nat.log 2 (Nat.log 2 n) + 1) := by
      have h_log_pow_le : ∀ a k : ℕ, a > 0 → Nat.log 2 (a ^ k) ≤ k * (Nat.log 2 a + 1) := by
        intros a k ha_pos
        have h_log_pow_le : a ^ k ≤ 2 ^ (k * (Nat.log 2 a + 1)) := by
          rw [pow_mul']; gcongr; exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)
        exact Nat.le_trans (Nat.log_mono_right h_log_pow_le) (by rw [Nat.log_pow (by decide)])
      exact h_log_pow_le _ _ (Nat.log_pos one_lt_two hn)
    linarith
  have h_log_mul_le_add' : ∀ n ≥ 2, Nat.log 2 (n * Nat.log 2 n ^ D) ≤
      Nat.log 2 n + D * (Nat.log 2 n + 1) + 1 :=
    fun n hn ↦ (h_log_mul_le_add n hn).trans (by gcongr; exact Nat.log_le_self _ _)
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨D + D + 2, 2, fun n hn ↦ ?_⟩
  norm_cast
  nlinarith [h_log_mul_le_add' n hn, Nat.le_log_of_pow_le one_lt_two (show 2 ^ 1 ≤ n by linarith)]

theorem nearLinear_comp (hf : f ∈ nearLinear) (hg : g ∈ nearLinear) : f ∘ g ∈ nearLinear := by
  obtain ⟨C₁, hC₁⟩ := hf
  obtain ⟨C₂, hC₂⟩ := hg
  obtain ⟨M, hM⟩ : ∃ M, ∀ᶠ n in .atTop, g n ≤ M * n * (Nat.log 2 n)^C₂ := by
    rw [Asymptotics.isBigO_iff'] at hC₂
    norm_num +zetaDelta at *
    obtain ⟨c, hc₀, a, ha⟩ := hC₂
    refine ⟨⌈c⌉₊, a, fun n hn ↦ ?_⟩
    rw [← @Nat.cast_le ℝ]; push_cast
    nlinarith [Nat.le_ceil c, ha n hn, show (0 : ℝ) ≤ n * Nat.log 2 n ^ C₂ by positivity]
  -- Using `log_nearLinear_bound`, `log(g(n)) = O(log n)`.
  have h_log₀ : (fun n ↦ (Nat.log 2 (g n) : ℤ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℤ)) := by
    have h_log₁ : ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ Nat.log 2 (M * n * (Nat.log 2 n)^C₂) := by
      filter_upwards [hM] with n hn using Nat.log_mono_right hn
    -- Using `log_nearLinear_bound`, `log(M * n * (log n)^D) = O(log n)`.
    have h_log₂ : (fun n ↦ (Nat.log 2 (M * n * Nat.log 2 n ^ C₂) : ℤ))
        =O[.atTop] (fun n ↦ (Nat.log 2 n : ℤ)) := by
      rcases M with (_ | M)
      · simpa using Asymptotics.isBigO_zero _ _
      simp only [Nat.cast_mul, Nat.cast_pow, mul_assoc, Filter.eventually_atTop] at *
      -- Bound `log((M + 1) * (n * (log n)^C₂))`.
      have h_log_bound : ∀ᶠ n in .atTop, Nat.log 2 ((M + 1) * (n * (Nat.log 2 n)^C₂)) ≤
          Nat.log 2 (n * Nat.log 2 n ^ C₂) + Nat.log 2 (M + 1) + 1 := by
        refine Filter.eventually_atTop.mpr ⟨2, fun n hn ↦ ?_⟩
        refine Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow ?_ ?_)
        · positivity [Nat.log_pos one_lt_two hn]
        · rw [Nat.pow_succ, pow_add, pow_add]
          have _ := Nat.lt_pow_succ_log_self one_lt_two (n * Nat.log 2 n ^ C₂)
          have _ := Nat.lt_pow_succ_log_self one_lt_two (M + 1)
          norm_num [Nat.pow_succ'] at *
          nlinarith [Nat.zero_le (n * Nat.log 2 n ^ C₂)]
      have hq := log_nearLinear_bound C₂
      rw [Asymptotics.isBigO_iff] at *
      obtain ⟨c, hc⟩ := hq
      use c + Nat.log 2 (M + 1) + 1
      filter_upwards [h_log_bound, hc, Filter.eventually_gt_atTop 1] with n hn₁ hn₂ hn₃
      norm_num at *
      have : (Nat.log 2 ((M + 1) * (n * Nat.log 2 n ^ C₂)) : ℝ) ≤
          Nat.log 2 (n * Nat.log 2 n ^ C₂) + Nat.log 2 (M + 1) + 1 := by exact_mod_cast hn₁
      have : (Nat.log 2 n : ℝ) ≥ 1 := by
        exact_mod_cast Nat.le_log_of_pow_le (by norm_num) (by linarith)
      nlinarith
    refine Asymptotics.IsBigO.trans ?_ h_log₂
    rw [Asymptotics.isBigO_iff]
    exact ⟨1, by filter_upwards [h_log₁] with n hn; simpa using mod_cast hn⟩
  have ⟨K, K', hK⟩ : ∃ K K', ∀ᶠ n in .atTop, f (g n) ≤ K * (g n * (Nat.log 2 (g n))^C₁) + K' := by
    rw [Asymptotics.isBigO_iff'] at *
    obtain ⟨K, hK₁, hK₂⟩ := hC₁
    norm_num +zetaDelta at *
    obtain ⟨a, ha⟩ := hK₂
    -- Let `K'` be such that `f(x) ≤ K * (x * (log x)^C) + K'` for all `x`.
    obtain ⟨K', hK'⟩ : ∃ K', ∀ x, f x ≤ K * (x * (Nat.log 2 x)^C₁) + K' := by
      refine ⟨∑ x ∈ .range a, (f x : ℝ), fun x ↦ ?_⟩
      by_cases hx : x < a
      · exact le_add_of_nonneg_of_le (by positivity)
          (Finset.single_le_sum (fun x _ ↦ Nat.cast_nonneg (f x)) (Finset.mem_range.mpr hx))
      · exact le_add_of_le_of_nonneg (ha x (le_of_not_gt hx)) (by positivity)
    refine ⟨⌈K⌉₊, ⌈K'⌉₊, a, fun n hn ↦ ?_⟩
    specialize hK' (g n)
    exact_mod_cast hK'.trans (add_le_add
      (mul_le_mul_of_nonneg_right (Nat.le_ceil _) <| by positivity) <| Nat.le_ceil _)
  have ⟨K'', hK''⟩ : ∃ K'', ∀ᶠ n in .atTop, f (g n) ≤ K'' * (n * (Nat.log 2 n)^(C₁ + C₂)) + K' := by
    -- Using `h_log₀`, we can bound `(Nat.log 2 (g n))^C₁` by `O((Nat.log 2 n)^C₁)`.
    obtain ⟨L, hL⟩ : ∃ L, ∀ᶠ n in .atTop, (Nat.log 2 (g n))^C₁ ≤ L * (Nat.log 2 n)^C₁ := by
      rw [Asymptotics.isBigO_iff'] at h_log₀
      norm_num +zetaDelta at *
      obtain ⟨c, hc₀, a, ha⟩ := h_log₀
      refine ⟨⌈c ^ C₁⌉₊, a, fun n hn ↦ ?_⟩
      rw [← @Nat.cast_le ℝ]
      push_cast
      apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (ha n hn) _).trans
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
    -- Substitute the bounds from `hM` and `hL` into the inequality from `hK`.
    have h_subst : ∀ᶠ n in .atTop, f (g n) ≤
        K * (M * n * Nat.log 2 n ^ C₂ * (L * Nat.log 2 n ^ C₁)) + K' := by
      filter_upwards [hK, hM, hL] with n hn hn' hn'' using le_trans hn <| by gcongr
    refine ⟨K * M * L, ?_⟩
    filter_upwards [h_subst] with n hn
    convert hn using 1
    ring
  use C₁ + C₂
  simp only [Function.comp_apply, norm_natCast, Asymptotics.isBigO_iff]
  simp only [Filter.eventually_atTop] at hK'' hM ⊢
  obtain ⟨a, ha⟩ := hK''
  use K'' + K' + 1
  refine ⟨a + 2, fun n hn ↦ ?_⟩
  specialize ha n (by linarith)
  norm_cast
  nlinarith [show 0 < n * Nat.log 2 n ^ (C₁ + C₂) from
      mul_pos (by omega) (pow_pos (Nat.log_pos one_lt_two (by omega)) _)]

private lemma exists_bound_of_isBigO {f h : ℕ → ℕ} (hf : (f · : ℕ → ℤ) =O[.atTop] (h · : ℕ → ℤ)) :
    ∃ C : ℕ, ∀ n, f n ≤ C * h n + C := by
  obtain ⟨c, N, hc⟩ : ∃ c N, ∀ n ≥ N, f n ≤ c * h n := by
    rw [Asymptotics.isBigO_iff'] at hf
    simp only [norm_natCast, Filter.eventually_atTop] at hf
    obtain ⟨c, hc, N, hN⟩ := hf
    refine ⟨⌈c⌉₊, N, fun n hn ↦ ?_⟩
    exact_mod_cast (hN n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  have ⟨M, hM⟩ : ∃ M, ∀ n < N, f n ≤ M :=
    ⟨(Finset.range N).sup f, fun n ↦ Finset.le_sup ∘ Finset.mem_range.mpr⟩
  refine ⟨c ⊔ M, fun n ↦ ?_⟩
  nth_grw 1 [← le_max_left c M, ← le_max_right c M]
  rcases lt_or_ge n N with hn | hn
  · specialize hM n hn
    omega
  · specialize hc n hn
    omega

theorem poly_comp_log (hf : f ∈ poly) (hg : g ∈ log) : f ∘ g ∈ polylog := by
  rcases hf with ⟨C, hc⟩
  have ⟨A, hA⟩ : ∃ A : ℕ, ∀ n, f n ≤ A * n ^ C + A := by
    rw [Asymptotics.isBigO_iff'] at hc
    norm_num +zetaDelta at *
    obtain ⟨c, hc₀, a, ha⟩ := hc
    -- Let `A` be a constant such that `f(n) ≤ A * n^C + A` for all `n ≥ a`.
    obtain ⟨A, hA⟩ : ∃ A : ℕ, ∀ n ≥ a, f n ≤ A * n ^ C + A := by
      refine ⟨⌈c⌉₊, fun n hn ↦ ?_⟩
      specialize ha n hn
      suffices (f n : ℝ) ≤ ⌈c⌉₊ * n ^ C + ⌈c⌉₊ from mod_cast this
      nlinarith [Nat.le_ceil c, show 0 ≤ (n : ℝ) ^ C by positivity]
    -- Let `A'` be a constant such that `f(n) ≤ A' * n^C + A'` for all `n < a`.
    obtain ⟨A', hA'⟩ : ∃ A' : ℕ, ∀ n < a, f n ≤ A' * n ^ C + A' := by
      refine ⟨∑ n ∈ .range a, f n + 1, fun n hn ↦ ?_⟩
      nlinarith [Finset.single_le_sum (fun n _ ↦ Nat.zero_le (f n)) (Finset.mem_range.mpr hn),
        pow_nonneg (Nat.zero_le n) C]
    refine ⟨A ⊔ A', fun n ↦ ?_⟩
    rcases lt_or_ge n a with hn | hn
    · specialize hA' n hn
      nth_grw 1 [← le_max_right A A']
      omega
    · specialize hA n hn
      nth_grw 1 [← le_max_left A A']
      omega
  obtain ⟨B, hB⟩ := exists_bound_of_isBigO hg
  have hfg (n) : f (g n) ≤ A * (B * Nat.log 2 n + B) ^ C + A :=
    (hA _).trans (by gcongr; exact hB n)
  -- The term `(B log n + B)^C` is a polynomial in `log n` of degree `C`, so it is `O((log n)^C)`.
  have h_polylog : ∃ D : ℕ, ∀ n, (B * Nat.log 2 n + B) ^ C ≤ D * (Nat.log 2 n) ^ C + D := by
    -- We can bound `(B * log n + B)^C` by `(2B * log n)^C` for large enough `n`.
    have h_bound : ∀ n, (B * Nat.log 2 n + B) ^ C ≤ (2 * B * Nat.log 2 n) ^ C + (2 * B) ^ C := by
      intro n
      rcases eq_or_ne B 0 with rfl | hB₀
      · simp_all
      simp only [two_mul]
      rcases k : Nat.log 2 n with (_ | k)
      · simp_all only [ne_eq, Nat.log_eq_zero_iff, Order.lt_two_iff, Nat.not_ofNat_le_one,
          or_false, mul_zero, zero_add]
        cases C
        · norm_num
        · norm_num
          gcongr
          omega
      · simp only [add_mul]
        apply le_add_of_le_of_nonneg ?_ (by positivity)
        exact Nat.pow_le_pow_left (by nlinarith) C
    use (2 * B) ^ C
    exact fun n ↦ le_trans (h_bound n) (by rw [mul_pow])
  obtain ⟨D, hD⟩ := h_polylog
  have ⟨E, hE⟩ : ∃ E : ℕ, ∀ n, f (g n) ≤ E * (Nat.log 2 n) ^ C + E :=
    ⟨A * D + A, fun n ↦ by nlinarith [hfg n, hD n, pow_nonneg (Nat.zero_le (Nat.log 2 n)) C]⟩
  use C
  apply Asymptotics.IsBigO.of_bound (E + E)
  simp only [Function.comp_apply, norm_natCast, Nat.cast_pow, norm_pow, Filter.eventually_atTop]
  use 2
  intro n hn
  norm_cast
  nlinarith [hE n, Nat.one_le_pow C _ (Nat.log_pos one_lt_two hn)]

private lemma exists_poly_bound_nat {f : ℕ → ℕ} (hf : f ∈ poly) :
    ∃ C K : ℕ, ∀ n, f n ≤ K * (n + 1) ^ C := by
  rcases hf with ⟨C, hC⟩
  rw [Asymptotics.isBigO_iff'] at hC
  simp only [norm_natCast, norm_pow, Filter.eventually_atTop] at hC
  rcases hC with ⟨c, hc_pos, N, hN⟩
  have ⟨K₁, hK₁⟩ : ∃ K : ℕ, ∀ n ≥ N, f n ≤ K * (n + 1) ^ C := by
    use Nat.ceil c + 1
    intro n hn
    specialize hN n hn
    suffices (f n : ℝ) ≤ (⌈c⌉₊ + 1) * (n + 1) ^ C by exact_mod_cast this
    have h : (n : ℝ) ^ C ≤ (n + 1) ^ C := by gcongr; linarith
    grw [hN, ← Nat.le_ceil c, h]
    nlinarith
  have ⟨K₂, hK₂⟩ : ∃ K : ℕ, ∀ n < N, f n ≤ K * (n + 1) ^ C := by
    refine ⟨(Finset.range N).sup f, fun n hn ↦ ?_⟩
    nlinarith [Finset.le_sup (f := f) (Finset.mem_range.mpr hn), pow_pos (Nat.succ_pos n) C]
  refine ⟨C, K₁ ⊔ K₂, fun n ↦ ?_⟩
  rcases lt_or_ge n N with hn | hn
  · specialize hK₂ n hn
    nth_grw 1 [← le_max_right K₁ K₂]
    omega
  · specialize hK₁ n hn
    nth_grw 1 [← le_max_left K₁ K₂]
    omega

theorem poly_comp (hf : f ∈ poly) (hg : g ∈ poly) : f ∘ g ∈ poly := by
  have ⟨C_f, K_f, hf⟩ := exists_poly_bound_nat hf
  have ⟨C_g, K_g, hg⟩ := exists_poly_bound_nat hg
  use C_f * C_g
  have hfg_bound (n) : f (g n) ≤ K_f * (K_g * (n + 1) ^ C_g + 1) ^ C_f :=
    (hf _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by linarith [hg n]) _))
  have ⟨C, K, hfg_poly⟩ : ∃ C K : ℕ, ∀ n, f (g n) ≤ K * (n + 1) ^ (C_f * C_g) := by
    have h (n) : (K_g * (n + 1) ^ C_g + 1) ^ C_f ≤ (K_g + 1) ^ C_f * (n + 1) ^ (C_f * C_g) := by
      rw [pow_mul', ← mul_pow]
      exact Nat.pow_le_pow_left (by nlinarith [pow_pos (Nat.succ_pos n) C_g]) _
    use C_f * C_g, K_f * (K_g + 1) ^ C_f
    exact fun n ↦ (hfg_bound n).trans (by nlinarith [h n])
  rw [Asymptotics.isBigO_iff]
  use K * 2 ^ (C_f * C_g)
  norm_num
  refine ⟨1, fun n hn ↦ le_trans (Nat.cast_le.mpr (hfg_poly n)) ?_⟩; norm_cast; ring_nf
  rw [mul_assoc, ← mul_pow]
  gcongr
  lia

private lemma isBigO_poly_comp_exp {k C : ℕ}
    (hf : (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(n ^ k) : ℕ → ℤ))
    (hg : (g · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(C ^ n) : ℕ → ℤ)) :
    ∃ K : ℕ, (fun n ↦ f (g n) : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(K ^ n) : ℕ → ℤ) := by
  have ⟨N_f, c_f, hM_f⟩ : ∃ N_f c_f, ∀ x, x ≥ N_f → f x ≤ c_f * x ^ k := by
    simp_all only [Nat.cast_pow, Asymptotics.isBigO_iff', norm_natCast, norm_pow,
      Filter.eventually_atTop]
    have ⟨c, hc, a, ha⟩ := hf
    refine ⟨a, ⌈c⌉₊, fun x hx ↦ ?_⟩
    exact_mod_cast (ha x hx).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  -- For all `x`, `f(x) ≤ M_f + c_f * x^k`.
  obtain ⟨M_f, hM_f⟩ : ∃ M_f, ∀ x, f x ≤ M_f + c_f * x ^ k := by
    use (Finset.range N_f).sup f
    intro x
    by_cases hx : x < N_f
    · exact le_add_of_le_of_nonneg (Finset.le_sup (Finset.mem_range.mpr hx)) (Nat.zero_le _)
    · exact le_add_of_nonneg_of_le (Nat.zero_le _) (hM_f x (le_of_not_gt hx))
  -- From `hg`, there exists `c_g > 0` and `N_g` such that for all `n ≥ N_g`, `g(n) ≤ c_g * C^n`.
  obtain ⟨c_g, N_g, hM_g⟩ : ∃ c_g N_g, ∀ n ≥ N_g, g n ≤ c_g * C ^ n := by
    rw [Asymptotics.isBigO_iff'] at hg
    norm_num at *
    have ⟨c, hc₀, N_g, hN_g⟩ := hg
    refine ⟨⌈c⌉₊, N_g, fun n hn ↦ ?_⟩
    exact_mod_cast (hN_g n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  -- So for `n ≥ N_g`, `(g(n))^k ≤ (c_g * C^n)^k = c_g^k * (C^k)^n`.
  have h_bound : ∀ n ≥ N_g, (g n) ^ k ≤ c_g ^ k * (C ^ k) ^ n := by
    intro n hn; convert Nat.pow_le_pow_left (hM_g n hn) k using 1; ring
  -- Let `K = max(2, C^k)`. We claim `f(g(n)) = O(K^n)`.
  use 2 ⊔ C ^ k
  -- Thus `f(g(n)) ≤ M_f + c_f * c_g^k * (C^k)^n`.
  have h_final_bound : ∀ n ≥ N_g, f (g n) ≤ M_f + c_f * c_g ^ k * (C ^ k) ^ n :=
    fun n hn ↦ (hM_f _).trans (by nlinarith [h_bound n hn])
  have h_K_bound : ∀ n ≥ N_g, (C ^ k) ^ n ≤ (max 2 (C ^ k)) ^ n ∧ 1 ≤ (max 2 (C ^ k)) ^ n :=
    fun n hn ↦ ⟨Nat.pow_le_pow_left (le_max_right _ _) _, Nat.one_le_pow _ _ (by positivity)⟩
  rw [Asymptotics.isBigO_iff]
  norm_num +zetaDelta at *
  refine ⟨M_f + c_f * c_g ^ k, N_g, fun n hn ↦ ?_⟩
  erw [Real.norm_of_nonneg (by positivity)]
  exact le_trans (Nat.cast_le.mpr (h_final_bound n hn))
    (by norm_cast; nlinarith [h_K_bound n hn, show 0 ≤ c_f * c_g ^ k by positivity])

theorem poly_comp_exp (hf : f ∈ poly) (hg : g ∈ exp) : f ∘ g ∈ exp := by
  have ⟨k₁, hk₁⟩ := hf.imp fun _ ↦ mod_cast id
  have ⟨k₂, hk₂⟩ := hg.imp fun _ ↦ mod_cast id
  simpa [exp] using isBigO_poly_comp_exp hk₁ hk₂

private lemma log_bound_of_quasipoly {g : ℕ → ℕ} (hg : g ∈ quasipoly) :
    ∃ D : ℕ, (fun n ↦ (Nat.log 2 (g n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℝ) ^ D) := by
  have h := @log_comp_quasipoly
  contrapose! h
  refine ⟨fun n ↦ Nat.log 2 n, g, ?_, hg, ?_⟩
  · apply Asymptotics.isBigO_iff.mpr
    exact ⟨1, Filter.Eventually.of_forall fun n ↦ by norm_num⟩
  · intro H
    obtain ⟨C, hC⟩ := H
    apply h C
    rw [Asymptotics.isBigO_iff'] at *
    aesop

private lemma quasipoly_of_log_bound {f : ℕ → ℕ} (D : ℕ)
    (hf : (fun n ↦ (Nat.log 2 (f n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℝ) ^ D)) :
    f ∈ quasipoly := by
  -- From `hf`, we have `Nat.log 2 (f n) ≤ C * (Nat.log 2 n)^D` for large `n`. Then
  -- `f n ≤ 2^(Nat.log 2 (f n) + 1) ≤ 2^(C * (Nat.log 2 n)^D + 1)`.
  have ⟨C, hC⟩ : ∃ C : ℕ, ∀ᶠ n in .atTop, Nat.log 2 (f n) ≤ C * (Nat.log 2 n) ^ D := by
    rw [Asymptotics.isBigO_iff'] at hf
    norm_num +zetaDelta at *
    have ⟨c, hc, a, ha⟩ := hf
    refine ⟨⌈c⌉₊, a, fun n hn ↦ ?_⟩
    exact_mod_cast Nat.le_of_lt_succ <| by
      rw [← @Nat.cast_lt ℝ]; push_cast
      nlinarith [Nat.le_ceil c, ha n hn,
        pow_nonneg (Nat.cast_nonneg (Nat.log 2 n) : (0 :ℝ) ≤ Nat.log 2 n) D]
  -- We want to show `f n = O(2^((Nat.log 2 n)^K))`. Choose `K > D`. Then `(Nat.log 2 n)^K`
  -- eventually dominates `C * (Nat.log 2 n)^D + 1`.
  have ⟨K, hK₁, hK₂⟩ : ∃ K, K > D ∧ ∀ᶠ n in .atTop, C * Nat.log 2 n ^ D + 1 ≤ Nat.log 2 n ^ K := by
    refine ⟨D + 1, ?_, ?_⟩
    · norm_num
    simp only [Order.add_one_le_iff, Filter.eventually_atTop, pow_succ']
    refine ⟨2 ^ (C + 1), fun n hn ↦ ?_⟩
    have h1 : C < Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
    have h2 : 0 < Nat.log 2 n ^ D := by
      apply pow_pos
      exact Nat.log_pos (by norm_num) (by
        linarith [Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num)
          (show C + 1 ≥ 1 from Nat.le_add_left _ _)])
    nlinarith
  refine ⟨K, ?_⟩
  rw [Asymptotics.isBigO_iff']
  -- Then `f n ≤ 2^(Nat.log 2 (f n) + 1) ≤ 2^(C * (Nat.log 2 n)^D + 1) ≤ 2^((Nat.log 2 n)^K)`.
  have h_bound : ∀ᶠ n in .atTop, f n ≤ 2 ^ ((Nat.log 2 n) ^ K) := by
    filter_upwards [hC, hK₂] with n hn hn'
    exact (Nat.lt_pow_of_log_lt one_lt_two <| by linarith).le
  simp only [Filter.eventually_atTop, norm_natCast, norm_pow] at h_bound ⊢
  rcases h_bound with ⟨M, hM⟩
  refine ⟨1, by norm_num, M, fun n hn ↦ ?_⟩
  simpa [Norm.norm] using mod_cast hM n hn

theorem quasipoly_comp (hf : f ∈ quasipoly) (hg : g ∈ quasipoly) : f ∘ g ∈ quasipoly := by
  have ⟨Df, hDf⟩ := log_bound_of_quasipoly hf
  have ⟨Dg, hDg⟩ := log_bound_of_quasipoly hg
  have ⟨M, C, hM⟩ : ∃ M C : ℕ, ∀ m ≥ M, (Nat.log 2 (f m) : ℝ) ≤ C * Nat.log 2 m ^ Df := by
    rw [Asymptotics.isBigO_iff'] at hDf
    rcases hDf with ⟨c, hc₀, hc⟩
    have ⟨M, hM⟩ := Filter.eventually_atTop.mp hc
    refine ⟨M, ⌈c⌉₊, fun m hm ↦ ?_⟩
    specialize hM m hm; norm_num at *
    exact hM.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  have ⟨K, hK⟩ : ∃ K : ℕ, ∀ n, (Nat.log 2 (f (g n)) : ℝ) ≤ K ∨
      Nat.log 2 (f (g n)) ≤ C * (Nat.log 2 (g n) : ℝ) ^ Df := by
    use Finset.sup (Finset.image (fun m ↦ Nat.log 2 (f m)) (Finset.range M)) id
    exact fun n ↦ if hn : g n < M then
      Or.inl <| mod_cast Finset.le_sup (f := id) <| Finset.mem_image_of_mem _ <|
        Finset.mem_range.mpr hn
      else Or.inr <| hM _ <| le_of_not_gt hn
  -- From (2), `Nat.log 2 (g n) ≤ C' * (Nat.log 2 n)^Dg` for large `n`.
  obtain ⟨C', hC'⟩ : ∃ C' : ℕ, ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ C' * (Nat.log 2 n : ℝ) ^ Dg := by
    rw [Asymptotics.isBigO_iff] at hDg
    simp only [RCLike.norm_natCast, norm_pow, Filter.eventually_atTop] at hDg ⊢
    rcases hDg with ⟨c, a, hc⟩
    refine ⟨⌈c⌉₊, a, fun n hn ↦ ?_⟩
    exact (hc n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  apply quasipoly_of_log_bound (Dg * Df)
  rw [Asymptotics.isBigO_iff]
  have ⟨C, hC⟩ : ∃ C, ∀ᶠ n in .atTop, Nat.log 2 (f (g n)) ≤ C * (Nat.log 2 n : ℝ) ^ (Dg * Df) := by
    use K + C * C' ^ Df
    filter_upwards [hC', Filter.eventually_gt_atTop 1] with n h hn'
    simp only [pow_mul]
    rcases hK n with hK₂ | hK₂ <;> apply hK₂.trans
    · exact (le_add_of_nonneg_right <| by positivity).trans
        (le_mul_of_one_le_right (by positivity) <| one_le_pow₀ <| one_le_pow₀ <|
          mod_cast Nat.le_log_of_pow_le (by norm_num) <| by linarith)
    · apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h _) (by positivity)).trans
      ring_nf
      exact le_add_of_nonneg_right (by positivity)
  use C
  filter_upwards [hC] with n hn
  simpa using hn

/-- If g is O(log n) and C > 1, then C^(g n) is polynomially bounded. -/
private lemma exists_pow_bound_of_exp_comp_log_real {g : ℕ → ℕ} {C : ℝ} (hC : 1 < C)
    (hg : (fun n ↦ (g n : ℝ)) =O[.atTop] (fun n ↦ Real.log (n : ℝ))) :
    ∃ K : ℝ, (fun n ↦ C ^ (g n : ℝ)) =O[.atTop] (fun n ↦ (n : ℝ) ^ K) := by
  have ⟨M, hM⟩ : ∃ M : ℝ, ∀ᶠ n in .atTop, (g n : ℝ) ≤ M * Real.log n := by
    rw [Asymptotics.isBigO_iff'] at hg
    rcases hg with ⟨M, hM₁, hM₂⟩
    refine ⟨M, ?_⟩
    filter_upwards [hM₂, Filter.eventually_gt_atTop 1] with n hn hn'
    rwa [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.log_nonneg <| Nat.one_le_cast.mpr <| pos_of_gt hn')] at hn
  have h_bound : ∀ᶠ n in .atTop, (C : ℝ) ^ (g n : ℝ) ≤ (n : ℝ) ^ (M * Real.log C) := by
    filter_upwards [hM, Filter.eventually_gt_atTop 1] with n hn hn'
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity)]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.log_pos hC])
  refine ⟨M * Real.log C, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [h_bound] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  simpa using hn

/-- If f(n) is O(C^n) with C >= 1, then f(g(n)) is O(C^(g(n))). -/
private lemma isBigO_comp_exp_of_isBigO_exp {f g : ℕ → ℕ} {C : ℝ} (hC : 1 ≤ C)
    (hf : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ C ^ (n : ℝ))) :
    (fun n ↦ (f (g n) : ℝ)) =O[.atTop] (fun n ↦ C ^ (g n : ℝ)) := by
  simp only [Real.rpow_natCast, Asymptotics.isBigO_iff, RCLike.norm_natCast, norm_pow,
    Real.norm_eq_abs, Filter.eventually_atTop] at hf ⊢
  rcases hf with ⟨c, a, hc⟩
  have ⟨M, hM⟩ : ∃ M, ∀ n < a, f n ≤ M :=
    ⟨(Finset.range a).sup f, fun n hn ↦ Finset.le_sup (Finset.mem_range.mpr hn)⟩
  refine ⟨c ⊔ M, a, fun n hn ↦ ?_⟩
  rcases lt_or_ge (g n) a with h | h
  · grw [← hM _ h, ← le_max_right, ← (show 1 ≤ |C| by rw [abs_of_nonneg] <;> linarith)]
    simp
  · grw [← le_max_left, hc _ h]

/-- If f(n) is O(C^n) with 0 <= C <= 1, then f is polynomially bounded.
TODO: Show this holds for any LawfulGrowthRate instead.
-/
private lemma exp_subset_poly_of_le_one {f : ℕ → ℕ} {C : ℝ} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1)
    (hf : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ C ^ (n : ℝ))) : f ∈ poly := by
  use 0
  have h : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ 1 : ℕ → ℝ) := by
    apply hf.trans
    norm_num [Asymptotics.isBigO_iff]
    exact ⟨1, 0, fun n hn ↦ by rw [abs_of_nonneg hC₀]; exact pow_le_one₀ hC₀ hC₁⟩
  simpa [Asymptotics.isBigO_iff] using h

theorem exp_comp_log (hf : f ∈ exp) (hg : g ∈ log) : f ∘ g ∈ poly := by
  by_cases hC : ∃ C : ℝ, 1 < C ∧ (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ C ^ (n : ℝ))
  · -- Apply `isBigO_comp_exp_of_isBigO_exp` to show `f(g(n)) = O(C^{g(n)})`.
    rcases hC with ⟨C, hC₁, hC₂⟩
    have h_f_g_poly : (fun n ↦ (f (g n) : ℝ)) =O[.atTop] (fun n ↦ C ^ (g n : ℝ)) := by
      apply isBigO_comp_exp_of_isBigO_exp hC₁.le hC₂
    -- Apply `exists_pow_bound_of_exp_comp_log_real` to show `C^{g(n)} = O(n^K)` for some `K`.
    have ⟨K, hK⟩ : ∃ K : ℝ, (fun n ↦ C ^ (g n : ℝ)) =O[.atTop] (fun n ↦ (n : ℝ) ^ K) := by
      rw [log_iff_rlog] at hg
      exact exists_pow_bound_of_exp_comp_log_real hC₁ hg
    have h := h_f_g_poly.trans hK
    convert poly_iff_rpow.mpr _
    exact ⟨K, h⟩
  · contrapose! hC
    rcases hf with ⟨(_ | _ | C), hC⟩
    · have h_f_zero : ∀ᶠ n in .atTop, f n = 0 := by
        rw [Asymptotics.isBigO_iff'] at hC
        norm_num +zetaDelta at *
        rcases hC with ⟨c, hc, a, ha⟩
        exact ⟨a + 1, fun n hn ↦ by simpa [show n ≠ 0 by linarith] using ha n (by linarith)⟩
      norm_num +zetaDelta at *
      simp_rw [Asymptotics.isBigO_iff]
      use 2, one_lt_two, 1
      filter_upwards [Filter.eventually_ge_atTop h_f_zero.choose] with n hn
      norm_num [h_f_zero.choose_spec n hn]
    · simp only [zero_add, Nat.cast_one, one_pow, Asymptotics.isBigO_one_iff,
        Filter.IsBoundedUnder, Filter.IsBounded, norm_natCast, Filter.eventually_map,
        Filter.eventually_atTop, ge_iff_le] at hC
      simp only [Real.rpow_natCast, Asymptotics.isBigO_iff, norm_natCast, norm_pow,
        Real.norm_eq_abs, Filter.eventually_atTop] at ⊢
      rcases hC with ⟨b, a, hb⟩
      refine ⟨2, one_lt_two, b, a, fun n hn ↦ ?_⟩
      grw [hb n hn, ← one_le_pow₀ (by simp), mul_one]
      grw [← hb a le_rfl, Nat.cast_nonneg']
    · refine ⟨C + 1 + 1, by linarith, ?_⟩
      norm_cast at *
      rwa [Asymptotics.isBigO_iff] at hC ⊢

lemma exp_bound_nat {f : ℕ → ℕ} (hf : f ∈ exp) :
    ∃ (C : ℕ) (M : ℕ), 1 < C ∧ ∀ n, f n ≤ M * C ^ n := by
  have ⟨C₀, hC₀, N, hN⟩ : ∃ C₀ M₀ N, ∀ n ≥ N, f n ≤ M₀ * C₀ ^ n := by
    rcases hf with ⟨C₀, hC₀⟩
    norm_num [Asymptotics.isBigO_iff] at hC₀
    rcases hC₀ with ⟨c, a, hca⟩
    refine ⟨C₀, ⌈c⌉₊, a, fun n hn ↦ ?_⟩
    specialize hca n hn
    exact_mod_cast (by nlinarith [Nat.le_ceil c, show (C₀ ^ n : ℝ) ≥ 0 by positivity] :
      (f n : ℝ) ≤ ⌈c⌉₊ * C₀ ^ n)
  -- Choose `C = max(C₀, 2)` to ensure `C > 1`.
  set C := C₀ ⊔ 2
  have hC : 1 < C := lt_max_of_lt_right one_lt_two
  refine ⟨C, hC₀ + ∑ n ∈ .range N, f n + 1, hC, fun n ↦ ?_⟩
  by_cases hn : n < N
  · nlinarith [Nat.zero_le (∑ n ∈ .range N, f n),
      Finset.single_le_sum (fun n _ ↦ Nat.zero_le (f n)) (Finset.mem_range.mpr hn),
      pow_pos (zero_lt_one.trans hC) n]
  · exact le_trans (hN n (le_of_not_gt hn))
      (Nat.mul_le_mul (by nlinarith [Nat.zero_le (∑ n ∈ .range N, f n)])
        (Nat.pow_le_pow_left (le_max_left _ _) _))

lemma polylog_bound_nat (hg : g ∈ polylog) :
    ∃ (k : ℕ) (K : ℕ), ∀ᶠ n in .atTop, g n ≤ K * (Nat.log 2 n) ^ k := by
  rcases hg with ⟨k, hk⟩
  have ⟨K, hK⟩ := hk.exists_pos
  simp only [Nat.cast_pow, Asymptotics.IsBigOWith, norm_natCast, norm_pow,
    Filter.eventually_atTop] at hK ⊢
  use k, ⌈K⌉₊
  rcases hK with ⟨hK, a, ha⟩
  refine ⟨a, fun n hn ↦ ?_⟩
  suffices h : (g n : ℝ) ≤ ⌈K⌉₊ * Nat.log 2 n ^ k from mod_cast h
  nlinarith [Nat.le_ceil K, ha n hn, show (Nat.log 2 n : ℝ) ^ k ≥ 0 by positivity]

lemma quasipoly_of_bound_nat {A k M : ℕ}
    (hf : ∀ᶠ n in .atTop, f n ≤ M * A ^ ((Nat.log 2 n) ^ k)) : f ∈ quasipoly := by
  -- Let `L = log₂ A`. Then `A < 2^(L+1)`
  set L := Nat.log 2 A
  have h_bound : ∀ᶠ n in .atTop, (f n : ℝ) ≤ M * 2 ^ ((L + 1) * (Nat.log 2 n) ^ k) := by
    filter_upwards [hf] with n hn
    have hA_le : (A : ℝ) ≤ 2 ^ (L + 1) := by
      exact_mod_cast Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)
    grw [pow_mul, ← hA_le, hn]
    exact_mod_cast le_rfl
  -- We want to bound this by `2 ^ ((log n)^(k+1))`.
  replace h_bound : ∀ᶠ n in .atTop, (f n : ℝ) ≤ M * 2 ^ ((Nat.log 2 n) ^ (k + 1)) := by
    have h_ineq : ∀ᶠ n in .atTop, (L + 1) * (Nat.log 2 n) ^ k ≤ (Nat.log 2 n) ^ (k + 1) := by
      have h_ineq : ∀ᶠ n in .atTop, (L + 1) ≤ Nat.log 2 n := by
        rw [Filter.eventually_atTop]
        exact ⟨2 ^ (L + 1), fun n ↦ Nat.le_log_of_pow_le one_lt_two⟩
      filter_upwards [h_ineq] with n hn using by rw [pow_succ']; exact Nat.mul_le_mul_right _ hn
    filter_upwards [h_bound, h_ineq] with n hn hn' using
      le_trans hn (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hn')
        (Nat.cast_nonneg _))
  refine ⟨k + 1, ?_⟩
  apply Asymptotics.isBigO_iff.mpr
  norm_num at *
  exact ⟨M, h_bound.choose, fun n hn ↦
    le_trans (h_bound.choose_spec n hn) (by norm_num [Norm.norm])⟩

theorem exp_comp_polylog (hf : f ∈ exp) (hg : g ∈ polylog) : f ∘ g ∈ quasipoly := by
  have ⟨C, M_f, hC, hf⟩ := exp_bound_nat hf
  have ⟨k, K, hg⟩ := polylog_bound_nat hg
  set K' := 1 ⊔ K
  apply quasipoly_of_bound_nat (A := C ^ K') (k := k) (M := M_f)
  simp +zetaDelta only [Filter.eventually_atTop, Function.comp_apply] at hg ⊢
  refine ⟨hg.choose, fun n hn ↦ le_trans (hf _) ?_⟩
  simpa only [← pow_mul] using Nat.mul_le_mul_left _ (pow_le_pow_right₀ hC.le <| by
    nlinarith [hg.choose_spec n hn, Nat.le_max_left 1 K, Nat.le_max_right 1 K,
      pow_nonneg (Nat.zero_le (Nat.log 2 n)) k])

theorem exp_comp_linear (hf : f ∈ exp) (hg : g ∈ linear) : f ∘ g ∈ exp := by
  -- From `hf`, we have some `C` such that `f n = O(C^n)`. We can assume `C ≥ 2` WLOG.
  have ⟨C, hC⟩ : ∃ C, (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ C ^ n : ℕ → ℤ) ∧ 2 ≤ C := by
    rcases hf with ⟨C, hC⟩
    generalize_proofs at *
    rcases C with (_ | _ | C) <;> norm_num at *
    · refine ⟨2, ?_, ?_⟩ <;> norm_num
      apply hC.trans
      simpa using Asymptotics.isBigO_of_le _ fun n ↦ by cases n <;> norm_num [pow_succ']
    · refine ⟨2, ?_, ?_⟩ <;> norm_num [Asymptotics.isBigO_iff]
      rcases hC with ⟨c, hc⟩
      norm_num [Norm.norm] at *
      refine ⟨c, hc.choose, fun n hn ↦ ?_⟩
      exact le_trans (hc.choose_spec n hn)
        (le_mul_of_one_le_right (le_trans (Nat.cast_nonneg _) (hc.choose_spec _ le_rfl))
          (one_le_pow₀ (by norm_num)))
    · exact ⟨_, hC, by linarith⟩
  have ⟨K, hK⟩ : ∃ K, ∀ᶠ n in .atTop, g n ≤ K * n := by
    have ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp hg
    norm_num at *
    refine ⟨⌈K⌉₊, hK.choose, fun n hn ↦ ?_⟩
    exact_mod_cast (hK.choose_spec n hn).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  -- Then `f (g n) = O(C^(g n))`.
  have hfg : (fun n ↦ (f (g n) : ℤ)) =O[.atTop] (fun n ↦ C ^ (g n) : ℕ → ℤ) := by
    simp only [Filter.eventually_atTop, Asymptotics.isBigO_iff', norm_natCast, norm_pow] at hK hC ⊢
    rcases hC with ⟨⟨c, hc, a, ha⟩, hC⟩
    use c + ∑ x ∈ .range (a + 1), (f x : ℝ) / ‖C‖ ^ x
    constructor
    · exact add_pos_of_pos_of_nonneg hc (Finset.sum_nonneg fun _ _ ↦
        div_nonneg (Nat.cast_nonneg _) (by positivity))
    refine ⟨a + hK.choose + 1, fun b hb ↦ ?_⟩
    simp only [add_mul]
    rcases lt_or_ge (g b) a with h | h
    · apply le_add_of_nonneg_of_le (by positivity)
      rw [Finset.sum_mul]
      exact le_trans
        (by rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos (norm_pos_iff.mpr (by linarith)) _))])
        (Finset.single_le_sum
          (fun i _ ↦ mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (norm_nonneg _) _))
            (pow_nonneg (norm_nonneg _) _))
          (Finset.mem_range.mpr (by linarith)))
    · grw [← ha _ h, le_add_iff_nonneg_right]
      positivity
  have h_mono : (fun n ↦ C ^ (g n) : ℕ → ℤ) =O[.atTop] (fun n ↦ C ^ (K * n) : ℕ → ℤ) := by
    rw [Asymptotics.isBigO_iff]
    norm_num [Norm.norm]
    have ⟨N, hN⟩ := Filter.eventually_atTop.mp hK
    refine ⟨1, N, fun n hn ↦ ?_⟩
    rw [abs_of_nonneg (by norm_cast; linarith)]
    exact (pow_le_pow_right₀ (by norm_cast; linarith) (hN n hn)).trans (by norm_num)
  have h_comp : (fun n ↦ (f (g n) : ℤ)) =O[.atTop] (fun n ↦ (C^K) ^ n : ℕ → ℤ) := by
    simpa only [pow_mul] using hfg.trans h_mono
  use C.natAbs^K
  simpa [abs_of_nonneg (by linarith : 0 ≤ C)] using h_comp

lemma _root_.Nat.Primrec.sum_range (hf : Nat.Primrec f) :
    Nat.Primrec (∑ i ∈ .range ·, f i) := by
  -- Define g such that g(n, s) = s + f(n)
  let g : ℕ → ℕ → ℕ := fun n s ↦ s + f n
  have hg : Nat.Primrec (fun p ↦ g p.unpair.1 p.unpair.2) := by
    convert Nat.Primrec.add.comp (.pair (.right) (hf.comp .left)) using 1
    simp [g]
  have hS : (fun n ↦ ∑ i ∈ .range n, f i) = fun n ↦ Nat.rec 0 (fun n s ↦ g n s) n := by
    funext n
    induction n
    · rfl
    · simp [*, Finset.sum_range_succ]
      rfl
  rw [hS]
  convert Nat.Primrec.prec1 0 hg using 1
  simp

/--
Every primitive recursive function is bounded by a monotone primitive recursive function.
-/
private lemma exists_monotone_primrec_bound {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ g, Nat.Primrec g ∧ Monotone g ∧ ∀ n, f n ≤ g n := by
  -- Let `S(n) = ∑ i in range (n+1), f i`.
  set S : ℕ → ℕ := fun n ↦ ∑ i ∈ .range (n + 1), f i
  refine ⟨S, ?_, ?_, ?_⟩
  · exact hf.sum_range.comp Nat.Primrec.succ
  · exact fun n m hnm ↦ Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hnm))
  · exact fun n ↦ Finset.single_le_sum (fun i _ ↦ Nat.zero_le (f i))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))

theorem primitiveRecursive_comp (hf : f ∈ primitiveRecursive) (hg : g ∈ primitiveRecursive) :
    f ∘ g ∈ primitiveRecursive := by
  rcases hf with ⟨h_f, hf_primrec, hf_bound⟩
  rcases hg with ⟨h_g, hg_primrec, hg_bound⟩
  -- Apply the lemma that allows bounding a primitive recursive function by a monotone one to `h_f`.
  have ⟨H_f, hH_f_primrec, hH_f_mono, hH_f_bound⟩ := exists_monotone_primrec_bound hf_primrec
  -- Thus `f(g(n)) ≤ C_f H_f(g(n)) + K`.
  have ⟨C_f, N_f, hf_bound⟩ : ∃ C_f N_f, ∀ x ≥ N_f, f x ≤ C_f * H_f x := by
    have ⟨C_f, N_f, hC_f⟩ := hf_bound.exists_pos
    rw [Asymptotics.isBigOWith_iff] at hC_f
    norm_num at *
    have ⟨N_f, hN_f⟩ := hC_f
    refine ⟨⌈C_f⌉₊, N_f, fun x hx ↦ ?_⟩
    specialize hN_f x hx
    exact_mod_cast hN_f.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hH_f_bound x))
      (by positivity)) |> le_trans <| mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _)
  have ⟨C_g, N_g, hg_bound⟩ : ∃ C_g N_g, ∀ n ≥ N_g, g n ≤ C_g * h_g n := by
    rw [bigO, Set.mem_setOf_eq, Asymptotics.isBigO_iff'] at hg_bound
    norm_num at *
    have ⟨c, hc₀, N_g, hc⟩ := hg_bound
    refine ⟨⌈c⌉₊, N_g, fun n hn ↦ ?_⟩
    exact_mod_cast (hc n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  have ⟨K, hK⟩ : ∃ K, ∀ x < N_f, f x ≤ K :=
    ⟨(Finset.range N_f).sup f, fun x hx ↦ Finset.le_sup (Finset.mem_range.mpr hx)⟩
  -- Thus for `n ≥ N_g`, `f(g(n)) ≤ C_f H_f(C_g h_g(n)) + K`.
  have h_comp_bound : ∀ n ≥ N_g, f (g n) ≤ C_f * H_f (C_g * h_g n) + K := by
    intros n hn
    specialize hH_f_mono (hg_bound _ hn)
    rcases lt_or_ge (g n) N_f with hgn | hgn
    · exact le_add_of_nonneg_of_le (Nat.zero_le _) (hK _ hgn)
    · exact le_add_of_le_of_nonneg ((hf_bound _ hgn).trans (mul_le_mul_right hH_f_mono _)) K.zero_le
  -- The function `B(n) = C_f H_f(C_g h_g(n)) + K` is primitive recursive.
  have hB_primrec : Nat.Primrec (fun n ↦ C_f * H_f (C_g * h_g n) + K) := by
    have h_const_mul : Nat.Primrec (fun n ↦ C_g * n) := by
      convert Nat.Primrec.mul.comp (Nat.Primrec.const C_g |>.pair Nat.Primrec.id) using 1
      simp [Nat.unpair_pair]
    have h_Cg_hg : Nat.Primrec (fun n ↦ C_g * h_g n) := h_const_mul.comp hg_primrec
    have h_Hf_comp : Nat.Primrec (fun n ↦ H_f (C_g * h_g n)) := hH_f_primrec.comp h_Cg_hg
    have h_mul_Cf : Nat.Primrec (fun n ↦ C_f * n) := by
      have h_mul_step : ∀ m, Nat.Primrec (fun n ↦ n * m) := by
        intro m
        induction m with
        | zero => simp [Nat.Primrec.const]
        | succ k hk =>
          simp_all only [Nat.mul_succ]
          convert Nat.Primrec.add.comp (hk.pair Nat.Primrec.id) using 1
          exact funext fun n ↦ by simp [Nat.unpair_pair]
      simpa only [mul_comm] using h_mul_step C_f
    have h_Cf_Hf : Nat.Primrec (fun n ↦ C_f * H_f (C_g * h_g n)) := h_mul_Cf.comp h_Hf_comp
    have h_add_K : Nat.Primrec (fun n ↦ n + K) :=
      Nat.recOn K Nat.Primrec.id fun _ ihn ↦ Nat.Primrec.succ.comp ihn
    exact h_add_K.comp h_Cf_Hf
  refine ⟨_, hB_primrec, ?_⟩
  apply Asymptotics.IsBigO.of_bound 1
  simp only [Function.comp_apply, norm_natCast, Nat.cast_add, Nat.cast_mul, one_mul,
    Filter.eventually_atTop]
  refine ⟨N_g, fun n hn ↦ ?_⟩
  grw [h_comp_bound n hn]
  convert le_refl _
  exact Real.norm_of_nonneg (by positivity)

section computable

/-- `max_scan f n` computes the maximum value of `f` on `0..n`. -/
private def max_scan (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (f 0) (fun k acc ↦ acc ⊔ (f (k + 1))) n

private lemma max_scan_le (n : ℕ) : f n ≤ max_scan f n := by
  induction n <;> simp [*, max_scan]

private lemma max_scan_mono (f : ℕ → ℕ) : Monotone (max_scan f) := by
  exact monotone_nat_of_le_succ fun k ↦ le_max_left ..

private lemma computable_max_scan {f : ℕ → ℕ} (hf : Computable f) : Computable (max_scan f) := by
  open Computable in
  apply nat_rec .id (h := fun _ p ↦ p.2 ⊔ (f (p.1 + 1))) (.const (f 0))
  apply Computable₂.comp₂
      (f := fun (p : ℕ × ℕ) (q : ℕ × ℕ) ↦ p.2 ⊔ q.2)
      (g := fun _ (p : ℕ × ℕ) ↦ (p.1, p.2)) (h := fun _ p ↦ (p.1, f (p.1 + 1)))
  · exact (Primrec₂.to_comp Primrec.nat_max).comp (comp snd fst) (comp snd snd)
  · exact pair (comp fst snd) (comp snd snd)
  · exact pair (comp fst (comp snd .id)) (hf.comp <| succ.comp <| comp fst <| comp snd .id)

lemma bigO_implies_bound {f g : ℕ → ℕ} (h : f ∈ bigO g) :
    ∃ C K, ∀ n, f n ≤ C * g n + K := by
  have ⟨C, hC⟩ := h.exists_pos
  rw [Asymptotics.IsBigOWith] at hC
  simp only [norm_natCast, Filter.eventually_atTop] at hC
  rcases hC with ⟨hC, a, hA⟩
  -- Let `K` be the maximum of `f(n)` for `n < N`.
  have ⟨K, hK⟩ : ∃ K, ∀ n < a, f n ≤ K :=
    ⟨(Finset.range a).sup f, fun n hn ↦ Finset.le_sup (Finset.mem_range.mpr hn)⟩
  refine ⟨⌈C⌉₊, K, fun n ↦ ?_⟩
  rcases lt_or_ge n a with hn | hn
  · exact (hK n hn).trans (by norm_num)
  · specialize hA n hn
    exact_mod_cast (by nlinarith [Nat.le_ceil C, show (g n : ℝ) ≥ 0 by positivity] :
      (f n : ℝ) ≤ ⌈C⌉₊ * g n + K)

lemma bound_implies_bigO {f g : ℕ → ℕ} (C K : ℕ) (h : ∀ n, f n ≤ C * g n + K) :
    f ∈ bigO (fun n ↦ g n + 1) := by
  simp only [bigO, Nat.cast_add, Nat.cast_one, Asymptotics.isBigO_iff, norm_natCast,
    Filter.eventually_atTop, Set.mem_setOf_eq]
  use C + K + 1, 0
  refine fun n hn ↦ ?_
  erw [Real.norm_of_nonneg (by positivity)]
  norm_cast
  nlinarith [h n]

lemma exists_monotone_computable_bound {f : ℕ → ℕ} (hf : Computable f) :
    ∃ F, Computable F ∧ Monotone F ∧ f ∈ bigO F := by
  refine ⟨max_scan f, computable_max_scan hf, max_scan_mono f, ?_⟩
  apply Asymptotics.IsBigO.of_bound 1
  norm_num
  exact ⟨0, fun n hn ↦ max_scan_le n⟩

/--
The function `n ↦ C * n + K` is computable.
-/
private lemma computable_affine (C K : ℕ) : Computable (fun n ↦ C * n + K) := by
  apply Computable.comp (f := fun n ↦ n + K) (g := fun n ↦ C * n)
  · induction K with
    | zero => exact Computable.id
    | succ _ ih =>
      simp only [Nat.add_comm, Nat.add_left_comm] at ih ⊢
      exact ih.comp Computable.succ
  · apply Primrec.to_comp
    induction C with
    | zero => simp [Primrec.const]
    | succ _ ih =>
      simp_rw [Nat.succ_mul]
      exact Primrec.nat_add.comp ih Primrec.id

theorem computable_comp (hf : f ∈ computable) (hg : g ∈ computable) :
    f ∘ g ∈ computable := by
  rcases hf with ⟨f', hf', hf⟩
  rcases hg with ⟨g', hg', hg⟩
  have ⟨F, hF₁, hF₂⟩ := exists_monotone_computable_bound hf'
  have ⟨C₁, K₁, hC₁⟩ := bigO_implies_bound hg
  have ⟨C₂, K₂, hC₂⟩ := bigO_implies_bound (hf.trans hF₂.2)
  -- Define H(n) = C₂ * F(C₁ * g'(n) + K₁) + K₂.
  set H : ℕ → ℕ := fun n ↦ C₂ * F (C₁ * g' n + K₁) + K₂
  refine ⟨H, ?_, ?_⟩
  · exact (computable_affine _ _).comp <| hF₁.comp <| (computable_affine _ _).comp hg'
  have hfg_le_H : ∀ n, f (g n) ≤ H n := fun n ↦
    le_trans (hC₂ _) (add_le_add_left (mul_le_mul_of_nonneg_left (hF₂.1 (hC₁ _)) (Nat.zero_le _)) _)
  simp_rw [bigO, Set.mem_setOf_eq, Asymptotics.isBigO_iff, Filter.eventually_atTop]
  use 1, 0
  exact fun n hn ↦ by simpa using hfg_le_H n

end computable

/-- `poly` is `O(n)^O(1)`. -/
theorem poly_eq_linear_pow_const : poly = linear ^ const := by
  apply le_antisymm
  · rintro f ⟨C, hC⟩
    obtain ⟨D, KD, hKD⟩ : ∃ D KD : ℕ, ∀ n, f n ≤ D * (n + 1) ^ C + KD := by
      obtain ⟨D, K, hK⟩ := bigO_implies_bound hC;
      exact ⟨D, K, fun n => (hK n).trans (by gcongr; linarith)⟩
    refine ⟨fun n => D * (n + 1) + KD + 1, ?_, _, const_mem_const (C + 1), ?_⟩
    · apply Asymptotics.IsBigO.of_bound (D + KD + 1)
      simp only [norm, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, Int.cast_one, id_eq, Nat.abs_cast, Filter.eventually_atTop]
      exact ⟨D + KD + 2, fun _ _ ↦ by rw [abs_of_nonneg] <;> norm_cast <;> nlinarith⟩
    · intro n
      specialize hKD n
      rcases C with _ | C
      · grind
      simp only [pow_succ'] at hKD ⊢
      grw [hKD, ← show _ ≤ _ + 1 from Nat.le_succ (D * (n + 1) + KD)]
      rcases D with (_ | D)
      · rcases KD with _ | _ <;> simp [Order.one_le_iff_pos]
      rcases KD with _ | KD
      · simp only [add_zero]
        gcongr <;> lia
      · have h : (D + 1) * (n + 1) + (KD + 1) ≥ (n + 1) := by nlinarith
        refine le_trans ?_ (mul_le_mul_right (Nat.mul_le_mul h <| Nat.pow_le_pow_left h _) _)
        have : 0 < (n + 1) * (n + 1) ^ C := by positivity
        have : 0 < (D + 1) * (n + 1) * (n + 1) ^ C := by positivity
        nlinarith
  · rintro _ ⟨f, hf, g, hg, hfg⟩
    obtain ⟨C, ⟨K, hK⟩⟩ := bigO_implies_bound hf
    obtain ⟨D, ⟨E, hE⟩⟩ := bigO_implies_bound hg
    use D + E + 1
    apply Asymptotics.IsBigO.of_bound ((C + K + 1) ^ (D + E + 1))
    simp only [norm_natCast, norm_pow, Filter.eventually_atTop]
    simp only [id_eq] at hK
    simp only [Pi.one_apply, mul_one] at hE
    refine ⟨1, fun n hn ↦ ?_⟩
    norm_cast
    specialize hE n
    specialize hfg n
    specialize hK n
    dsimp only at hfg
    grw [hfg, Nat.pow_le_pow_left (show f n ≤ (C + K + 1) * n by nlinarith) _, mul_pow]
    apply Nat.mul_le_mul <;> exact pow_le_pow_right₀ (by lia) (by lia)

@[simp]
theorem exp_eq_const_pow_exp : const ^ linear = exp := by
  apply Set.eq_of_subset_of_subset;
  · intro h hh
    rw [mem_pow] at hh
    rcases hh with ⟨f, hf, g, hg, hh⟩
    obtain ⟨C, hC⟩ := bounded_of_const hf
    obtain ⟨D, hD⟩ := bigO_implies_bound hg
    obtain ⟨K, hK⟩ := hD
    have h_bound (n) : h n ≤ (C + 1) ^ (D * n + K) :=
      (hh n).trans (Nat.le_trans ( Nat.pow_le_pow_left ( Nat.le_succ_of_le ( hC n ) ) _ )
        ( Nat.pow_le_pow_right ( by linarith ) ( hK n ) ) ) |> le_trans <| by norm_num
    use (C + 1) ^ D
    apply Asymptotics.IsBigO.of_bound ((C + 1) ^ K)
    refine Filter.eventually_atTop.mpr ⟨0, fun n hn => ?_⟩
    simp only [norm_natCast, Nat.cast_pow, Nat.cast_add, Nat.cast_one, norm_pow]
    convert h_bound n using 1
    norm_cast
    ring_nf!
    erw [Real.norm_of_nonneg (by positivity)]
    norm_cast
  · intro h ⟨C, hC⟩
    simp only [mem_pow]
    -- Choose f to be a constant function such that f(n) = D for some D ≥ C
    obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ n, h n ≤ D ^ (n + 1) := by
      obtain ⟨D, ⟨K, hK⟩⟩ := bigO_implies_bound hC;
      use D + K + C + 1
      intro n
      specialize hK n
      ring_nf at hK ⊢
      nlinarith [pow_pos (by lia : 0 < 1 + D + C + K) n,
        pow_le_pow_left' (by lia : C ≤ 1 + D + C + K) n]
    refine ⟨D, const_mem_const D, fun n => n + 1, ?_, hD⟩
    apply Asymptotics.isBigO_iff.mpr
    simp only [norm, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one,
      id_eq, Nat.abs_cast, Filter.eventually_atTop]
    exact ⟨2, 1, fun n hn => by norm_cast; lia⟩

@[simp]
theorem primitiveRecursive_pow_self :
    primitiveRecursive ^ primitiveRecursive = primitiveRecursive := by
  apply le_antisymm
  · intro f hf
    obtain ⟨f₁, hf₁, f₂, hf₂, hf⟩ := hf
    have h_exp : ∀ f g : ℕ → ℕ, f ∈ primitiveRecursive → g ∈ primitiveRecursive →
        (fun n ↦ f n ^ g n) ∈ primitiveRecursive := by
      rintro f g ⟨hf₁, hf₂, hf₃⟩ ⟨hg₁, hg₂, hg₃⟩
      obtain ⟨C₁, N₁, hC₁⟩ : ∃ C₁ N₁, ∀ n ≥ N₁, f n ≤ C₁ * hf₁ n := by
        obtain ⟨C₁, hC₁, hC₁_bound⟩ := hf₃.exists_pos
        use ⌈C₁⌉₊
        rcases Filter.eventually_atTop.mp hC₁_bound.bound with ⟨N₁, hN₁⟩
        use N₁
        intros n hn
        specialize hN₁ n hn
        norm_num at hN₁ ⊢
        apply Nat.le_of_lt_succ
        rw [← @Nat.cast_lt ℝ]
        push_cast
        nlinarith [Nat.le_ceil C₁, show (0 : ℝ) ≤ hf₁ n from Nat.cast_nonneg _]
      obtain ⟨C₂, N₂, hC₂⟩ : ∃ C₂ N₂, ∀ n ≥ N₂, g n ≤ C₂ * hg₁ n := by
        have ⟨C₂, hC₂, hC₂_bound⟩ := hg₃.exists_pos
        use ⌈C₂⌉₊
        simp_all only [Asymptotics.IsBigOWith, norm_natCast, Filter.eventually_atTop]
        rcases hC₂_bound with ⟨N₂, hN₂⟩
        refine ⟨N₂, fun n h ↦ ?_⟩
        exact mod_cast (hN₂ n h).trans <| mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
      obtain ⟨M, hM⟩ : ∃ M, ∀ n < max N₁ N₂, f n ^ g n ≤ M := by
        use ∑ n ∈ Finset.range (N₁ ⊔ N₂), f n ^ g n
        intro n hn
        exact Finset.single_le_sum (fun n _ ↦ (f n ^ g n).zero_le) (Finset.mem_range.mpr hn)
      refine ⟨fun n ↦ (C₁ * hf₁ n + 1) ^ (C₂ * hg₁ n + 1) + M, ?_, ?_⟩
      · suffices h_primrec : Nat.Primrec (fun n => (C₁ * hf₁ n + 1) ^ (C₂ * hg₁ n + 1)) from
          Nat.Primrec.of_eq (.comp .add (h_primrec.pair (.const M))) (by simp)
        have h_primrec : Nat.Primrec (fun n => C₁ * hf₁ n + 1) := by
          apply Nat.Primrec.succ.comp
          simpa using Nat.Primrec.mul.comp <| .pair (.const C₁) hf₂
        have h_primrec' : Nat.Primrec (fun n => C₂ * hg₁ n + 1) := by
          simpa using Nat.Primrec.succ.comp <| .comp .mul <| .pair (.const C₂) hg₂
        simpa using Nat.Primrec.pow.comp (h_primrec.pair h_primrec')
      · refine Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩
        filter_upwards [Filter.eventually_ge_atTop N₁, Filter.eventually_ge_atTop N₂] with n hn₁ hn₂
        simp only [Nat.cast_pow, norm_pow, norm_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
          one_mul]
        erw [Real.norm_of_nonneg (by positivity)]
        norm_cast
        specialize hC₁ n hn₁
        specialize hC₂ n hn₂
        exact le_add_of_le_of_nonneg ((Nat.pow_le_pow_left (by lia) _).trans
          (Nat.pow_le_pow_right (by positivity) (by lia))) (by positivity)
    exact mono (h_exp f₁ f₂ hf₁ hf₂) hf
  · intro f hf
    use f, hf, fun _ => 1
    simp only [primitiveRecursive, Set.mem_setOf_eq, pow_one, Std.le_refl, and_true]
    use  1
    simp only [bigO, Pi.one_apply, Nat.cast_one, Asymptotics.isBigO_one_iff, norm_natCast,
      Set.mem_setOf_eq]
    exact ⟨Nat.Primrec.const 1, ⟨1, Filter.eventually_atTop.mpr ⟨0, fun _ _ ↦ by simp⟩⟩⟩

@[simp]
theorem computable_pow_self : computable ^ computable = computable := by
  apply le_antisymm
  · simp only [computable]
    rintro h ⟨g, ⟨g', hg', hg⟩, h, ⟨h', hh', hh⟩, hf⟩
    have ⟨C₁, C₂, K₁, K₂, h_bound⟩ : ∃ C₁ C₂ K₁ K₂ : ℕ,
        ∀ n, g n ≤ C₁ * g' n + K₁ ∧ h n ≤ C₂ * h' n + K₂ := by
      have := bigO_implies_bound hg
      have := bigO_implies_bound hh
      aesop;
    refine ⟨fun n ↦ (C₁ * g' n + K₁ + 1) ^ (C₂ * h' n + K₂ + 1), ?_, ?_⟩
    · refine .comp (Primrec₂.unpaired'.mp .pow |>.to_comp) <|
        .pair ((computable_affine C₁ (K₁ + 1)).comp hg') ((computable_affine C₂ (K₂ + 1)).comp hh')
    · apply Asymptotics.IsBigO.of_bound 1
      simp only [norm_natCast, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_one, norm_pow,
        one_mul, Filter.eventually_atTop, ge_iff_le]
      refine ⟨1, fun n hn ↦ ?_⟩
      norm_cast
      trans ↑((C₁ * g' n + K₁) ^ h n)
      · exact Nat.cast_le.mpr (hf n |>.trans (Nat.pow_le_pow_left (h_bound n).1 _))
      · simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, norm, Nat.cast_one, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_one]
        exact_mod_cast (Nat.pow_le_pow_left (by lia) _).trans
          (Nat.pow_le_pow_right (by positivity) (by linarith [h_bound n]))
  · intro h
    simp only [computable, Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro f hf hx
    exact ⟨_, ⟨f, hf, hx⟩, _, ⟨1, Computable.const 1, Asymptotics.isBigO_refl ..⟩, by simp⟩

end closure_comp

end GrowthRate

end CSLib
