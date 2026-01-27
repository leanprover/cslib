import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Order.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Cslib.Init
import Cslib.CPS.DiscreteLinearTime.Basic
import Cslib.CPS.DiscreteLinearTime.Cayley


/-
Copyright (c) 2026 Bashar Hamade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bashar Hamade
-/

/-!
# Asymptotic Stability Analysis

This module analyzes the asymptotic stability of discrete-time linear systems.
It uses the Gelfand spectral radius formula to show that if the
spectral radius of the system matrix is less than one,
the state converges to zero under zero input.

## Main Theorems
* `asymptotic_stability_discrete`: The main stability theorem.
* `gelfand_le_one_when_spectral_radius_le_one`: Relates spectral radius to Gelfand limit.
-/




open scoped ComplexOrder

variable {σ ι : Type*}
variable [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [NormedAddCommGroup ι] [NormedSpace ℂ ι]




/-- System evolution function. -/
noncomputable def system_evolution (sys : DiscreteLinearSystemState σ ι) : ℕ → σ
  | 0 => sys.x₀
  | k + 1 => sys.a (system_evolution sys k) + sys.B (sys.u k)

/-- Discrete State space representation property. -/
def state_system_equation (sys : DiscreteLinearSystemState σ ι) : Prop :=
  ∀ k : ℕ, sys.x (k + 1) = sys.a (sys.x k) + sys.B (sys.u k)







/-- Lemma: State evolution under zero input. -/
lemma state_evolution_zero_input (sys : DiscreteLinearSystemState σ ι)
 (h_init : sys.x 0 = sys.x₀)
 (h_state : state_system_equation sys)
 (h_zero_input : sys.u = zero_input) :
 ∀ k, sys.x k = (sys.a ^ k) sys.x₀ := by
  intro k
  induction k with
 | zero =>
   simp [pow_zero, h_init]
 | succ k ih =>
   have h1 : sys.x (k + 1) = sys.a (sys.x k) + sys.B (sys.u k) := h_state k
   rw [ih] at h1
   rw [h_zero_input] at h1
   unfold zero_input at h1
   simp only [ContinuousLinearMap.map_zero, add_zero] at h1
   rw [h1]
   rw [←ContinuousLinearMap.comp_apply]
   congr 1
   rw [system_power_multiplication_flopped]






/-- Bound on state norm. -/
theorem bound_x_norm
    (sys : DiscreteLinearSystemState σ ι)
    (hx : ∀ k, sys.x k = (sys.a ^ k) sys.x₀) (N : ℕ) :
    ∀ k, N < k → ‖sys.x k‖ ≤ ‖sys.a ^ k‖ * ‖sys.x₀‖ := by
  intro k hk
  rw [hx k]
  exact ContinuousLinearMap.le_opNorm (sys.a ^ k) sys.x₀

/-- Spectral radius strictly less than one. -/
def spectral_radius_less_than_one (a : σ →L[ℂ] σ) : Prop :=
  spectralRadius ℂ a < 1

/-- If the spectral radius of `a` is less than one, then the
Gelfand formula limits to less than one. -/
theorem gelfand_le_one_when_spectral_radius_le_one
    [CompleteSpace σ] (a : σ →L[ℂ] σ) :
    spectral_radius_less_than_one a →
    Filter.limsup (fun (n : ℕ) => (‖a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1 := by
  intro h_spectral
  unfold spectral_radius_less_than_one at h_spectral
  have h_gelfand := spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius a
  convert lt_of_le_of_lt h_gelfand h_spectral



/-- If the Gelfand limit is < 1, then eventually the root-term is bounded by some `r < 1`. -/
theorem gelfand_eventually_bounded [CompleteSpace σ]
    (a : σ →L[ℂ] σ) (h : Filter.limsup (fun n :
    ℕ ↦ (‖a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1) :
    ∃ (r : ENNReal) (N : ℕ), 0 < r ∧ r < 1
    ∧ ∀ (k : ℕ), N < k → (‖a ^ k‖₊ : ENNReal) ^ (1 / k : ℝ) < r :=
by
  obtain ⟨r, h_limsup_lt_r, h_r_lt_one⟩ := exists_between h
  have r_pos : 0 < r := lt_of_le_of_lt (zero_le _) h_limsup_lt_r
  have eventually_lt := Filter.eventually_lt_of_limsup_lt h_limsup_lt_r
  rw [Filter.eventually_atTop] at eventually_lt
  obtain ⟨N, hN⟩ := eventually_lt
  use r, N
  refine ⟨r_pos, h_r_lt_one, fun k hk => hN k (Nat.le_of_lt hk)⟩


/-- If terms are eventually bounded by `r^k` with `r < 1`, the sequence tends to zero. -/
theorem power_to_zero [CompleteSpace σ] (sys : DiscreteLinearSystemState σ ι)
  (r : ENNReal) (N : ℕ)
  (r_pos : 0 < r)
  (r_lt_one : r < 1)
  (h_power : ∀ (k : ℕ), N < k → (‖sys.a ^ k‖₊ : ENNReal) < r ^ k) :
  Filter.Tendsto (fun k => ‖sys.a ^ k‖) Filter.atTop (nhds 0) := by
  have r_real_zero : Filter.Tendsto (fun n => (r ^ n).toReal) Filter.atTop (nhds 0) := by
    simp only [ENNReal.toReal_pow, tendsto_pow_atTop_nhds_zero_iff, ENNReal.abs_toReal]
    cases r with
    | top => simp
    | coe x =>
      simp only [ENNReal.coe_toReal, NNReal.coe_lt_one]
      exact ENNReal.coe_lt_one_iff.mp r_lt_one
  rw [Metric.tendsto_atTop]
  intro ε ε_pos
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp r_real_zero ε ε_pos
  use max N N₁ + 1
  intro k hk
  have hkN : N < k := lt_of_le_of_lt (le_max_left N N₁) (Nat.lt_of_succ_le hk)
  have hkN₁ : N₁ ≤ k := le_trans (le_max_right N N₁) (Nat.le_of_succ_le hk)
  have h_bound := h_power k hkN
  have h_r_small := hN₁ k hkN₁
  simp only [dist_zero_right, norm_norm, gt_iff_lt]
  simp only [ENNReal.toReal_pow, dist_zero_right, norm_pow, Real.norm_eq_abs,
    ENNReal.abs_toReal] at h_r_small
  have h_r_ennreal : (r ^ k).toReal < ε := by
    rw [ENNReal.toReal_pow]
    exact h_r_small
  have h_finite : (r ^ k) ≠ ⊤ := by
    simp only [ne_eq, ENNReal.pow_eq_top_iff]
    intro h
    cases h with
    | intro h_r_top h_k_ne_zero =>
      have : r < ⊤ := r_lt_one.trans_le le_top
      exact ne_of_lt this h_r_top
  calc ‖sys.a ^ k‖
  = (‖sys.a ^ k‖₊ : ℝ) := by simp
  _ = (↑‖sys.a ^ k‖₊ : ENNReal).toReal := by simp
  _ < (r ^ k).toReal := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top h_finite).mpr h_bound
  _ < ε := h_r_ennreal






/-- Main theorem: Asymptotic Stability. If the spectral radius is < 1,
the zero-input response converges to zero. -/
theorem asymptotic_stability_discrete [CompleteSpace σ] (sys : DiscreteLinearSystemState σ ι)
  (h_init : sys.x 0 = sys.x₀)
  (h_state : state_system_equation sys)
  (h_zero_input : sys.u = zero_input)
  (h_spectral : spectral_radius_less_than_one sys.a) :
  Filter.Tendsto (fun k => ‖sys.x k‖) Filter.atTop (nhds 0) := by
  have h_gelfand := spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius sys.a
  have h_gelfand_le_one : Filter.limsup (fun (n : ℕ) =>
  (‖sys.a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1 := by
      unfold spectral_radius_less_than_one at h_spectral
      refine lt_of_le_of_lt ?_ h_spectral
      exact h_gelfand
  have eventually_bounded := gelfand_eventually_bounded sys.a h_gelfand_le_one
  obtain ⟨r, N, r_pos, r_lt_one, h_bound⟩ := eventually_bounded
  have h_power : ∀ (k : ℕ), N < k → ↑‖sys.a ^ k‖₊ < r ^ k := by
      intros k' hk'
      specialize h_bound k' hk'
      have h_k'_pos : 0 < k' := Nat.zero_lt_of_lt hk'
      have h_inv_k' : (k' : ℝ)⁻¹ * k' = 1 := by
        field_simp
      have h_pow : (↑‖sys.a ^ k'‖₊ ^ (1 / k' : ℝ)) ^ (k' : ℝ) < r ^ k' := by
        rw [← ENNReal.rpow_natCast r k']
        exact ENNReal.rpow_lt_rpow h_bound (Nat.cast_pos.mpr h_k'_pos)
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h_pow
      simp only [one_div, ENNReal.rpow_natCast] at h_pow
      rw [h_inv_k'] at h_pow
      simp only [ENNReal.rpow_one] at h_pow
      exact h_pow
  have hx : ∀ k, sys.x k = (sys.a ^ k) sys.x₀ :=
      state_evolution_zero_input sys h_init h_state h_zero_input
  have pow_zero : Filter.Tendsto (fun k => ‖sys.a ^ k‖) Filter.atTop (nhds 0) :=
      power_to_zero sys r N r_pos r_lt_one h_power
  simp only [hx]
  have h_norm_eq : ∀ k, ‖(sys.a ^ k) sys.x₀‖ ≤ ‖sys.a ^ k‖ * ‖sys.x₀‖ :=
    fun k => ContinuousLinearMap.le_opNorm (sys.a ^ k) sys.x₀
  have h_prod_zero : Filter.Tendsto (fun k => ‖sys.a ^ k‖ * ‖sys.x₀‖) Filter.atTop (nhds 0) := by
    rw [← zero_mul ‖sys.x₀‖]
    exact Filter.Tendsto.mul_const ‖sys.x₀‖ pow_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds)
    h_prod_zero
    (fun k => norm_nonneg _)
    h_norm_eq
