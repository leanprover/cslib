/-
Copyright (c) 2026 Bashar Hamade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Bashar Hamade
-/

import Cslib.Init
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Exponential

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Order.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.Algebra.Algebra.Bilinear



--set_option diagnostics true
open scoped ComplexOrder

-- Trace instance synthesis to debug
--set_option trace.Meta.synthInstance true

-- Test if we can check the instance
#check (by infer_instance : NormedField ℂ)
/-!
# Cayley-Hamilton implications for Controllability

Auxiliary results based on the Cayley-Hamilton theorem for proving controllability results.
-/
set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.deprecated.module false

variable {σ ι : Type*}
variable [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι]
variable [Inhabited ι]



/-- Power definition: A^(k+1) = A^k * A. -/
lemma system_power_multiplication (a : σ →L[ℂ] σ) (k : ℕ) :
    a ^ (k + 1) = (a ^ k).comp a := by
  induction k with
  | zero =>
    simp [pow_zero]
    exact ContinuousLinearMap.id_comp a

  | succ k ih =>
    rw [pow_succ]
    rw [ih]
    rfl

/-- Power definition commutation: A^(k+1) = A * A^k. -/
lemma system_power_multiplication_flopped (a : σ →L[ℂ] σ) (k : ℕ) :
    a ^ (k + 1) = a.comp (a^k) := by
  induction k with
  | zero =>
    simp [pow_zero]
    exact ContinuousLinearMap.id_comp a

  | succ k ih =>
    rw [pow_succ]
    rw [ih]

    simp only [←ContinuousLinearMap.mul_def]
    rw [mul_assoc]

    congr 1



/-- Commutativity helper: A (A^i B v) = A^(i+1) B v. -/
lemma helper1 [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) (i : Fin n) (v : ι) :
    a.toLinearMap ((a ^ i.val) (B v)) = (a ^ (i.val + 1)) (B v) := by

    simp only [system_power_multiplication_flopped]
    rfl



/-- The degree of the characteristic polynomial equals the dimension of the space. -/
lemma helper2 [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ)  (n : ℕ) (h_dim : Module.finrank ℂ σ = n) :
    a.toLinearMap.charpoly.natDegree = n := by
  rw [← h_dim]
  exact LinearMap.charpoly_natDegree a.toLinearMap

/-- By Cayley-Hamilton, A^n can be expressed as a linear combination of lower powers. -/
lemma helper3 [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ)  (n : ℕ) (h_dim : Module.finrank ℂ σ = n) :
    ∃ (c : Fin n → ℂ), a.toLinearMap ^ n = ∑ j : Fin n, c j • (a.toLinearMap ^ j.val) := by

  let p := a.toLinearMap.charpoly

  have ch : Polynomial.aeval a.toLinearMap p = 0 := LinearMap.aeval_self_charpoly _
  have deg_p : p.natDegree = n := by rw [← h_dim]; exact LinearMap.charpoly_natDegree _
  have monic_p : p.Monic := LinearMap.charpoly_monic _
  have lead_coeff : p.coeff n = 1 := by rw [← deg_p]; exact monic_p.leadingCoeff

  use fun j => -(p.coeff j.val)
  simp only [neg_smul]


  rw [Finset.sum_neg_distrib]

  have expand : Polynomial.aeval a.toLinearMap p =
      a.toLinearMap ^ n + ∑ j : Fin n, p.coeff j.val • a.toLinearMap ^ j.val := by
    rw [Polynomial.aeval_eq_sum_range, deg_p, Finset.sum_range_succ]
    rw [lead_coeff, one_smul, add_comm]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i => p.coeff i • a.toLinearMap ^ i) n).symm

  rw [expand] at ch
  exact eq_neg_of_add_eq_zero_left ch


/-- The span of the controllability vectors is invariant under A. -/
lemma controllabilityColumnSpace_invariant [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) (h_dim : Module.finrank ℂ σ = n) :
    Submodule.map a.toLinearMap
    (Submodule.span ℂ (⋃ i : Fin n, Set.range (fun v => (a ^ i.val) (B v)))) ≤
    Submodule.span ℂ (⋃ i : Fin n, Set.range (fun v => (a ^ i.val) (B v))):= by





  rw [Submodule.map_span_le]


  intro x hx


  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hx⟩ := hx
  simp only [Set.mem_range] at hx
  obtain ⟨v, rfl⟩ := hx




  by_cases h : i.val + 1 < n
  · have : (a.toLinearMap ((a ^ i.val) (B v))) = (a ^ (i.val + 1)) (B v) := by
      apply helper1 a B n i v

    rw [this]
    apply Submodule.subset_span
    simp only [Set.mem_iUnion]
    use ⟨i.val + 1, h⟩
    simp only [Set.mem_range]
    use v

  · push_neg at h


    have ch := LinearMap.aeval_self_charpoly a.toLinearMap


    have deg_ch : a.toLinearMap.charpoly.natDegree = n := by
      apply helper2 a  n h_dim


    have i_eq : i.val = n - 1 := by
      have : i.val < n := i.prop
      omega





    have : ∃ (c : Fin n → ℂ), a.toLinearMap ^ n = ∑ j : Fin n, c j • (a.toLinearMap ^ j.val) := by


      apply helper3 a  n h_dim

    obtain ⟨c, hc⟩ := this


    have h_apply : (a ^ n) (B v) = ∑ j : Fin n, c j • ((a ^ j.val) (B v)) := by
      have pow_eq : ∀ k x, (a ^ k) x = (a.toLinearMap ^ k) x := fun k x => by
        induction k with
        | zero => simp [pow_zero]
        | succ k ih =>

          simp [pow_succ', ih]



      rw [pow_eq n]
      rw [congrFun (congrArg DFunLike.coe hc) (B v)]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      congr 1
      ext j
      rw [← pow_eq j.val]


    rw [i_eq]
    have : a.toLinearMap ((a ^ (n - 1)) (B v)) = (a ^ n) (B v) := by
      have hn : n = n - 1 + 1 := by omega
      conv_rhs => rw [hn, pow_succ']
      rfl

    rw [this, h_apply]


    apply Finset.sum_induction _ (· ∈ Submodule.span ℂ _)
    · exact fun _ _ => Submodule.add_mem _
    · exact Submodule.zero_mem _
    · intro j _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp only [Set.mem_iUnion]
      use j
      simp only [Set.mem_range]
      use v

/-- Main Lemma: Higher powers A^j (j ≥ n) lie in the span of the first n powers. -/
theorem cayley_hamilton_controllability' [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) (hn : n > 0)
    (h_dim : Module.finrank ℂ σ = n) :
    ∀ j ≥ n, ∀ v : ι, (a ^ j) (B v)
    ∈ Submodule.span ℂ (⋃ i : Fin n, Set.range (fun v => (a ^ i.val) (B v))) := by
  intro j hj v
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hjn : j < n
    · apply Submodule.subset_span
      simp only [Set.mem_iUnion, Set.mem_range]


      exact ⟨⟨j, hjn⟩, v, rfl⟩

    · push_neg at hjn
      by_cases hj_zero : j = 0
      · omega
      · have hj_pos : j > 0 := Nat.pos_of_ne_zero hj_zero
        have : j = (j - 1) + 1 := by
          omega

        rw [this, pow_succ', ContinuousLinearMap.mul_apply]
        apply controllabilityColumnSpace_invariant a B n h_dim
        apply Submodule.mem_map_of_mem
        have h_pred_ge : j - 1 ≥ n ∨ j - 1 < n := by
          by_cases h : j - 1 ≥ n
          · left; exact h
          · right; push_neg at h; exact h


        cases h_pred_ge with
        | inl h_ge =>
          apply ih
          omega
          exact h_ge
        | inr h_lt =>


          apply Submodule.subset_span
          simp only [Set.mem_iUnion, Set.mem_range]
          exact ⟨⟨j - 1, h_lt⟩, v, rfl⟩
