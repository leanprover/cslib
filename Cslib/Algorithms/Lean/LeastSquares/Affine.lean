/- Copyright (c) 2026 Alisson Matheus Silva. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alisson Matheus Silva -/
module
public import Cslib.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LeastSquares.General

variable {n : ℕ}

/-- `Sx = ∑ xᵢ`. -/
noncomputable def Sx (x : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum x

/-- `Sy = ∑ yᵢ`. -/
noncomputable def Sy (y : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum y

/-- `Sxx = ∑ xᵢ²`. -/
noncomputable def Sxx (x : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => (x i) ^ 2)

/-- `Sxy = ∑ xᵢ yᵢ`. -/
noncomputable def Sxy (x y : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => x i * y i)

/-- `Stt = ∑ (xᵢ - x̄)²`, the total sum of squares of the centered predictor.
This plays the role that `Sxx` plays in the origin case. -/
noncomputable def Stt (x : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum
    (fun i => (x i - Sx x / n) ^ 2)

/-- Least-squares slope: `aStar = (n * Sxy - Sx * Sy) / Stt`. -/
noncomputable def aStar (x y : Fin n → ℝ) : ℝ :=
  (n * Sxy x y - Sx x * Sy y) / Stt x

/-- Least-squares intercept: `bStar = (Sy - aStar * Sx) / n`. -/
noncomputable def bStar (x y : Fin n → ℝ) : ℝ :=
  (Sy y - aStar x y * Sx x) / n

/-- Squared loss for the affine model: `loss(a, b) = ∑ (a * xᵢ + b - yᵢ)²`. -/
noncomputable def loss (x y : Fin n → ℝ) (a b : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => (a * x i + b - y i) ^ 2)

lemma Stt_nonneg (x : Fin n → ℝ) : 0 ≤ Stt x := by
  unfold Stt
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg _

lemma Sxx_nonneg (x : Fin n → ℝ) : 0 ≤ Sxx x := by
  unfold Sxx
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg _

/-- `Stt x = n * Sxx x - (Sx x) ^ 2`. -/
lemma Stt_eq (x : Fin n → ℝ) :
    Stt x = n * Sxx x - (Sx x) ^ 2 := by
  sorry

/-- First normal equation: the slope cross term vanishes at `(aStar, bStar)`. -/
lemma crossTerm_slope_eq_zero (x y : Fin n → ℝ) (h : Stt x ≠ 0) :
    (Finset.univ : Finset (Fin n)).sum
        (fun i => x i * (aStar x y * x i + bStar x y - y i)) = 0 := by
  sorry

/-- Second normal equation: the intercept cross term vanishes at `(aStar, bStar)`. -/
lemma crossTerm_intercept_eq_zero (x y : Fin n → ℝ) (h : Stt x ≠ 0) :
    (Finset.univ : Finset (Fin n)).sum
        (fun i => aStar x y * x i + bStar x y - y i) = 0 := by
  sorry

/-- Loss decomposition around `(aStar, bStar)`:
    `loss a b = loss aStar bStar + Stt * (a - aStar)² + n * (b - bStar)²`. -/
lemma loss_decomp (x y : Fin n → ℝ) (h : Stt x ≠ 0) (a b : ℝ) :
    loss x y a b =
      loss x y (aStar x y) (bStar x y)
        + Stt x * (a - aStar x y) ^ 2
        + n * (b - bStar x y) ^ 2 := by
  sorry

/-- `(aStar, bStar)` jointly minimize the squared loss over all affine fits. -/
theorem aStar_minimizes (x y : Fin n → ℝ) (h : Stt x ≠ 0) :
    ∀ a b : ℝ, loss x y (aStar x y) (bStar x y) ≤ loss x y a b := by
  intro a b
  have hdecomp := loss_decomp (x := x) (y := y) h a b
  have h1 : 0 ≤ Stt x * (a - aStar x y) ^ 2 :=
    mul_nonneg (Stt_nonneg x) (sq_nonneg _)
  have h2 : 0 ≤ (n : ℝ) * (b - bStar x y) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
  linarith [hdecomp]

end Cslib.Algorithms.Lean.LeastSquares.General
