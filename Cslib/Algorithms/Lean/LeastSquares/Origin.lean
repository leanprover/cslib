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

namespace Cslib.Algorithms.Lean.LeastSquares.Origin

variable {n : ℕ}

/-- `Sxx = ∑ xᵢ²`. -/
noncomputable def Sxx (x : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => (x i) ^ 2)

/-- `Sxy = ∑ xᵢ yᵢ`. -/
noncomputable def Sxy (x y : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => x i * y i)

/-- Least-squares slope through the origin: `a* = Sxy / Sxx`. -/
noncomputable def aStar (x y : Fin n → ℝ) : ℝ :=
  (Sxy x y) / (Sxx x)

/-- Squared loss: `loss(a) = ∑ (a xᵢ - yᵢ)²`. -/
noncomputable def loss (x y : Fin n → ℝ) (a : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => (a * x i - y i) ^ 2)

lemma Sxx_nonneg (x : Fin n → ℝ) : 0 ≤ Sxx x := by
  classical
  unfold Sxx
  refine Finset.induction_on (s := (Finset.univ : Finset (Fin n))) ?base ?step
  · simp
  · intro a s ha hs
    have hxa : 0 ≤ (x a) ^ 2 := sq_nonneg (x a)
    simpa [Finset.sum_insert, ha] using add_nonneg hxa hs

/-- Normal equation: the cross term vanishes at `aStar`. -/
lemma crossTerm_eq_zero (x y : Fin n → ℝ) (h : Sxx x ≠ 0) :
    (Finset.univ : Finset (Fin n)).sum
        (fun i => x i * (aStar x y * x i - y i)) = 0 := by
  classical
  let U : Finset (Fin n) := Finset.univ
  have hrewrite :
      U.sum (fun i => x i * (aStar x y * x i - y i))
        =
      aStar x y * (U.sum (fun i => (x i) ^ 2))
        - (U.sum (fun i => x i * y i)) := by
    calc
      U.sum (fun i => x i * (aStar x y * x i - y i))
          =
        U.sum (fun i => aStar x y * (x i) ^ 2 - x i * y i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [pow_two]
          ring_nf
      _ =
        U.sum (fun i => aStar x y * (x i) ^ 2)
          - U.sum (fun i => x i * y i) := by
          -- direct lemma; no simp/simpa needed
          exact Finset.sum_sub_distrib
            (s := U)
            (f := fun i => aStar x y * (x i) ^ 2)
            (g := fun i => x i * y i)
      _ =
        aStar x y * (U.sum (fun i => (x i) ^ 2))
          - U.sum (fun i => x i * y i) := by
          have hm :
              U.sum (fun i => aStar x y * (x i) ^ 2)
                =
              aStar x y * (U.sum (fun i => (x i) ^ 2)) :=
            (Finset.mul_sum
              (s := U)
              (f := fun i => (x i) ^ 2)
              (a := aStar x y)).symm
          simp [hm]
  calc
    (Finset.univ : Finset (Fin n)).sum
          (fun i => x i * (aStar x y * x i - y i))
        =
      aStar x y * (U.sum (fun i => (x i) ^ 2))
        - (U.sum (fun i => x i * y i)) := by
          simpa [U] using hrewrite
    _ = 0 := by
      -- Clear denominators: (Sxy/Sxx)*Sxx - Sxy = 0
      simp [aStar, Sxx, Sxy, U] at h ⊢
      field_simp [h]
      ring_nf

/-- Loss decomposition around `aStar` (regression through the origin). -/
lemma loss_decomp (x y : Fin n → ℝ) (h : Sxx x ≠ 0) (a : ℝ) :
    loss x y a =
      loss x y (aStar x y) + (Sxx x) * (a - aStar x y) ^ 2 := by
  classical
  let U : Finset (Fin n) := Finset.univ
  let a0 : ℝ := aStar x y
  let d : ℝ := a - a0
  have hterm : ∀ i : Fin n, a * x i - y i = d * x i + (a0 * x i - y i) := by
    intro i
    simp [d, sub_eq_add_neg, a0]
    ring_nf
  have hcross : U.sum (fun i => x i * (a0 * x i - y i)) = 0 := by
    simpa [a0, U] using crossTerm_eq_zero (x := x) (y := y) h
  have hexpand :
      U.sum (fun i => (a * x i - y i) ^ 2)
        =
      U.sum (fun i =>
        (d ^ 2) * (x i) ^ 2
        + (a0 * x i - y i) ^ 2
        + (2 * d) * (x i * (a0 * x i - y i))) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have ht := hterm i
    simp [ht, pow_two]
    ring_nf
  let A : Fin n → ℝ := fun i => (d ^ 2) * (x i) ^ 2
  let B : Fin n → ℝ := fun i => (a0 * x i - y i) ^ 2
  let C : Fin n → ℝ := fun i => (2 * d) * (x i * (a0 * x i - y i))
  have hsplit :
      U.sum (fun i => A i + B i + C i)
        =
      (U.sum A + U.sum B) + U.sum C := by
    have h1 :
        U.sum (fun i => (A i + B i) + C i)
          =
        U.sum (fun i => A i + B i) + U.sum C := by
      simpa using
        (Finset.sum_add_distrib
          (s := U)
          (f := fun i => A i + B i)
          (g := C))
    have h2 :
        U.sum (fun i => A i + B i) = U.sum A + U.sum B := by
      simpa using (Finset.sum_add_distrib (s := U) (f := A) (g := B))
    calc
      U.sum (fun i => A i + B i + C i)
          = U.sum (fun i => (A i + B i) + C i) := by rfl
      _ = U.sum (fun i => A i + B i) + U.sum C := h1
      _ = (U.sum A + U.sum B) + U.sum C := by simp [h2]
  have hA : U.sum A = (d ^ 2) * (U.sum (fun i => (x i) ^ 2)) := by
    -- unfold A, then it matches `mul_sum` exactly
    dsimp [A]
    exact (Finset.mul_sum (s := U) (f := fun i => (x i) ^ 2) (a := d ^ 2)).symm
  have hC :
      U.sum C
        =
      (2 * d) * (U.sum (fun i => x i * (a0 * x i - y i))) := by
    dsimp [C]
    exact (Finset.mul_sum
      (s := U)
      (f := fun i => x i * (a0 * x i - y i))
      (a := 2 * d)).symm
  unfold loss
  calc
    (Finset.univ : Finset (Fin n)).sum (fun i => (a * x i - y i) ^ 2)
        = U.sum (fun i => (a * x i - y i) ^ 2) := by rfl
    _ = U.sum (fun i =>
          (d ^ 2) * (x i) ^ 2
          + (a0 * x i - y i) ^ 2
          + (2 * d) * (x i * (a0 * x i - y i))) := hexpand
    _ = U.sum (fun i => A i + B i + C i) := by rfl
    _ = (U.sum A + U.sum B) + U.sum C := hsplit
    _ = ((d ^ 2) * (U.sum (fun i => (x i) ^ 2)) + U.sum B)
          + (2 * d) * (U.sum (fun i => x i * (a0 * x i - y i))) := by
          simp [hA, hC]
    _ = ((d ^ 2) * (U.sum (fun i => (x i) ^ 2)) + U.sum B) + (2 * d) * 0 := by
          simp [hcross]
    _ = U.sum B + (U.sum (fun i => (x i) ^ 2)) * (d ^ 2) := by
          -- just algebraic rearrangement
          ring_nf
    _ = (Finset.univ : Finset (Fin n)).sum (fun i => (a0 * x i - y i) ^ 2)
          + (Sxx x) * (a - a0) ^ 2 := by
          simp [U, Sxx, d, B]
    _ = loss x y a0 + (Sxx x) * (a - a0) ^ 2 := by
          simp [loss]
    _ = loss x y (aStar x y) + (Sxx x) * (a - aStar x y) ^ 2 := by
          simp [a0]

/-- `aStar` minimizes the squared loss (regression through the origin). -/
theorem aStar_minimizes (x y : Fin n → ℝ) (h : Sxx x ≠ 0) :
    ∀ a : ℝ, loss x y (aStar x y) ≤ loss x y a := by
  classical
  intro a
  have hdecomp := loss_decomp (x := x) (y := y) h a
  have hnonneg : 0 ≤ (Sxx x) * (a - aStar x y) ^ 2 :=
    mul_nonneg (Sxx_nonneg (x := x)) (sq_nonneg (a - aStar x y))
  calc
    loss x y (aStar x y)
        ≤ loss x y (aStar x y) + (Sxx x) * (a - aStar x y) ^ 2 := by
          exact le_add_of_nonneg_right hnonneg
    _ = loss x y a := by
          exact hdecomp.symm

end Cslib.Algorithms.Lean.LeastSquares.Origin
