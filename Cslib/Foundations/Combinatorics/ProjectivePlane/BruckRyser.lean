/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.Configuration
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.SumFourSquares
public import Mathlib.NumberTheory.SumTwoSquares

/-!
# The Bruck–Ryser theorem

The Bruck–Ryser theorem states that if a finite projective plane has order `n` congruent to `1` or
`2` modulo `4`, then `n` is a sum of two squares. In particular no projective plane has order
`2 * 3 ^ (2 * k + 1)`, so there are infinitely many natural numbers that are not the order of any
projective plane.

This module is deliberately restricted to projective planes, and does not develop the
Bruck–Ryser–Chowla theorem for symmetric designs.

## Proof outline

Let `N = n ^ 2 + n + 1` be the number of points. For rational variables `x p` indexed by the points
and `z l = ∑ p ∈ l, x p` indexed by the lines, counting incidences gives
`∑ l, z l ^ 2 = n * ∑ p, x p ^ 2 + (∑ p, x p) ^ 2`. Adjoin one more variable on each side, so that
the number of variables is divisible by four. Writing `n` as a sum of four squares, Euler's
four-square identity provides a linear change of variables `y ↦ x` with
`n * ∑ i, x i ^ 2 = ∑ j, y j ^ 2`. The `z l` are then linear forms in the `y j`, and it is possible
to choose `y` with last coordinate `1` such that `z l ^ 2 = y l ^ 2` for every line `l`
(`Cslib.exists_sq_eq_sq_of_linearMap`). What remains of the identity is `n * q ^ 2 = 1 + r ^ 2` for
rational numbers `q` and `r`, which forces `n` to be a sum of two squares.

The classical proof chooses the coordinates of `y` one at a time. We instead use that for every
square matrix `C` over a field of characteristic different from two there is a diagonal matrix `E`
with entries `±1` such that `C - E` is invertible
(`Cslib.exists_det_sub_diagonal_ne_zero`).

## References

* [R. H. Bruck and H. J. Ryser, *The nonexistence of certain finite projective planes*]
  [BruckRyser1949]
* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

namespace Cslib

open Matrix

section SignLemma

variable {K : Type*} [Field K] [NeZero (2 : K)]

private theorem exists_det_sub_diagonal_ne_zero_fin :
    ∀ (k : ℕ) (C : Matrix (Fin k) (Fin k) K),
      ∃ ε : Fin k → K, (∀ i, ε i = 1 ∨ ε i = -1) ∧ (C - diagonal ε).det ≠ 0
  | 0, C => ⟨fun _ => 1, fun _ => .inl rfl, by rw [det_fin_zero]; exact one_ne_zero⟩
  | k + 1, C => by
    obtain ⟨ε, hε, hdet⟩ := exists_det_sub_diagonal_ne_zero_fin k (C.submatrix Fin.succ Fin.succ)
    have key (s : K) : (C - diagonal (Fin.cons s ε)).det =
        (C - diagonal (Fin.cons 0 ε)).det -
          s * (C.submatrix Fin.succ Fin.succ - diagonal ε).det := by
      have hrow : C - diagonal (Fin.cons s ε) = updateRow (C - diagonal (Fin.cons 0 ε)) 0
          ((C - diagonal (Fin.cons 0 ε)) 0 + (-s) • Pi.single 0 1) := by
        ext i j
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [updateRow_self]
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [sub_eq_add_neg]
          · simp [Fin.succ_ne_zero, (Fin.succ_ne_zero j).symm]
        · rw [updateRow_ne (Fin.succ_ne_zero i)]
          simp [diagonal_apply]
      have hsub : (updateRow (C - diagonal (Fin.cons 0 ε)) 0 (Pi.single 0 1)).det =
          (C.submatrix Fin.succ Fin.succ - diagonal ε).det := by
        rw [det_succ_row_zero, Fin.sum_univ_succ]
        have hzero : ∀ j : Fin k, (-1 : K) ^ (j.succ : ℕ) *
            updateRow (C - diagonal (Fin.cons 0 ε)) 0 (Pi.single 0 1) 0 j.succ *
            ((updateRow (C - diagonal (Fin.cons 0 ε)) 0 (Pi.single 0 1)).submatrix Fin.succ
              j.succ.succAbove).det = 0 := fun j => by
          rw [updateRow_self, Pi.single_eq_of_ne (Fin.succ_ne_zero j), mul_zero, zero_mul]
        rw [Finset.sum_eq_zero fun j _ => hzero j, add_zero, updateRow_self, Pi.single_eq_same,
          Fin.val_zero, pow_zero, one_mul, one_mul]
        congr 1
        ext i j
        simp [diagonal_apply]
      rw [hrow, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, hsub]
      ring
    by_cases h1 : (C - diagonal (Fin.cons 1 ε)).det = 0
    · refine ⟨Fin.cons (-1) ε, fun i => Fin.cases (.inr rfl) hε i, fun h2 => ?_⟩
      rw [key] at h1 h2
      have h : (2 : K) * (C.submatrix Fin.succ Fin.succ - diagonal ε).det = 0 := by
        linear_combination h2 - h1
      exact hdet ((mul_eq_zero.mp h).resolve_left (NeZero.ne 2))
    · exact ⟨Fin.cons 1 ε, fun i => Fin.cases (.inl rfl) hε i, h1⟩

/-- For every square matrix `C` over a field of characteristic different from two, there is a
diagonal matrix `E` with entries `1` and `-1` such that `C - E` is invertible. -/
theorem exists_det_sub_diagonal_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n K) : ∃ ε : n → K, (∀ i, ε i = 1 ∨ ε i = -1) ∧ (C - diagonal ε).det ≠ 0 := by
  let e := Fintype.equivFin n
  obtain ⟨ε, hε, hdet⟩ := exists_det_sub_diagonal_ne_zero_fin _ (C.submatrix e.symm e.symm)
  refine ⟨ε ∘ e, fun i => hε (e i), ?_⟩
  rw [← det_submatrix_equiv_self e.symm]
  convert hdet using 2
  ext i j
  simp [diagonal_apply, e.symm.injective.eq_iff]

end SignLemma

/-- Given linear forms `f i` in variables indexed by `Option ι`, one for each `i : ι`, there is an
assignment `y` of the variables with `y none = 1` such that `f i y` and `y (some i)` have the same
square for every `i`. -/
theorem exists_sq_eq_sq_of_linearMap {ι : Type*} [Finite ι]
    (f : ι → ((Option ι → ℚ) →ₗ[ℚ] ℚ)) :
    ∃ y : Option ι → ℚ, y none = 1 ∧ ∀ i, f i y ^ 2 = y (some i) ^ 2 := by
  classical
  have := Fintype.ofFinite ι
  let C : Matrix ι ι ℚ := fun i j => f i fun o => if some j = o then 1 else 0
  let c : ι → ℚ := fun i => f i fun o => if none = o then 1 else 0
  obtain ⟨ε, hε, hdet⟩ := exists_det_sub_diagonal_ne_zero C
  let u : ι → ℚ := (C - diagonal ε)⁻¹ *ᵥ (-c)
  have hu : (C - diagonal ε) *ᵥ u = -c := by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  refine ⟨fun o => o.elim 1 u, rfl, fun i => ?_⟩
  have hf : f i (fun o => o.elim 1 u) = ε i * u i := by
    have hi := congrFun hu i
    rw [sub_mulVec, Pi.sub_apply, mulVec_diagonal, Pi.neg_apply] at hi
    have hsum : ∑ j, u j * C i j = (C *ᵥ u) i := by
      simp only [mulVec, dotProduct, mul_comm]
    rw [LinearMap.pi_apply_eq_sum_univ, Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some, smul_eq_mul, one_mul]
    change c i + ∑ j, u j * C i j = ε i * u i
    rw [hsum]
    linear_combination hi
  rw [hf, mul_pow]
  rcases hε i with h | h <;> simp [h]

section FourSquares

/-- A linear map on `ℚ ^ 4` that scales the sum of squares by `1 / n`, obtained from a
representation of `n` as a sum of four squares by Euler's four-square identity. -/
private theorem exists_linearMap_sum_sq_fin_four {n : ℕ} (hn : n ≠ 0) :
    ∃ T : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ), ∀ v, (n : ℚ) * ∑ r, T v r ^ 2 = ∑ r, v r ^ 2 := by
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares n
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hq : (n : ℚ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by exact_mod_cast habcd.symm
  let F : Fin 4 → ((Fin 4 → ℚ) →ₗ[ℚ] ℚ) := ![
    (n : ℚ)⁻¹ • ((a : ℚ) • LinearMap.proj 0 - (b : ℚ) • LinearMap.proj 1 -
      (c : ℚ) • LinearMap.proj 2 - (d : ℚ) • LinearMap.proj 3),
    (n : ℚ)⁻¹ • ((a : ℚ) • LinearMap.proj 1 + (b : ℚ) • LinearMap.proj 0 +
      (c : ℚ) • LinearMap.proj 3 - (d : ℚ) • LinearMap.proj 2),
    (n : ℚ)⁻¹ • ((a : ℚ) • LinearMap.proj 2 - (b : ℚ) • LinearMap.proj 3 +
      (c : ℚ) • LinearMap.proj 0 + (d : ℚ) • LinearMap.proj 1),
    (n : ℚ)⁻¹ • ((a : ℚ) • LinearMap.proj 3 + (b : ℚ) • LinearMap.proj 2 -
      (c : ℚ) • LinearMap.proj 1 + (d : ℚ) • LinearMap.proj 0)]
  refine ⟨LinearMap.pi F, fun v => ?_⟩
  have h0 : F 0 v = (n : ℚ)⁻¹ * (a * v 0 - b * v 1 - c * v 2 - d * v 3) := rfl
  have h1 : F 1 v = (n : ℚ)⁻¹ * (a * v 1 + b * v 0 + c * v 3 - d * v 2) := rfl
  have h2 : F 2 v = (n : ℚ)⁻¹ * (a * v 2 - b * v 3 + c * v 0 + d * v 1) := rfl
  have h3 : F 3 v = (n : ℚ)⁻¹ * (a * v 3 + b * v 2 - c * v 1 + d * v 0) := rfl
  rw [Fin.sum_univ_four, Fin.sum_univ_four, LinearMap.pi_apply, LinearMap.pi_apply,
    LinearMap.pi_apply, LinearMap.pi_apply, h0, h1, h2, h3]
  field_simp
  rw [hq]
  ring

/-- For index types of the same cardinality divisible by four, there is a linear map that scales
the sum of squares by `1 / n`. -/
theorem exists_linearMap_sum_sq {I J : Type*} [Fintype I] [Fintype J]
    (hIJ : Fintype.card I = Fintype.card J) (h4 : 4 ∣ Fintype.card I) {n : ℕ} (hn : n ≠ 0) :
    ∃ T : (J → ℚ) →ₗ[ℚ] (I → ℚ), ∀ y, (n : ℚ) * ∑ i, T y i ^ 2 = ∑ j, y j ^ 2 := by
  obtain ⟨m, hm⟩ := h4
  obtain ⟨T₄, hT₄⟩ := exists_linearMap_sum_sq_fin_four hn
  have hI : Fintype.card I = Fintype.card (Fin m × Fin 4) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hm, mul_comm]
  let eI : I ≃ Fin m × Fin 4 := Fintype.equivOfCardEq hI
  let eJ : J ≃ Fin m × Fin 4 := Fintype.equivOfCardEq (hIJ ▸ hI)
  refine ⟨LinearMap.pi fun i => (LinearMap.proj (eI i).2).comp
    (T₄.comp (LinearMap.pi fun r => LinearMap.proj (eJ.symm ((eI i).1, r)))), fun y => ?_⟩
  simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [← Equiv.sum_comp eI.symm, ← Equiv.sum_comp eJ.symm (fun j => y j ^ 2), Fintype.sum_prod_type,
    Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.apply_symm_apply]
  exact hT₄ fun r => y (eJ.symm (k, r))

end FourSquares

section SumTwoSquares

/-- If `n * c ^ 2` is a sum of two squares for some nonzero `c`, then so is `n`. -/
theorem _root_.Nat.eq_sq_add_sq_of_mul_sq_eq {n a b c : ℕ} (hc : c ≠ 0)
    (h : n * c ^ 2 = a ^ 2 + b ^ 2) : ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  intro q hq hq3
  have hn : n ≠ 0 := (Nat.mem_primeFactors.mp hq).2.2
  have hprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hprime⟩
  have hmem : q ∈ (n * c ^ 2).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hprime, (Nat.dvd_of_mem_primeFactors hq).mul_right _, mul_ne_zero hn (pow_ne_zero 2 hc)⟩
  have heven := (Nat.eq_sq_add_sq_iff.mp ⟨a, b, h⟩) q hmem hq3
  rw [Nat.padicValNat_def] at heven ⊢
  rw [Nat.multiplicity_mul hn (pow_ne_zero 2 hc), Nat.multiplicity_pow] at heven
  exact (Nat.even_add.mp heven).mpr (even_two_mul _)

/-- If `n * q ^ 2 = 1 + r ^ 2` for rational numbers `q` and `r`, then `n` is a sum of two
squares. -/
theorem exists_sq_add_sq_of_rat {n : ℕ} {q r : ℚ} (h : (n : ℚ) * q ^ 2 = 1 + r ^ 2) :
    ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  have hq : q ≠ 0 := by
    rintro rfl
    have : (0 : ℚ) < 1 + r ^ 2 := by positivity
    rw [← h] at this
    simp at this
  have hqd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hrd : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_ne_zero
  refine Nat.eq_sq_add_sq_of_mul_sq_eq (c := q.num.natAbs * r.den) (a := q.den * r.den)
    (b := r.num.natAbs * q.den)
    (mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)) r.den_ne_zero) ?_
  refine Nat.cast_injective (R := ℚ) ?_
  rw [← Rat.num_div_den q, ← Rat.num_div_den r] at h
  field_simp at h
  push_cast [Nat.cast_natAbs, mul_pow, sq_abs]
  linear_combination h

end SumTwoSquares

section Plane

open Configuration ProjectivePlane

variable {P L : Type*} [Membership P L] [ProjectivePlane P L]

open scoped Classical in
/-- In a projective plane of order `n`, a point lies on `n + 1` lines and two distinct points lie
on exactly one common line. -/
theorem card_filter_mem_and_mem [Finite P] [Fintype L] (p q : P) :
    (Finset.univ.filter fun l : L => p ∈ l ∧ q ∈ l).card = if p = q then order P L + 1 else 1 := by
  split_ifs with hpq
  · subst hpq
    rw [← lineCount_eq L p, lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [and_self]
  · obtain ⟨l, hl, hl'⟩ := HasLines.existsUnique_line P L p q hpq
    refine Finset.card_eq_one.mpr ⟨l, Finset.ext fun l' => ?_⟩
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => hl' l' h.2, fun h => ⟨Finset.mem_univ _, h ▸ hl⟩⟩

open scoped Classical in
/-- The incidence identity of a projective plane of order `n`: for variables `x p` indexed by the
points, the sum over the lines of the squares of the line sums is
`n * ∑ p, x p ^ 2 + (∑ p, x p) ^ 2`. -/
theorem sum_sq_sum_incidence [Fintype P] [Fintype L] (x : P → ℚ) :
    ∑ l : L, (∑ p : P, if p ∈ l then x p else 0) ^ 2 =
      order P L * ∑ p, x p ^ 2 + (∑ p, x p) ^ 2 := by
  have hcount (p q : P) : ∑ l : L, (if p ∈ l then x p else 0) * (if q ∈ l then x q else 0) =
      x p * x q + if p = q then order P L * x p ^ 2 else 0 := by
    have hmul (l : L) : (if p ∈ l then x p else 0) * (if q ∈ l then x q else 0) =
        if p ∈ l ∧ q ∈ l then x p * x q else 0 := by
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl fun l _ => hmul l, ← Finset.sum_filter, Finset.sum_const,
      card_filter_mem_and_mem, nsmul_eq_mul]
    split_ifs with hpq
    · subst hpq
      push_cast
      ring
    · push_cast
      ring
  calc ∑ l : L, (∑ p : P, if p ∈ l then x p else 0) ^ 2
    _ = ∑ l : L, ∑ p : P, ∑ q : P,
          (if p ∈ l then x p else 0) * (if q ∈ l then x q else 0) := by
      simp only [sq, Finset.sum_mul_sum]
    _ = ∑ p : P, ∑ q : P, ∑ l : L,
          (if p ∈ l then x p else 0) * (if q ∈ l then x q else 0) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p : P, ∑ q : P, (x p * x q + if p = q then order P L * x p ^ 2 else 0) := by
      simp only [hcount]
    _ = order P L * ∑ p, x p ^ 2 + (∑ p, x p) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

/-- The rational form of the Bruck–Ryser theorem. -/
theorem exists_rat_mul_sq_eq_one_add_sq [Finite P] [Finite L]
    (h : order P L % 4 = 1 ∨ order P L % 4 = 2) :
    ∃ q r : ℚ, (order P L : ℚ) * q ^ 2 = 1 + r ^ 2 := by
  classical
  have := Fintype.ofFinite P
  have := Fintype.ofFinite L
  have hn : order P L ≠ 0 := (Nat.zero_lt_one.trans (one_lt_order P L)).ne'
  have hcard : Fintype.card (Option P) = Fintype.card (Option L) := by
    rw [Fintype.card_option, Fintype.card_option, card_points_eq_card_lines P L]
  have h4 : 4 ∣ Fintype.card (Option P) := by
    rw [Fintype.card_option, card_points P L]
    rcases h with h | h
    · obtain ⟨t, ht⟩ : ∃ t, order P L = 4 * t + 1 := ⟨order P L / 4, by omega⟩
      exact ⟨4 * t ^ 2 + 3 * t + 1, by rw [ht]; ring⟩
    · obtain ⟨t, ht⟩ : ∃ t, order P L = 4 * t + 2 := ⟨order P L / 4, by omega⟩
      exact ⟨4 * t ^ 2 + 5 * t + 2, by rw [ht]; ring⟩
  obtain ⟨T, hT⟩ := exists_linearMap_sum_sq hcard h4 hn
  let f : L → ((Option L → ℚ) →ₗ[ℚ] ℚ) := fun l =>
    ∑ p : P, if p ∈ l then (LinearMap.proj (some p)).comp T else 0
  obtain ⟨y, hy1, hy⟩ := exists_sq_eq_sq_of_linearMap f
  have hf (l : L) : f l y = ∑ p : P, if p ∈ l then T y (some p) else 0 := by
    simp only [f, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun p _ => by split_ifs <;> rfl
  refine ⟨T y none, ∑ p, T y (some p), ?_⟩
  have h1 := sum_sq_sum_incidence (L := L) fun p => T y (some p)
  have h2 := hT y
  rw [Fintype.sum_option, Fintype.sum_option, hy1] at h2
  have h3 : ∑ l, (∑ p : P, if p ∈ l then T y (some p) else 0) ^ 2 = ∑ l, y (some l) ^ 2 :=
    Finset.sum_congr rfl fun l _ => by rw [← hf, hy]
  rw [h3] at h1
  linear_combination h2 + h1

end Plane

end Cslib

namespace Configuration.ProjectivePlane

variable (P L : Type*) [Membership P L] [ProjectivePlane P L] [Finite P] [Finite L]

/-- The **Bruck–Ryser theorem**: if the order of a finite projective plane is congruent to `1` or
`2` modulo `4`, then it is a sum of two squares. -/
theorem exists_sq_add_sq_of_order (h : order P L % 4 = 1 ∨ order P L % 4 = 2) :
    ∃ a b : ℕ, order P L = a ^ 2 + b ^ 2 := by
  obtain ⟨q, r, hqr⟩ := Cslib.exists_rat_mul_sq_eq_one_add_sq h
  exact Cslib.exists_sq_add_sq_of_rat hqr

/-- **Theorem B** of [Monk1964]: there is no projective plane of order `2 * 3 ^ (2 * k + 1)`, by
the Bruck–Ryser theorem. -/
theorem order_ne_two_mul_three_pow (k : ℕ) : order P L ≠ 2 * 3 ^ (2 * k + 1) := by
  intro hk
  have hodd : 3 ^ (2 * k + 1) % 2 = 1 := by
    rw [Nat.pow_mod]
    simp
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_of_order P L (.inr (by omega))
  rw [hk] at hab
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : 3 ∈ (2 * 3 ^ (2 * k + 1)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, (dvd_pow_self 3 (Nat.succ_ne_zero _)).mul_left 2,
      by positivity⟩
  have heven := (Nat.eq_sq_add_sq_iff.mp ⟨a, b, hab⟩) 3 hmem rfl
  rw [Nat.padicValNat_def, Nat.multiplicity_mul two_ne_zero (by positivity),
    Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd (by decide), zero_add] at heven
  obtain ⟨r, hr⟩ := heven
  omega

end Configuration.ProjectivePlane
