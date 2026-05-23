/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic

/-!
# Fourier expansion of Boolean functions

The cube `Fin n → ZMod 2` is paired with the `±1` encoding
`chi : ZMod 2 → ℝ`, `b ↦ (-1)^b`; a Boolean-valued function is one with
range `{-1, +1} ⊂ ℝ`.

Real-valued functions on the cube carry the uniform-measure `L²` inner
product `⟪f, g⟫ = 𝔼 x, f x * g x`. The parity functions
`χ_S(x) = ∏_{i ∈ S} (-1)^(xᵢ)` form an orthonormal basis, and every function
has a unique Fourier expansion `f(x) = ∑_S 𝓕 f S · χ_S(x)` with
`𝓕 f S = ⟪f, χ_S⟫`.

This file formalizes Chapter 1 of [ODonnell2014] up to Parseval/Plancherel.

## Main definitions

- `HammingCube`: the Hamming cube `Fin n → ZMod 2`.
- `BooleanFunction`: real-valued functions on the Hamming cube, equipped with
  the uniform-measure `L²` inner product as an `InnerProductSpace ℝ`.
- `chi`: the `±1` encoding `ZMod 2 → ℝ` sending `0 ↦ 1` and `1 ↦ -1`.
- `parityFun`: the parity function `χ_S : 𝔽₂ⁿ → ℝ`,
  `(χ_S)(x) = ∏_{i ∈ S} χ(xᵢ)`.
- `fourierCoeff`: Fourier coefficient `𝓕 f S = ⟪f, χ_S⟫`.
- `IsBooleanValued`: the predicate that `f` takes values in `{-1, 1}`.

## Main results

- `parityFun_orthonormal_apply`: `⟪χ_S, χ_T⟫ = δ_{S,T}`
  ([ODonnell2014], Theorem 1.5, orthonormality identity).
- `parityOrthonormalBasis`: the parity functions form an orthonormal basis
  ([ODonnell2014], Theorem 1.5, basis form).
- `fourier_expansion`: every `f` equals `∑_S 𝓕 f S · χ_S` pointwise
  ([ODonnell2014], Theorem 1.1, existence).
- `fourier_uniqueness`: the Fourier coefficients are unique
  ([ODonnell2014], Theorem 1.1, uniqueness).
- `plancherel`: `⟪f, g⟫ = ∑_S 𝓕 f S · 𝓕 g S`.
- `parseval`: `⟪f, f⟫ = ∑_S (𝓕 f S)²`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*, Chapter 1][ODonnell2014]
-/

@[expose] public section

namespace Cslib.Foundations.Combinatorics.BooleanFunctions

open Finset
open scoped BigOperators

variable {n : ℕ}

/-! ### The Hamming cube and the space of Boolean functions -/

/-- The Hamming cube `𝔽₂ⁿ`, modelled as `Fin n → ZMod 2`. -/
abbrev HammingCube (n : ℕ) := Fin n → ZMod 2

/-- Real-valued functions on the Hamming cube, equipped with the uniform-measure
`L²` inner product `⟪f, g⟫ = 𝔼 x, f x * g x`. -/
def BooleanFunction (n : ℕ) := HammingCube n → ℝ

namespace BooleanFunction

noncomputable instance : CommRing (BooleanFunction n) :=
  inferInstanceAs (CommRing (HammingCube n → ℝ))
noncomputable instance : Module ℝ (BooleanFunction n) :=
  inferInstanceAs (Module ℝ (HammingCube n → ℝ))
noncomputable instance : Algebra ℝ (BooleanFunction n) :=
  inferInstanceAs (Algebra ℝ (HammingCube n → ℝ))
instance : Inhabited (BooleanFunction n) :=
  inferInstanceAs (Inhabited (HammingCube n → ℝ))

instance : FunLike (BooleanFunction n) (HammingCube n) ℝ where
  coe f := f
  coe_injective' _ _ h := h

@[ext]
theorem ext {f g : BooleanFunction n} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp] theorem zero_apply (x : HammingCube n) : (0 : BooleanFunction n) x = 0 := rfl
@[simp] theorem one_apply (x : HammingCube n) : (1 : BooleanFunction n) x = 1 := rfl
@[simp] theorem add_apply (f g : BooleanFunction n) (x : HammingCube n) :
    (f + g) x = f x + g x := rfl
@[simp] theorem neg_apply (f : BooleanFunction n) (x : HammingCube n) : (-f) x = -(f x) := rfl
@[simp] theorem sub_apply (f g : BooleanFunction n) (x : HammingCube n) :
    (f - g) x = f x - g x := rfl
@[simp] theorem mul_apply (f g : BooleanFunction n) (x : HammingCube n) :
    (f * g) x = f x * g x := rfl
@[simp] theorem smul_apply (r : ℝ) (f : BooleanFunction n) (x : HammingCube n) :
    (r • f) x = r * f x := rfl

@[simp] theorem sum_apply {ι : Type*} (s : Finset ι) (g : ι → BooleanFunction n)
    (x : HammingCube n) : (∑ i ∈ s, g i) x = ∑ i ∈ s, (g i) x :=
  Finset.sum_apply x s g

/-! ### Inner product space structure -/

/-- Uniform-measure `L²` inner-product core on `BooleanFunction n`. -/
@[reducible]
noncomputable def innerCore : InnerProductSpace.Core ℝ (BooleanFunction n) where
  inner f g := (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, f x * g x
  conj_inner_symm f g := by
    change (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, g x * f x =
        (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, f x * g x
    congr 1
    exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  re_inner_nonneg f := by
    change 0 ≤ (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, f x * f x
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun x _ => mul_self_nonneg (f x))
  add_left f g h := by
    change (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, (f + g) x * h x =
        (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, f x * h x +
          (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, g x * h x
    simp [add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  smul_left f g r := by
    change (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, (r • f) x * g x =
        r * ((1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, f x * g x)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [smul_apply]; ring
  definite f h := by
    change (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, f x * f x = 0 at h
    have hsum : ∑ x : HammingCube n, f x * f x = 0 :=
      (mul_eq_zero.mp h).resolve_left (by positivity)
    ext x
    simpa [mul_self_eq_zero] using
      (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_self_nonneg (f x)).mp hsum
        x (Finset.mem_univ x)

noncomputable instance : NormedAddCommGroup (BooleanFunction n) :=
  innerCore.toNormedAddCommGroup

noncomputable instance innerProductSpace : InnerProductSpace ℝ (BooleanFunction n) :=
  InnerProductSpace.ofCore { __ := innerCore }

theorem inner_def (f g : BooleanFunction n) :
    @inner ℝ _ _ f g = (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, f x * g x := rfl

end BooleanFunction

/-! ### Notation -/

/-- Inner product on `BooleanFunction n`. -/
scoped notation "⟪" f ", " g "⟫" => @inner ℝ (BooleanFunction _) _ f g

/-- `L²` norm on `BooleanFunction n`. -/
scoped notation "‖" f "‖₂" => @norm (BooleanFunction _) _ f

/-! ### The `±1` encoding and parity functions -/

/-- A function on the Hamming cube is Boolean-valued if it takes values in
`{-1, 1}` ([ODonnell2014], §1.2). -/
def IsBooleanValued (f : BooleanFunction n) : Prop :=
  ∀ x, f x = 1 ∨ f x = -1

/-- The `±1` encoding `χ : ZMod 2 → ℝ`, `χ(b) = (-1)^b`
([ODonnell2014], §1.2). -/
def chi : ZMod 2 → ℝ := fun b => if b = 0 then 1 else -1

/-- The parity function `χ_S : 𝔽₂ⁿ → ℝ` for `S ⊆ [n]`, defined by
`(χ_S)(x) = ∏_{i ∈ S} χ(xᵢ) = (-1)^(∑_{i ∈ S} xᵢ)`
([ODonnell2014], Definition 1.2). -/
noncomputable def parityFun (S : Finset (Fin n)) : BooleanFunction n :=
  fun x => ∏ i ∈ S, chi (x i)

@[inherit_doc] scoped prefix:max "χ" => parityFun

/-- The Fourier coefficient `𝓕 f S = ⟪f, χ S⟫` ([ODonnell2014], Proposition 1.8).
Its square `(𝓕 f S)²` is called the *Fourier weight* of `f` on `S`
([ODonnell2014], Definition 1.17). -/
noncomputable def fourierCoeff (f : BooleanFunction n) (S : Finset (Fin n)) : ℝ :=
  ⟪f, χ S⟫

@[inherit_doc] scoped notation "𝓕" => fourierCoeff

/-- The uniform expectation over the Hamming cube equals `2⁻ⁿ · ∑_x f(x)`. -/
theorem expect_eq_sum_div_pow (f : HammingCube n → ℝ) :
    𝔼 x, f x = 1 / 2 ^ n * ∑ x : HammingCube n, f x := by
  rw [Finset.expect_eq_sum_div_card]
  simp [Finset.card_univ, ZMod.card]
  ring

/-- `⟪f, g⟫ = 𝔼 x, f x * g x` ([ODonnell2014], Definition 1.3). -/
theorem inner_eq_expect (f g : BooleanFunction n) :
    ⟪f, g⟫ = 𝔼 x, f x * g x := by
  simp [BooleanFunction.inner_def, expect_eq_sum_div_pow]

/-! ### Properties of the encoding `χ` -/

@[simp] theorem chi_zero : chi (0 : ZMod 2) = 1 := by simp [chi]

@[simp] theorem chi_one : chi (1 : ZMod 2) = -1 := by simp [chi]

@[simp] theorem chi_sq (b : ZMod 2) : chi b ^ 2 = 1 := by
  fin_cases b <;> simp [chi]

private theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> tauto

/-- `χ` is multiplicative on `ZMod 2`: `χ(a + b) = χ(a) · χ(b)`. -/
@[simp] theorem chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [chi, show (1 : ZMod 2) + 1 = 0 from Fin.ext (by decide)]

/-! ### Properties of parity functions -/

@[simp] theorem parityFun_empty : (χ (∅ : Finset (Fin n))) = fun _ => 1 := by
  funext _; simp [parityFun]

/-- Parity functions are multiplicative: `χ_S(x + y) = χ_S(x) · χ_S(y)`
([ODonnell2014], Equation 1.5). -/
@[simp] theorem parityFun_add (S : Finset (Fin n)) (x y : HammingCube n) :
    (χ S) (x + y) = (χ S) x * (χ S) y := by
  simp [parityFun, ← Finset.prod_mul_distrib, chi_add]

@[simp] theorem parityFun_sq (S : Finset (Fin n)) (x : HammingCube n) : (χ S) x ^ 2 = 1 := by
  simp [parityFun, ← Finset.prod_pow]

@[simp] theorem parityFun_zero (S : Finset (Fin n)) : (χ S) 0 = 1 := by simp [parityFun]

/-- `χ_S · χ_T = χ_{S △ T}` pointwise ([ODonnell2014], Fact 1.6). -/
theorem parityFun_mul_apply (S T : Finset (Fin n)) (x : HammingCube n) :
    (χ S) x * (χ T) x = (χ (symmDiff S T)) x := by
  simp only [parityFun]
  have hsd : (S ∪ T) \ (S ∩ T) = symmDiff S T := by
    ext i; simp [Finset.mem_symmDiff]; tauto
  have hsdiff := hsd ▸ Finset.prod_sdiff
    (Finset.inter_subset_union (s := S) (t := T)) (f := fun i => chi (x i))
  have hchi_sq : (∏ i ∈ S ∩ T, chi (x i)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]; simp
  rw [← Finset.prod_union_inter (s₁ := S) (s₂ := T) (f := fun i => chi (x i)),
    ← hsdiff, mul_assoc, ← sq, hchi_sq, mul_one]

/-- `𝔼 x, χ_S x = 1` if `S = ∅` and `0` otherwise ([ODonnell2014], Fact 1.7). -/
theorem expect_parityFun (S : Finset (Fin n)) :
    𝔼 x, (χ S) x = if S = ∅ then 1 else 0 := by
  split_ifs with h
  · subst h
    simp
  · simp only [expect_eq_sum_div_pow]
    obtain ⟨j, hj⟩ := Finset.nonempty_of_ne_empty h
    let ej : HammingCube n := Pi.single j 1
    have hej : (χ S) ej = -1 := by
      simp only [parityFun]
      have hprod : ∀ i ∈ S, chi (ej i) = if i = j then -1 else 1 := by
        intro i _
        simp only [ej, Pi.single_apply]
        split_ifs <;> simp
      rw [Finset.prod_congr rfl hprod]
      simp [hj]
    suffices h0 : ∑ x : HammingCube n, (χ S) x = 0 by rw [h0, mul_zero]
    have hself : ∑ x : HammingCube n, (χ S) x = -(∑ x : HammingCube n, (χ S) x) := by
      conv_lhs =>
        rw [Fintype.sum_equiv (Equiv.addRight ej) _ (fun y => -(χ S) y) (fun x => by
          change (χ S) x = -(χ S) (x + ej)
          rw [parityFun_add, hej, mul_neg_one, neg_neg])]
      rw [Finset.sum_neg_distrib]
    linarith

/-- The parity functions are orthonormal: `⟪χ_S, χ_T⟫ = δ_{S,T}`
([ODonnell2014], Theorem 1.5, orthonormality identity). -/
theorem parityFun_orthonormal_apply (S T : Finset (Fin n)) :
    ⟪χ S, χ T⟫ = if S = T then 1 else 0 := by
  rw [inner_eq_expect, funext (parityFun_mul_apply S T), expect_parityFun]
  simp

/-! ### The Fourier expansion theorem -/

/-- Sum of all parity functions at a point: `∑_S χ_S(z) = 2ⁿ` if `z = 0`, else `0`. -/
theorem sum_parityFun (z : HammingCube n) :
    ∑ S : Finset (Fin n), (χ S) z = if z = 0 then (2 : ℝ) ^ n else 0 := by
  split_ifs with hz
  · subst hz; simp [Finset.sum_const, Finset.card_univ]
  · have ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext (fun i => by simpa using h i))
    have hzj : z j = 1 := by
      have := ZMod.val_lt (z j)
      rcases (show (z j).val = 0 ∨ (z j).val = 1 by omega) with h | h
      · exact absurd (Fin.ext h : z j = 0) hj
      · exact Fin.ext h
    have hflip : ∀ S : Finset (Fin n), (χ (symmDiff S {j})) z = -(χ S) z := by
      intro S
      rw [← parityFun_mul_apply S {j} z]
      simp only [parityFun, Finset.prod_singleton, hzj, chi_one, mul_neg_one]
    have hself : ∑ S : Finset (Fin n), (χ S) z = -(∑ S : Finset (Fin n), (χ S) z) := by
      conv_lhs =>
        rw [Fintype.sum_equiv
          ((symmDiff_right_involutive ({j} : Finset (Fin n))).toPerm)
          _ (fun S => -(χ S) z) (fun S => by
            change (χ S) z = -(χ (symmDiff {j} S)) z
            rw [symmDiff_comm, hflip]; ring)]
      rw [Finset.sum_neg_distrib]
    linarith

/-- Fourier expansion ([ODonnell2014], Theorem 1.1, existence):
`f(x) = ∑_S 𝓕 f S · χ_S(x)`. -/
theorem fourier_expansion (f : BooleanFunction n) (x : HammingCube n) :
    f x = ∑ S : Finset (Fin n), 𝓕 f S * (χ S) x := by
  simp only [fourierCoeff, BooleanFunction.inner_def]
  have hadd_zero : ∀ y : HammingCube n, y + x = 0 ↔ y = x := fun y => by
    simp only [funext_iff]
    refine forall_congr' fun i => ?_
    change y i + x i = 0 ↔ y i = x i
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]
  conv_rhs =>
    arg 2; ext S
    rw [show (1 / (2 : ℝ) ^ n * ∑ y, f y * (χ S) y) * (χ S) x =
      ∑ y : HammingCube n, 1 / (2 : ℝ) ^ n * (f y * ((χ S) (y + x))) from by
      rw [mul_comm _ ((χ S) x), Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _
      rw [parityFun_add]; ring]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_parityFun, hadd_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ _)]
  field_simp

/-- Fourier uniqueness ([ODonnell2014], Theorem 1.1, uniqueness): if
`f = ∑_S c_S · χ_S` then `c = 𝓕 f`. -/
theorem fourier_uniqueness (f : BooleanFunction n) (c : Finset (Fin n) → ℝ)
    (h : ∀ x, f x = ∑ S : Finset (Fin n), c S * (χ S) x) (T : Finset (Fin n)) :
    c T = 𝓕 f T := by
  have hortho : ∀ S, (1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, (χ S) x * (χ T) x =
      if S = T then 1 else 0 :=
    fun S => by rw [← BooleanFunction.inner_def]; exact parityFun_orthonormal_apply S T
  have hexpand : (fun x : HammingCube n => f x * (χ T) x) =
      (fun x => ∑ S, c S * ((χ S) x * (χ T) x)) :=
    funext fun x => by
      rw [h x, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hswap : ∑ x : HammingCube n, f x * (χ T) x =
      ∑ S : Finset (Fin n), c S * ∑ x : HammingCube n, (χ S) x * (χ T) x := by
    rw [hexpand, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum .. |>.symm
  have hmove : ∀ S, (1 / (2 : ℝ) ^ n) * (c S * ∑ x : HammingCube n, (χ S) x * (χ T) x) =
      c S * ((1 / (2 : ℝ) ^ n) * ∑ x : HammingCube n, (χ S) x * (χ T) x) :=
    fun _ => by ring
  simp only [fourierCoeff, BooleanFunction.inner_def]
  rw [hswap, Finset.mul_sum]
  simp_rw [hmove, hortho, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ### Plancherel and Parseval -/

/-- The parity functions form an orthonormal family. -/
theorem parityFun_orthonormal : Orthonormal ℝ (parityFun (n := n)) :=
  orthonormal_iff_ite.mpr parityFun_orthonormal_apply

/-- The parity functions span `BooleanFunction n`. -/
theorem parityFun_span : ⊤ ≤ Submodule.span ℝ (Set.range (parityFun (n := n))) := by
  intro f _
  have hf : f = ∑ S : Finset (Fin n), fourierCoeff f S • parityFun S := by
    ext x; simpa [BooleanFunction.smul_apply] using fourier_expansion f x
  rw [hf]
  exact Submodule.sum_mem _ fun S _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)

/-- The parity functions form an orthonormal basis for `BooleanFunction n`
([ODonnell2014], Theorem 1.5, basis form). -/
noncomputable def parityOrthonormalBasis :
    OrthonormalBasis (Finset (Fin n)) ℝ (BooleanFunction n) :=
  OrthonormalBasis.mk parityFun_orthonormal parityFun_span

@[simp] theorem parityOrthonormalBasis_apply (S : Finset (Fin n)) :
    parityOrthonormalBasis (n := n) S = parityFun S := by
  change (OrthonormalBasis.mk parityFun_orthonormal parityFun_span) S = _
  simp [OrthonormalBasis.coe_mk]

/-- Plancherel's theorem: `⟪f, g⟫ = ∑_S 𝓕 f S · 𝓕 g S`. -/
theorem plancherel (f g : BooleanFunction n) :
    ⟪f, g⟫ = ∑ S : Finset (Fin n), 𝓕 f S * 𝓕 g S := by
  have h := parityOrthonormalBasis (n := n) |>.sum_inner_mul_inner f g
  simp only [parityOrthonormalBasis_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [fourierCoeff]
  rw [real_inner_comm (χ S) g]

/-- Parseval's theorem: `⟪f, f⟫ = ∑_S (𝓕 f S)²`. -/
theorem parseval (f : BooleanFunction n) :
    ⟪f, f⟫ = ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 := by
  rw [plancherel]
  exact Finset.sum_congr rfl fun S _ => (sq _).symm

/-- Parseval's theorem for Boolean-valued functions: the Fourier weights
sum to `1`. -/
theorem parseval_boolean (f : BooleanFunction n) (hf : IsBooleanValued f) :
    ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 = 1 := by
  rw [← parseval]
  simp only [BooleanFunction.inner_def]
  have hsq : ∀ x : HammingCube n, f x * f x = 1 := by
    intro x; rcases hf x with hx | hx <;> simp [hx]
  rw [Finset.sum_congr rfl (fun x _ => hsq x)]
  simp [Finset.sum_const, Finset.card_univ, ZMod.card]

end Cslib.Foundations.Combinatorics.BooleanFunctions
