/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Cslib.Init
public import Cslib.Computability.Quantum.State
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Hilbert operators and unitary gates over finite registers

`HilbertOperator R` is the raw complex matrix over a finite register `R`.
It is used for observables, projectors, matrix sums, and block-encoding targets
that are not necessarily unitary.

`Gate R` is a unitary Hilbert operator.  A gate acts on raw vectors by
`applyVec` and evolves pure states by `apply`.
-/

@[expose] public section

namespace Cslib.Quantum

/-- Raw linear operator over a finite quantum register. -/
abbrev HilbertOperator (R : Register) : Type := Matrix R.Index R.Index ℂ

namespace HilbertOperator

noncomputable section

variable {R : Register}

/-- A Hilbert operator acts on a raw state vector by matrix-vector multiplication. -/
def applyVec (A : HilbertOperator R) (psi : StateVector R) : StateVector R :=
  WithLp.toLp 2 (A.mulVec psi.ofLp)

@[simp]
theorem applyVec_apply (A : HilbertOperator R) (psi : StateVector R) (i : R.Index) :
    applyVec A psi i = ∑ j, A i j * psi j :=
  rfl

@[simp]
theorem applyVec_add (A : HilbertOperator R) (psi phi : StateVector R) :
    applyVec A (psi + phi) = applyVec A psi + applyVec A phi := by
  unfold applyVec
  rw [show (psi + phi).ofLp = psi.ofLp + phi.ofLp from rfl, Matrix.mulVec_add]
  rfl

@[simp]
theorem applyVec_sub (A : HilbertOperator R) (psi phi : StateVector R) :
    applyVec A (psi - phi) = applyVec A psi - applyVec A phi := by
  unfold applyVec
  rw [show (psi - phi).ofLp = psi.ofLp - phi.ofLp from rfl, Matrix.mulVec_sub]
  rfl

@[simp]
theorem applyVec_smul (A : HilbertOperator R) (c : ℂ) (psi : StateVector R) :
    applyVec A (c • psi) = c • applyVec A psi := by
  unfold applyVec
  rw [show (c • psi).ofLp = c • psi.ofLp from rfl, Matrix.mulVec_smul]
  rfl

@[simp]
theorem applyVec_neg (A : HilbertOperator R) (psi : StateVector R) :
    applyVec A (-psi) = -applyVec A psi := by
  unfold applyVec
  rw [show (-psi).ofLp = -psi.ofLp from rfl, Matrix.mulVec_neg]
  rfl

@[simp]
theorem add_applyVec (A B : HilbertOperator R) (psi : StateVector R) :
    applyVec (A + B) psi = applyVec A psi + applyVec B psi := by
  unfold applyVec
  rw [Matrix.add_mulVec]
  rfl

@[simp]
theorem smul_applyVec (c : ℂ) (A : HilbertOperator R) (psi : StateVector R) :
    applyVec (c • A) psi = c • applyVec A psi := by
  unfold applyVec
  rw [Matrix.smul_mulVec]
  rfl

@[simp]
theorem one_applyVec (psi : StateVector R) : applyVec (1 : HilbertOperator R) psi = psi := by
  unfold applyVec
  rw [Matrix.one_mulVec]

theorem mul_applyVec (A B : HilbertOperator R) (psi : StateVector R) :
    applyVec (A * B) psi = applyVec A (applyVec B psi) := by
  unfold applyVec
  rw [show (WithLp.toLp 2 (B.mulVec psi.ofLp)).ofLp = B.mulVec psi.ofLp from rfl,
    Matrix.mulVec_mulVec]

/-- A Hilbert operator sends a basis ket to its corresponding column. -/
@[simp, nolint simpNF]
theorem applyVec_ket (A : HilbertOperator R) (x : R.Index) (i : R.Index) :
    applyVec A (PureState.ket x : StateVector R) i = A i x := by
  rw [applyVec_apply]
  simp only [PureState.ket_apply, mul_ite, mul_one, mul_zero]
  exact Fintype.sum_ite_eq' x (fun j => A i j)

/-- Hilbert operators are equal when they agree on all state vectors. -/
theorem ext_of_applyVec_eq {A B : HilbertOperator R}
    (h : ∀ psi : StateVector R, applyVec A psi = applyVec B psi) :
    A = B := by
  ext i j
  have hket := congrArg (fun psi : StateVector R => psi i)
    (h (PureState.ket j : StateVector R))
  simpa using hket

/-- Applying a Hilbert operator to a finite sum of state vectors is the finite
sum of its applications. -/
theorem applyVec_sum {ι : Type} [Fintype ι]
    (A : HilbertOperator R) (f : ι → StateVector R) :
    applyVec A (∑ i, f i) = ∑ i, applyVec A (f i) := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · ext k
    simp [applyVec_apply]
  · intro i s hi ih
    simp [Finset.sum_insert, hi, applyVec_add, ih]

/-- Applying a finite sum of Hilbert operators is the finite sum of their
applications. -/
theorem sum_applyVec {ι : Type} [Fintype ι]
    (f : ι → HilbertOperator R) (psi : StateVector R) :
    applyVec (∑ i, f i) psi = ∑ i, applyVec (f i) psi := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · ext k
    simp [applyVec_apply]
  · intro i s hi ih
    simp [Finset.sum_insert, hi, add_applyVec, ih]

/-- Hilbert operators are equal when they agree on every vector of an
orthonormal basis. -/
theorem ext_of_applyVec_eq_on_orthonormalBasis {ι : Type} [Fintype ι]
    (basis : OrthonormalBasis ι ℂ (StateVector R))
    {A B : HilbertOperator R}
    (h : ∀ i : ι, applyVec A (basis i) = applyVec B (basis i)) :
    A = B := by
  apply ext_of_applyVec_eq
  intro psi
  calc
    applyVec A psi =
        applyVec A (∑ i, basis.repr psi i • basis i) := by
          rw [basis.sum_repr]
    _ = ∑ i, applyVec A (basis.repr psi i • basis i) := by
          rw [applyVec_sum]
    _ = ∑ i, basis.repr psi i • applyVec A (basis i) := by
          simp [applyVec_smul]
    _ = ∑ i, basis.repr psi i • applyVec B (basis i) := by
          exact Finset.sum_congr rfl fun i _ => by rw [h i]
    _ = ∑ i, applyVec B (basis.repr psi i • basis i) := by
          simp [applyVec_smul]
    _ = applyVec B (∑ i, basis.repr psi i • basis i) := by
          rw [applyVec_sum]
    _ = applyVec B psi := by
          rw [basis.sum_repr]

/-- A unitary Hilbert operator preserves inner products on raw state vectors. -/
theorem inner_applyVec_applyVec_of_mem_unitaryGroup {U : HilbertOperator R}
    (hU : U ∈ Matrix.unitaryGroup R.Index ℂ) (psi phi : StateVector R) :
    inner ℂ (applyVec U psi) (applyVec U phi) = inner ℂ psi phi := by
  have hUU : U.conjTranspose * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  simp only [PiLp.inner_apply, RCLike.inner_apply, applyVec_apply]
  calc ∑ i, (∑ k, U i k * phi k) * starRingEnd ℂ (∑ j, U i j * psi j)
      = ∑ i, ∑ k, ∑ j, (U i k * starRingEnd ℂ (U i j))
          * (phi k * starRingEnd ℂ (psi j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    _ = ∑ k, ∑ j, (∑ i, U i k * starRingEnd ℂ (U i j))
          * (phi k * starRingEnd ℂ (psi j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ k, ∑ j, (1 : HilbertOperator R) j k * (phi k * starRingEnd ℂ (psi j)) := by
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [← hUU, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Matrix.conjTranspose_apply,
            show star (U i j) = starRingEnd ℂ (U i j) from rfl, mul_comm]
    _ = ∑ k, phi k * starRingEnd ℂ (psi k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
        exact Fintype.sum_ite_eq' k fun j => phi k * starRingEnd ℂ (psi j)

/-- A unitary Hilbert operator preserves raw vector norms. -/
theorem norm_applyVec_of_mem_unitaryGroup {U : HilbertOperator R}
    (hU : U ∈ Matrix.unitaryGroup R.Index ℂ) (psi : StateVector R) :
    ‖applyVec U psi‖ = ‖psi‖ := by
  have h := inner_applyVec_applyVec_of_mem_unitaryGroup hU psi psi
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖applyVec U psi‖ ^ 2 = ‖psi‖ ^ 2 := by exact_mod_cast h
  calc ‖applyVec U psi‖ = Real.sqrt (‖applyVec U psi‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖psi‖ ^ 2) := by rw [h2]
    _ = ‖psi‖ := Real.sqrt_sq (norm_nonneg _)

end

end HilbertOperator

/-- A unitary gate over a finite quantum register. -/
structure Gate (R : Register) where
  /-- Underlying Hilbert-space operator. -/
  op : HilbertOperator R
  /-- Gates are unitary by definition. -/
  unitary : op ∈ Matrix.unitaryGroup R.Index ℂ

namespace Gate

noncomputable section

variable {R : Register}

instance : Coe (Gate R) (HilbertOperator R) := ⟨Gate.op⟩
instance : CoeTail (Gate R) (HilbertOperator R) := ⟨Gate.op⟩
instance : CoeOut (Gate R) (HilbertOperator R) := ⟨Gate.op⟩

instance : CoeFun (Gate R) (fun _ => R.Index → R.Index → ℂ) :=
  ⟨fun G => G.op⟩

instance : HMul (Gate R) (HilbertOperator R) (HilbertOperator R) where
  hMul G A := (G : HilbertOperator R) * A

instance : HMul (HilbertOperator R) (Gate R) (HilbertOperator R) where
  hMul A G := A * (G : HilbertOperator R)

@[ext]
theorem ext {G K : Gate R} (h : ∀ i j, G i j = K i j) : G = K := by
  cases G with
  | mk G hG =>
    cases K with
    | mk K hK =>
      have hGK : G = K := by
        ext i j
        exact h i j
      subst hGK
      rfl

/-- Build a gate from a unitary Hilbert operator. -/
def ofUnitary (U : HilbertOperator R)
    (hU : U ∈ Matrix.unitaryGroup R.Index ℂ) : Gate R := ⟨U, hU⟩

@[simp]
theorem coe_ofUnitary (U : HilbertOperator R)
    (hU : U ∈ Matrix.unitaryGroup R.Index ℂ) :
    ((ofUnitary U hU : Gate R) : HilbertOperator R) = U := rfl

instance : Monoid (Gate R) where
  one := ofUnitary 1 (one_mem _)
  mul G K := ofUnitary ((G : HilbertOperator R) * (K : HilbertOperator R))
    (mul_mem G.unitary K.unitary)
  one_mul G := by
    ext i j
    change ((1 : HilbertOperator R) * (G : HilbertOperator R)) i j = G i j
    simp
  mul_one G := by
    ext i j
    change ((G : HilbertOperator R) * (1 : HilbertOperator R)) i j = G i j
    simp
  mul_assoc G K L := by
    ext i j
    change (((G : HilbertOperator R) * (K : HilbertOperator R)) * (L : HilbertOperator R)) i j
      = ((G : HilbertOperator R) * ((K : HilbertOperator R) * (L : HilbertOperator R))) i j
    rw [Matrix.mul_assoc]

@[simp]
theorem coe_one : (((1 : Gate R) : HilbertOperator R)) = 1 := rfl

@[simp]
theorem coe_mul (G K : Gate R) :
    (((G * K : Gate R) : HilbertOperator R))
      = (G : HilbertOperator R) * (K : HilbertOperator R) := rfl

@[simp]
theorem coe_pow (G : Gate R) (k : ℕ) :
    (((G ^ k : Gate R) : HilbertOperator R)) =
      (G : HilbertOperator R) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [pow_succ, ih]

/-- Conjugate transpose of a unitary gate, again as a gate. -/
def conjTranspose (G : Gate R) : Gate R :=
  ofUnitary ((G : HilbertOperator R).conjTranspose) (by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp G.unitary)

instance : Inv (Gate R) := ⟨conjTranspose⟩

@[simp]
theorem coe_conjTranspose (G : Gate R) :
    ((G.conjTranspose : Gate R) : HilbertOperator R)
      = (G : HilbertOperator R).conjTranspose := rfl

/-- A gate acts on a raw vector by its underlying Hilbert operator. -/
def applyVec (G : Gate R) (psi : StateVector R) : StateVector R :=
  HilbertOperator.applyVec (G : HilbertOperator R) psi

/-- A gate evolves a pure state to a pure state. -/
def apply (G : Gate R) (psi : PureState R) : PureState R :=
  PureState.ofVec (G.applyVec (psi : StateVector R)) (by
    change ‖HilbertOperator.applyVec (G : HilbertOperator R) (psi : StateVector R)‖ = 1
    rw [HilbertOperator.norm_applyVec_of_mem_unitaryGroup G.unitary, psi.norm_eq_one])

/-- Alias for `apply`, emphasizing unitary time evolution. -/
def evolve (G : Gate R) (psi : PureState R) : PureState R := G.apply psi

@[simp]
theorem apply_coe (G : Gate R) (psi : PureState R) :
    ((G.apply psi : PureState R) : StateVector R) = G.applyVec (psi : StateVector R) := rfl

@[simp]
theorem applyVec_apply (G : Gate R) (psi : StateVector R) (i : R.Index) :
    G.applyVec psi i = ∑ j, G i j * psi j := rfl

@[simp, nolint simpNF]
theorem apply_apply (G : Gate R) (psi : PureState R) (i : R.Index) :
    G.apply psi i = ∑ j, G i j * psi j := by
  change G.applyVec (psi : StateVector R) i = ∑ j, G i j * psi j
  rfl

@[simp]
theorem applyVec_add (G : Gate R) (psi phi : StateVector R) :
    G.applyVec (psi + phi) = G.applyVec psi + G.applyVec phi :=
  HilbertOperator.applyVec_add (G : HilbertOperator R) psi phi

@[simp]
theorem applyVec_sub (G : Gate R) (psi phi : StateVector R) :
    G.applyVec (psi - phi) = G.applyVec psi - G.applyVec phi :=
  HilbertOperator.applyVec_sub (G : HilbertOperator R) psi phi

@[simp]
theorem applyVec_smul (G : Gate R) (c : ℂ) (psi : StateVector R) :
    G.applyVec (c • psi) = c • G.applyVec psi :=
  HilbertOperator.applyVec_smul (G : HilbertOperator R) c psi

@[simp]
theorem applyVec_neg (G : Gate R) (psi : StateVector R) :
    G.applyVec (-psi) = -G.applyVec psi :=
  HilbertOperator.applyVec_neg (G : HilbertOperator R) psi

theorem apply_add (G : Gate R) (psi phi : StateVector R) :
    G.applyVec (psi + phi) = G.applyVec psi + G.applyVec phi :=
  applyVec_add G psi phi

theorem apply_sub (G : Gate R) (psi phi : StateVector R) :
    G.applyVec (psi - phi) = G.applyVec psi - G.applyVec phi :=
  applyVec_sub G psi phi

theorem apply_smul (G : Gate R) (c : ℂ) (psi : StateVector R) :
    G.applyVec (c • psi) = c • G.applyVec psi :=
  applyVec_smul G c psi

theorem apply_neg (G : Gate R) (psi : StateVector R) :
    G.applyVec (-psi) = -G.applyVec psi :=
  applyVec_neg G psi

@[simp]
theorem one_apply (psi : PureState R) : (1 : Gate R).apply psi = psi := by
  ext i
  change HilbertOperator.applyVec (1 : HilbertOperator R) (psi : StateVector R) i = psi i
  rw [HilbertOperator.one_applyVec]

@[simp]
theorem one_applyVec (psi : StateVector R) : (1 : Gate R).applyVec psi = psi :=
  HilbertOperator.one_applyVec psi

theorem mul_applyVec (G K : Gate R) (psi : StateVector R) :
    (G * K).applyVec psi = G.applyVec (K.applyVec psi) :=
  HilbertOperator.mul_applyVec (G : HilbertOperator R) (K : HilbertOperator R) psi

/-- Applying a gate after its adjoint returns the original vector. -/
theorem applyVec_conjTranspose_applyVec (G : Gate R) (psi : StateVector R) :
    G.applyVec (G.conjTranspose.applyVec psi) = psi := by
  change HilbertOperator.applyVec (G : HilbertOperator R)
    (HilbertOperator.applyVec (G.conjTranspose : HilbertOperator R) psi) = psi
  rw [← HilbertOperator.mul_applyVec]
  have hGG :
      (G : HilbertOperator R) *
          (G.conjTranspose : HilbertOperator R) =
        1 := by
    change (G : HilbertOperator R) *
          (G : HilbertOperator R).conjTranspose =
        1
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp G.unitary
  rw [hGG, HilbertOperator.one_applyVec]

/-- Applying a gate's adjoint after the gate returns the original vector. -/
theorem conjTranspose_applyVec_applyVec (G : Gate R) (psi : StateVector R) :
    G.conjTranspose.applyVec (G.applyVec psi) = psi := by
  change HilbertOperator.applyVec (G.conjTranspose : HilbertOperator R)
    (HilbertOperator.applyVec (G : HilbertOperator R) psi) = psi
  rw [← HilbertOperator.mul_applyVec]
  have hGG :
      (G.conjTranspose : HilbertOperator R) *
          (G : HilbertOperator R) =
        1 := by
    change (G : HilbertOperator R).conjTranspose *
          (G : HilbertOperator R) =
        1
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp G.unitary
  rw [hGG, HilbertOperator.one_applyVec]

theorem mul_apply (G K : Gate R) (psi : PureState R) :
    (G * K).apply psi = G.apply (K.apply psi) := by
  ext i
  change (G * K).applyVec (psi : StateVector R) i
      = G.applyVec (K.applyVec (psi : StateVector R)) i
  rw [mul_applyVec]

/-- A gate sends the basis ket `|x>` to its `x`-th column. -/
@[simp, nolint simpNF]
theorem apply_ket (G : Gate R) (x : R.Index) (i : R.Index) :
    G.apply (PureState.ket x) i = G i x := by
  rw [apply_apply]
  simp only [PureState.ket_apply, mul_ite, mul_one, mul_zero]
  exact Fintype.sum_ite_eq' x (fun j => G i j)

/-! ## Permutation gates -/

/-- The gate permuting the computational basis by `sigma`. -/
def ofPerm (sigma : Equiv.Perm R.Index) : Gate R :=
  ofUnitary (sigma.permMatrix ℂ) (by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
      inv_mul_cancel, Matrix.permMatrix_one])

@[simp, nolint simpNF]
theorem ofPerm_apply (sigma : Equiv.Perm R.Index) (psi : PureState R)
    (i : R.Index) : (ofPerm sigma).apply psi i = psi (sigma i) := by
  change HilbertOperator.applyVec (sigma.permMatrix ℂ) (psi : StateVector R) i =
    psi (sigma i)
  unfold HilbertOperator.applyVec
  rw [Matrix.permMatrix_mulVec]
  rfl

theorem ofPerm_apply_ket (sigma : Equiv.Perm R.Index) (x : R.Index) :
    (ofPerm sigma).apply (PureState.ket x) = PureState.ket (sigma⁻¹ x) := by
  ext i
  rw [ofPerm_apply, PureState.ket_apply, PureState.ket_apply]
  by_cases h : sigma i = x
  · rw [if_pos h, if_pos (by rw [← h]; exact (Equiv.symm_apply_apply sigma i).symm)]
  · rw [if_neg h,
      if_neg (fun hi => h (by rw [hi]; exact Equiv.apply_symm_apply sigma x))]

theorem ofPerm_mem_unitaryGroup (sigma : Equiv.Perm R.Index) :
    (ofPerm sigma : HilbertOperator R) ∈ Matrix.unitaryGroup R.Index ℂ :=
  (ofPerm sigma).unitary

/-! ## Unitary gates preserve inner products and norms -/

/-- Unitary gates preserve the inner product. -/
theorem inner_apply_apply_of_mem_unitaryGroup {U : Gate R}
    (_hU : (U : HilbertOperator R) ∈ Matrix.unitaryGroup R.Index ℂ)
    (psi phi : PureState R) :
    inner ℂ (U.apply psi : StateVector R) (U.apply phi : StateVector R)
      = inner ℂ (psi : StateVector R) (phi : StateVector R) :=
  HilbertOperator.inner_applyVec_applyVec_of_mem_unitaryGroup U.unitary
    (psi : StateVector R) (phi : StateVector R)

/-- Unitary gates preserve the norm. -/
theorem norm_apply_of_mem_unitaryGroup {U : Gate R}
    (_hU : (U : HilbertOperator R) ∈ Matrix.unitaryGroup R.Index ℂ)
    (psi : PureState R) :
    ‖(U.apply psi : StateVector R)‖ = ‖(psi : StateVector R)‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup U.unitary (psi : StateVector R)

theorem norm_apply (U : Gate R) (psi : PureState R) :
    ‖(U.apply psi : StateVector R)‖ = 1 :=
  (U.apply psi).norm_eq_one

end

end Gate

end Cslib.Quantum
