/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Cslib.Init
public import Cslib.Computability.Quantum.Register
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Pure states over finite registers

`StateVector R` is the raw Hilbert-space vector type over a finite register
`R`.  `PureState R` bundles a raw vector with a unit-norm proof.

The qubit specialization is written `StateVector (Qubits n)` and
`PureState (Qubits n)`.
-/

@[expose] public section

namespace Cslib.Quantum

/-- Raw Hilbert-space vector for a finite quantum register. -/
abbrev StateVector (R : Register) : Type := EuclideanSpace ℂ R.Index

/-- A pure state: a unit vector in the computational Hilbert space. -/
structure PureState (R : Register) where
  /-- Underlying Hilbert-space vector. -/
  vec : StateVector R
  /-- Pure states are normalized by definition. -/
  norm_eq_one : ‖vec‖ = 1

namespace PureState

noncomputable section

variable {R : Register}

instance : Coe (PureState R) (StateVector R) := ⟨PureState.vec⟩
instance : CoeTail (PureState R) (StateVector R) := ⟨PureState.vec⟩
instance : CoeOut (PureState R) (StateVector R) := ⟨PureState.vec⟩

instance : CoeFun (PureState R) (fun _ => R.Index → ℂ) :=
  ⟨fun psi => psi.vec⟩

instance : Norm (PureState R) := ⟨fun psi => ‖(psi : StateVector R)‖⟩

instance : Inner ℂ (PureState R) :=
  ⟨fun psi phi => inner ℂ (psi : StateVector R) (phi : StateVector R)⟩

instance : HAdd (PureState R) (PureState R) (StateVector R) :=
  ⟨fun psi phi => (psi : StateVector R) + (phi : StateVector R)⟩

instance : HSub (PureState R) (PureState R) (StateVector R) :=
  ⟨fun psi phi => (psi : StateVector R) - (phi : StateVector R)⟩

instance : HSMul ℂ (PureState R) (StateVector R) :=
  ⟨fun c psi => c • (psi : StateVector R)⟩

@[simp]
theorem hAdd_apply (psi phi : PureState R) (i : R.Index) :
    (psi + phi : StateVector R) i = psi i + phi i := rfl

@[simp]
theorem hSub_apply (psi phi : PureState R) (i : R.Index) :
    (psi - phi : StateVector R) i = psi i - phi i := rfl

@[simp]
theorem hSMul_apply (c : ℂ) (psi : PureState R) (i : R.Index) :
    (c • psi : StateVector R) i = c * psi i := rfl

/-- Build a pure state from a normalized Hilbert-space vector. -/
def ofVec (v : StateVector R) (h : ‖v‖ = 1) : PureState R := ⟨v, h⟩

@[simp]
theorem coe_ofVec (v : StateVector R) (h : ‖v‖ = 1) :
    ((ofVec v h : PureState R) : StateVector R) = v := rfl

@[simp]
theorem ofVec_apply (v : StateVector R) (h : ‖v‖ = 1) (i : R.Index) :
    ofVec v h i = v i := rfl

@[simp]
theorem norm_eq_one' (psi : PureState R) : ‖(psi : StateVector R)‖ = 1 :=
  psi.norm_eq_one

@[ext]
theorem ext {psi phi : PureState R} (h : ∀ i, psi i = phi i) : psi = phi := by
  cases psi with
  | mk psi hpsi =>
    cases phi with
    | mk phi hphi =>
      have hv : psi = phi := by
        apply WithLp.ofLp_injective
        funext i
        exact h i
      subst hv
      rfl

/-- Computational-basis ket over a finite register. -/
def ket (x : R.Index) : PureState R :=
  ofVec (PiLp.single 2 x 1) (by simp)

@[simp]
theorem ket_apply (x i : R.Index) : ket x i = if i = x then 1 else 0 := by
  simp [ket]

theorem ket_injective : Function.Injective (ket (R := R)) := by
  intro x y hxy
  by_contra hne
  have h : ket x x = ket y x := by rw [hxy]
  rw [ket_apply, ket_apply, if_pos rfl, if_neg hne] at h
  exact one_ne_zero h

@[simp, nolint simpNF]
theorem norm_ket (x : R.Index) : ‖(ket x : StateVector R)‖ = 1 :=
  (ket x).norm_eq_one

end

end PureState

end Cslib.Quantum
