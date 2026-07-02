/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

import Cslib.Computability.Quantum.Gate

namespace CslibTests

open Cslib.Quantum

/-! # Quantum computing foundation smoke tests -/

example : (Qubits 2).Index = Fin 4 := rfl

example (x : (Qubits 2).Index) : PureState.ket x x = 1 := by
  simp

example {x y : (Qubits 2).Index} (h : PureState.ket x = PureState.ket y) : x = y :=
  PureState.ket_injective h

example (A : HilbertOperator (Qubits 1)) (x i : (Qubits 1).Index) :
    HilbertOperator.applyVec A (PureState.ket x : StateVector (Qubits 1)) i = A i x := by
  simp

example (ψ : PureState (Qubits 1)) : (1 : Gate (Qubits 1)).apply ψ = ψ := by
  simp

example (G K : Gate (Qubits 1)) (ψ : PureState (Qubits 1)) :
    (G * K).apply ψ = G.apply (K.apply ψ) :=
  Gate.mul_apply G K ψ

example (U : Gate (Qubits 1)) (ψ φ : PureState (Qubits 1)) :
    inner ℂ (U.apply ψ : StateVector (Qubits 1)) (U.apply φ : StateVector (Qubits 1)) =
      inner ℂ (ψ : StateVector (Qubits 1)) (φ : StateVector (Qubits 1)) :=
  Gate.inner_apply_apply_of_mem_unitaryGroup (U := U) U.unitary ψ φ

example (U : Gate (Qubits 1)) (ψ : PureState (Qubits 1)) :
    ‖(U.apply ψ : StateVector (Qubits 1))‖ = 1 :=
  Gate.norm_apply U ψ

/-- The one-qubit bit-flip permutation. -/
def bitFlip : Equiv.Perm (Qubits 1).Index :=
  Equiv.swap (0 : Fin 2) (1 : Fin 2)

example (ψ : PureState (Qubits 1)) (i : (Qubits 1).Index) :
    (Gate.ofPerm bitFlip).apply ψ i = ψ (bitFlip i) := by
  simpa using Gate.ofPerm_apply bitFlip ψ i

example :
    (Gate.ofPerm bitFlip).apply (PureState.ket (0 : Fin 2)) = PureState.ket (1 : Fin 2) := by
  rw [Gate.ofPerm_apply_ket]
  ext i
  fin_cases i <;> rfl

/-! A direct Bell-state example, before tensor products and named gates are introduced. -/

/-- The Bell state `(∣00⟩ + ∣11⟩) / √2`, represented directly in the two-qubit basis. -/
noncomputable def bell00Vec : StateVector (Qubits 2) :=
  WithLp.toLp 2 ![(Real.sqrt 2 : ℂ)⁻¹, 0, 0, (Real.sqrt 2 : ℂ)⁻¹]

theorem bell00Vec_norm : ‖bell00Vec‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [bell00Vec, Fin.sum_univ_four, Real.sq_sqrt]
  norm_num

/-- The Bell state `(∣00⟩ + ∣11⟩) / √2` as a pure state. -/
noncomputable def bell00 : PureState (Qubits 2) :=
  PureState.ofVec bell00Vec bell00Vec_norm

example : bell00 (0 : Fin 4) = (Real.sqrt 2 : ℂ)⁻¹ := rfl
example : bell00 (1 : Fin 4) = 0 := rfl
example : bell00 (2 : Fin 4) = 0 := rfl
example : bell00 (3 : Fin 4) = (Real.sqrt 2 : ℂ)⁻¹ := rfl

example : ‖(bell00 : StateVector (Qubits 2))‖ = 1 :=
  bell00.norm_eq_one

example : (1 : Gate (Qubits 2)).apply bell00 = bell00 := by
  simp

end CslibTests
