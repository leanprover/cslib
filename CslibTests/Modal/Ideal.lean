/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.Modal.Lean.SMul
import Mathlib.RingTheory.Ideal.Operations

/-! # Example: radicals of ideals with modal logic

We leverage the accessibility relation induced by scalar multiplication to exemplify how laws of
radicals of ideals can be derived from modal logic laws.
-/

namespace CslibTests

open Cslib Logic Modal Proposition Model Relation

/-! ## Relational view of radicals of ideals

We interpret positive exponentiation as an action and hence as an accessibility relation.
Ideals are invariant under this action, while radical membership corresponds to reachability.
-/

/-- Positive naturals act on a monoid by exponentiation. -/
@[instance_reducible]
def posPowAction [Monoid α] : MulAction ℕ+ α where
  smul n x := x ^ (n : ℕ)
  one_smul x := pow_one x
  mul_smul m n x := by
    simp [HSMul.hSMul, ←pow_mul, mul_comm]

local instance [Monoid α] : MulAction ℕ+ α := posPowAction

/-- Ideals are invariant under positive exponentiation. -/
theorem Ideal.posPowSMulMemClass [Semiring R] : SMulMemClass (Ideal R) ℕ+ R where
  smul_mem n _ hx := Ideal.pow_mem_of_mem _ hx n n.prop

local instance [Semiring R] : SMulMemClass (Ideal R) ℕ+ R := Ideal.posPowSMulMemClass

/-- Accessibility by positive natural exponentiation. -/
abbrev PosPow α [Monoid α] := Relation.ofSMul ℕ+ α

/-- The modal model of ideals under positive-power accessibility. -/
abbrev idealPowerModel [Semiring R] : Model R (Ideal R) := Model.ofContainers (PosPow R)

/-- Logical equivalence under `idealPowerModel`. -/
abbrev IdealEquiv [Semiring R] := Proposition.Equiv (idealPowerModel (R := R))

/-- An ideal atom denotes its underlying set in `idealPowerModel`. -/
example [Semiring R] (I : Ideal R) : (I : Set R) = Proposition.denotation idealPowerModel I := rfl

/-- Characterisation of radicals as modal denotations. This is the key bridge that enables reasoning
about membership of radicals with modal logic. -/
@[local grind =]
theorem Ideal.radical_eq_modal_denotation [CommSemiring R] (I : Ideal R) :
    (I.radical : Set R) = Proposition.denotation idealPowerModel (◇I) := by
  rw [Proposition.ofSMul_diamond_denotation]
  ext x
  apply Iff.intro
  · rintro ⟨n, hn⟩
    refine ⟨⟨n + 1, Nat.succ_pos _⟩, ?_⟩
    exact I.pow_mem_of_pow_mem hn (Nat.le_succ n)
  · rintro ⟨n, hn⟩
    exact ⟨(n : ℕ), hn⟩

/-- In `idealPowerModel`, the radical of an ideal is logically equivalent to possibility. -/
theorem Ideal.radical_equiv_diamond [CommSemiring R] (I : Ideal R) :
    (I.radical : Proposition (Ideal R)) ≡[IdealEquiv] ◇I :=
  Proposition.equiv_iff_denotation_eq.mpr (Ideal.radical_eq_modal_denotation I)

open scoped Satisfies

/-- Radical is idempotent, as a consequence of modal idempotence of `◇`. -/
theorem Ideal.radical_idem [CommSemiring R] (I : Ideal R) : I.radical.radical = I.radical := by
  apply SetLike.ext'
  simp only [Ideal.radical_eq_modal_denotation]
  apply Proposition.denotation_eq_of_equiv
  calc
    (◇(I.radical : Ideal R) : Proposition (Ideal R)) ≡[IdealEquiv] ◇◇I := by
      let pc : HasContext.Context (Proposition (Ideal R)) := Context.diamond .hole
      apply LawfulCongruence.covariant.elim pc (Ideal.radical_equiv_diamond I)
    _ ≡[IdealEquiv] ◇I := by apply Proposition.diamond_diamond_equiv

/-- In `idealPowerModel`, possibility of membership in an infimum is equivalent to simultaneous
possibility of membership in both ideals. -/
theorem Ideal.inf_modelEquiv [Semiring R] (I J : Ideal R) :
    (◇(I ⊓ J : Ideal R) : Proposition (Ideal R)) ≡[IdealEquiv] (◇I ∧ ◇J) := by
  calc
    (◇(I ⊓ J : Ideal R) : Proposition (Ideal R)) ≡[IdealEquiv] ◇(I ∧ J) := by
      let pc : HasContext.Context (Proposition (Ideal R)) := Context.diamond .hole
      exact LawfulCongruence.covariant.elim pc
        (Proposition.ofContainers_inf_equiv (PosPow R) I J (by simp))
    _ ≡[IdealEquiv] (◇I ∧ ◇J) := Proposition.ofSMul_diamond_and_equiv I J

/-- Radicals of ideals distribute over intersection, as a consequence that `◇(I ⊓ J)` is logically
equivalent to `◇I ∧ ◇J`. -/
theorem Ideal.radical_inf [CommSemiring R] (I J : Ideal R) :
    (I ⊓ J).radical = I.radical ⊓ J.radical := by
  apply SetLike.ext'
  simp_rw [Submodule.coe_inf, Ideal.radical_eq_modal_denotation,
    Proposition.denotation_eq_of_equiv (Ideal.inf_modelEquiv I J)]
  rfl

end CslibTests
