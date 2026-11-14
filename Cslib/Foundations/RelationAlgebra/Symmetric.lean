/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Basic

/-!
# Symmetric integral relation algebras

A relation algebra is *symmetric* when its converse is trivial, which we express with Mathlib's
`TrivialStar`. This module characterizes the integral symmetric relation algebras by the
conditions used in [Monk1964], who calls the algebras satisfying them "Lyndon algebras":

1. `(A, +, ·, -)` is a Boolean algebra,
2. `x ; (y ; z) = (x ; y) ; z`,
3. `x ; y = y ; x`,
4. `(x + y) ; z = x ; z + y ; z`,
5. `x ; 1' = x`,
6. `x˘ = x`,
7. `1' ≤ x ; y` if and only if `x · y ≠ 0`.

In this library the name *Lyndon algebra* is reserved for the concrete construction of
`Cslib.RelationAlgebra.AtomStructure.lyndon`, following modern usage.

## Main definitions and statements

* `Cslib.RelationAlgebra.ofMonk`: Monk's conditions define a relation algebra, which is integral
  (`Cslib.RelationAlgebra.isIntegral_ofMonk`) and has trivial converse
  (`Cslib.RelationAlgebra.trivialStar_ofMonk`).
* `Cslib.RelationAlgebra.IsIntegral.one_le_mul_iff`: conversely, Monk's condition (vii) holds in
  every integral relation algebra with trivial converse. Commutativity is
  `Cslib.RelationAlgebra.mul_comm`.

## References

* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

namespace Cslib.RelationAlgebra

section ofMonk

variable {α : Type*} [BooleanAlgebra α] [Mul α] [One α]

/-- A `RelationAlgebra` can be constructed from the conditions of [Monk1964]. The converse is the
identity function, which is condition (vi). -/
@[instance_reducible]
def ofMonk
    (mul_assoc : ∀ a b c : α, a * b * c = a * (b * c))
    (mul_comm : ∀ a b : α, a * b = b * a)
    (sup_mul : ∀ a b c : α, (a ⊔ b) * c = a * c ⊔ b * c)
    (mul_one : ∀ a : α, a * 1 = a)
    (one_le_mul_iff : ∀ a b : α, 1 ≤ a * b ↔ a ⊓ b ≠ ⊥) : RelationAlgebra α where
  __ := ‹BooleanAlgebra α›
  mul_assoc := mul_assoc
  one_mul a := by rw [mul_comm, mul_one]
  mul_one := mul_one
  star := id
  star_involutive _ := rfl
  star_mul := mul_comm
  sup_mul := sup_mul
  star_sup _ _ := rfl
  tarski a b := by
    change a * (a * b)ᶜ ≤ bᶜ
    rw [le_compl_iff_disjoint_right, disjoint_iff]
    by_contra hne
    have h : 1 ≤ a * (a * b)ᶜ * b := (one_le_mul_iff _ _).mpr hne
    rw [mul_comm a, mul_assoc] at h
    exact (one_le_mul_iff _ _).mp h compl_inf_eq_bot

variable (mul_assoc : ∀ a b c : α, a * b * c = a * (b * c))
  (mul_comm : ∀ a b : α, a * b = b * a)
  (sup_mul : ∀ a b c : α, (a ⊔ b) * c = a * c ⊔ b * c)
  (mul_one : ∀ a : α, a * 1 = a)
  (one_le_mul_iff : ∀ a b : α, 1 ≤ a * b ↔ a ⊓ b ≠ ⊥)

/-- The converse of a relation algebra constructed from Monk's conditions is trivial. -/
theorem trivialStar_ofMonk :
    @TrivialStar α (ofMonk mul_assoc mul_comm sup_mul mul_one one_le_mul_iff).toStar :=
  @TrivialStar.mk α (ofMonk mul_assoc mul_comm sup_mul mul_one one_le_mul_iff).toStar fun _ => rfl

/-- A relation algebra constructed from Monk's conditions is integral. -/
theorem isIntegral_ofMonk :
    @IsIntegral α (ofMonk mul_assoc mul_comm sup_mul mul_one one_le_mul_iff) := by
  let _ := ofMonk mul_assoc mul_comm sup_mul mul_one one_le_mul_iff
  refine ⟨fun h1 => ?_, fun b hb => ?_⟩
  · exact (one_le_mul_iff ⊥ ⊥).mp (h1.trans_le bot_le) (inf_idem ⊥)
  · by_contra hne
    have hbb : 1 ≤ b * b := (one_le_mul_iff b b).mpr (by rwa [inf_idem])
    have hle : b * b ≤ b := (mul_le_mul_right hb.le b).trans_eq (mul_one b)
    exact hb.not_ge (hbb.trans hle)

end ofMonk

variable {α : Type*} [RelationAlgebra α]

/-- Condition (vii) of [Monk1964] holds in every integral relation algebra with trivial
converse. -/
theorem IsIntegral.one_le_mul_iff [TrivialStar α] (h : IsIntegral α) {a b : α} :
    1 ≤ a * b ↔ a ⊓ b ≠ ⊥ := by
  constructor
  · intro hab hbot
    have hle : (1 : α) ≤ ⊥ := calc
      1 = a * b ⊓ 1 := (inf_eq_right.mpr hab).symm
      _ ≤ a * (b ⊓ star a * 1) := left_modular a b 1
      _ = ⊥ := by rw [mul_one, star_trivial, inf_comm, hbot, mul_bot]
    exact IsAtom.ne_bot h (le_bot_iff.mp hle)
  · intro hne
    calc
      1 ≤ star (a ⊓ b) * (a ⊓ b) := h.one_le_star_mul_self hne
      _ = (a ⊓ b) * (a ⊓ b) := by rw [star_trivial]
      _ ≤ a * b := mul_le_mul' inf_le_left inf_le_right

end Cslib.RelationAlgebra
