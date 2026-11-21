/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.RelationAlgebra.SpecialElements

/-! # Relativization of a relation algebra

This file provides a relation algebra instance on `Set.Iic a`, for `a : α` a symmetric and
transitive element of a relation algebra.

## References

- [S. Givant, *Introduction to Relation Algebras: Relation Algebras, Volume 1*][Givant2017a],
chapter 10.
-/

@[expose] public section

open Cslib RelationAlgebra

variable {α : Type*} [RelationAlgebra α]

private lemma Cslib.RelationAlgebra.inf_one_mul_eq {a x : α} (h : x ≤ a)
    [IsRelSymm a] [IsRelTrans a] : (a ⊓ 1) * x = x := by
  apply le_antisymm
  · grw [inf_le_right, one_mul]
  · have : x ≤ (1 ⊓ x * star x) * x := by simpa using right_modular 1 x x
    nth_grw 1 [this, inf_comm, h, h, star_eq_of_symm a, mul_self_le_of_trans a]

/-- The **Relativization** of a relation algebra to a symmetric and transitive element `a`. -/
@[simps! one_coe mul_coe star_coe]
instance Set.Iic.instRelationAlgebra (a : α) [IsRelSymm a] [IsRelTrans a] :
    RelationAlgebra (Set.Iic a) where
  one := ⟨a ⊓ 1, inf_le_left⟩
  mul x y := ⟨(x : α) * y, mul_le_of_isRelTrans x.prop y.prop⟩
  mul_assoc x y z := Subtype.ext <| mul_assoc (x : α) y z
  one_mul x := private_decl% (Subtype.ext <| inf_one_mul_eq x.prop)
  mul_one x := by
    refine Subtype.ext (star_injective ?_ : x * (a ⊓ 1) = x)
    simpa [star_eq_of_symm] using inf_one_mul_eq (star_le_iff_of_isRelSymm.mpr x.prop)
  star x := ⟨star (x : α), star_le_iff_of_isRelSymm.mpr x.prop⟩
  star_involutive x := Subtype.ext <| star_involutive (x : α)
  star_mul x y := Subtype.ext <| star_mul (x : α) y
  sup_mul x y z := Subtype.ext <| sup_mul (x : α) y z
  star_sup x y := Subtype.ext <| star_sup (x : α) y
  tarski x y := by
    change star (x : α) * (a \ (x * y)) ≤ a \ y
    grw [_root_.sdiff_eq, _root_.sdiff_eq, mul_inf_le, tarski, (show x ≤ a from x.prop),
      star_eq_of_symm a, mul_self_le_of_trans a]
