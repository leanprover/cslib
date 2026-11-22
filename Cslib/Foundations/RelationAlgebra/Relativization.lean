/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.RelationAlgebra.Hom
public import Cslib.Foundations.RelationAlgebra.SpecialElements

/-! # Relativization of a relation algebra

This file provides a relation algebra instance on `Set.Iic a`, for `a : α` a symmetric and
transitive element of a relation algebra.

## References

- [S. Givant, *Introduction to Relation Algebras: Relation Algebras, Volume 1*][Givant2017a],
chapter 10.
-/

@[expose] public section

namespace Cslib

open RelationAlgebra Set

variable {α β : Type*} [RelationAlgebra α] [RelationAlgebra β]

private lemma RelationAlgebra.inf_one_mul_eq {a x : α} (h : x ≤ a)
    [IsRelSymm a] [IsRelTrans a] : (a ⊓ 1) * x = x := by
  apply le_antisymm
  · grw [inf_le_right, one_mul]
  · have : x ≤ (1 ⊓ x * star x) * x := by simpa using right_modular 1 x x
    nth_grw 1 [this, inf_comm, h, h, star_eq_of_symm a, mul_self_le_of_trans a]

/-- The **Relativization** of a relation algebra to a symmetric and transitive element `a`. -/
@[simps! one_coe mul_coe star_coe]
instance _root_.Set.Iic.instRelationAlgebra (a : α) [IsRelSymm a] [IsRelTrans a] :
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

/-- A homomorphism from `α` to `β` restricts to the relativization. If `b` is reducibly equal to
`f a`, then `f.restrictIic (refl a)` can find the required instances on `b` by synthesis. -/
@[simps]
def RelationAlgebraHom.restrictIic (f : RelationAlgebraHom α β) {a : α} [IsRelSymm a]
    [IsRelTrans a] {b : β} [IsRelSymm b] [IsRelTrans b] (h : f a = b) :
    RelationAlgebraHom (Iic a) (Iic b) where
  toFun x := ⟨f x, (f.mono x.prop).trans_eq h⟩
  map_sup' _ _ := Subtype.ext <| map_sup f ..
  map_inf' _ _ := Subtype.ext <| map_inf f ..
  map_mul' _ _ := Subtype.ext <| map_mul f ..
  map_star' _ := Subtype.ext <| map_star f ..
  map_top' := Subtype.ext h
  map_bot' := Subtype.ext <| map_bot f ..
  map_one' := Subtype.ext <| by simp [h]

/-- An equivalence between `α` and `β` restricts to the relativization. If `b` is reducibly equal to
`f a`, then `e.restrictIic (refl a)` can find the required instances on `b` by synthesis. -/
@[simps!]
def RelationAlgebraEquiv.restrictIic (e : RelationAlgebraEquiv α β) {a : α} [IsRelSymm a]
    [IsRelTrans a] {b : β} [IsRelSymm b] [IsRelTrans b] (h : e a = b) :
    RelationAlgebraEquiv (Iic a) (Iic b) := by
  have hsymm : e.symm.toHom b = a := by simpa using congr(e.symm $h.symm)
  refine .ofHomInv (e.toHom.restrictIic h) (e.symm.toHom.restrictIic hsymm) ?_ ?_
  · intro ⟨x, hx⟩
    ext; simp [e.toHom.restrictIic_apply_coe h]
  · intro ⟨x, hx⟩
    ext; simp [e.symm.toHom.restrictIic_apply_coe hsymm, e.toHom.restrictIic_apply_coe h]

end Cslib
