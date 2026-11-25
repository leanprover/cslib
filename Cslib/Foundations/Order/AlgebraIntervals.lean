/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.LatticeIntervals

/-! # Algebra instances on intervals

This file defines `SDiff (Set.Iic a)` and `HImp (Set.Ici a)` for an element `a : α` in,
respectively, a co-Heyting or Heyting algebra. In the case that `α` is a (generalized) Boolean
algebra, this makes `Set.Iic a` a Boolean algebra.

Note that further instances of this sort can be defined, but the `SDiff` and `HImp` operations
cease to commute with the coercions. As it stands, only the instances necessary for downstream use
are defined.
-/

@[expose] public section

variable {α : Type*}

@[simps! sdiff_coe hnot_coe]
instance Set.Iic.instCoheytingAlgebra [GeneralizedCoheytingAlgebra α] {a : α} :
    CoheytingAlgebra (Set.Iic a) where
  sdiff x y := ⟨(x : α) \ y, sdiff_le.trans x.prop⟩
  sdiff_le_iff _ _ _ := sdiff_le_iff (α := α)
  hnot x := ⟨a \ x, sdiff_le⟩
  top_sdiff _ := rfl

@[simps! himp_coe compl_coe]
instance Set.Ici.instHeytingAlgebra [GeneralizedHeytingAlgebra α] {a : α} :
    HeytingAlgebra (Set.Ici a) where
  himp x y := ⟨(x : α) ⇨ y, y.prop.trans le_himp⟩
  le_himp_iff _ _ _ := le_himp_iff (α := α)
  compl x := ⟨(x : α) ⇨ a, le_himp⟩
  himp_bot _ := rfl

@[simps! compl_coe]
instance Set.Iic.instBooleanAlgebra [GeneralizedBooleanAlgebra α] {a : α} :
    BooleanAlgebra (Set.Iic a) where
  __ := Set.Iic.instBoundedOrderElemOfOrderBot
  compl x := ⟨a \ x, sdiff_le⟩
  inf_compl_le_bot _ := inf_sdiff_self_right.le
  top_le_sup_compl _ := le_sup_sdiff
  sdiff_eq x y := by
    refine Subtype.ext (?_ : (x : α) \ y = (x : α) ⊓ a \ y)
    rw [inf_sdiff_left_comm, inf_of_le_right (sdiff_le.trans x.prop)]
