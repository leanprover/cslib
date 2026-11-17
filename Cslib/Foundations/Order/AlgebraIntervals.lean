/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.LatticeIntervals

/-! # Algebra instances on intervals -/

@[expose] public section

variable {α : Type*}

@[simps!]
instance Set.Iic.instCoheytingAlgebra [GeneralizedCoheytingAlgebra α] {a : α} :
    CoheytingAlgebra (Set.Iic a) where
  sdiff x y := ⟨(x : α) \ y, sdiff_le.trans x.prop⟩
  sdiff_le_iff _ _ _ := sdiff_le_iff (α := α)
  hnot x := ⟨a \ x, sdiff_le⟩
  top_sdiff _ := rfl

@[simps!]
instance Set.Ici.instHeytingAlgebra [GeneralizedHeytingAlgebra α] {a : α} :
    HeytingAlgebra (Set.Ici a) where
  himp x y := ⟨(x : α) ⇨ y, y.prop.trans le_himp⟩
  le_himp_iff _ _ _ := le_himp_iff (α := α)
  compl x := ⟨(x : α) ⇨ a, le_himp⟩
  himp_bot _ := rfl

@[simps! compl]
instance Set.Iic.instBooleanAlgebra [GeneralizedBooleanAlgebra α] {a : α} :
    BooleanAlgebra (Set.Iic a) where
  __ := Set.Iic.instBoundedOrderElemOfOrderBot
  compl x := ⟨a \ x, sdiff_le⟩
  inf_compl_le_bot _ := inf_sdiff_self_right.le
  top_le_sup_compl _ := le_sup_sdiff
  sdiff_eq x y := by
    ext
    change (x : α) \ y = (x : α) ⊓ a \ y
    rw [inf_sdiff_left_comm, inf_of_le_right (sdiff_le.trans x.prop)]
