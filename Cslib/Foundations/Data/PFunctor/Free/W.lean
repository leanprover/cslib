/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Polynomial free monads with an empty result type

When `α` is empty, a tree in `P.FreeM α` has only operation nodes. The equivalence
`PFunctor.FreeM.equivWOfIsEmpty` identifies these trees with the W-type `P.W`.
-/

@[expose] public section

universe uA uB u

namespace PFunctor

variable {P : PFunctor.{uA, uB}} {α : Type u}

/-- Regard a free polynomial tree with no return values as a W-type. -/
def FreeM.toWOfIsEmpty [IsEmpty α] : P.FreeM α → P.W
  | .pure a => isEmptyElim a
  | .liftBind a cont => W.mk (.mk a fun b => FreeM.toWOfIsEmpty (cont b))

/-- Regard a W-type as a free polynomial tree with no return nodes. -/
def W.toFreeM : P.W → P.FreeM α
  | ⟨a, cont⟩ => .liftBind a fun b => W.toFreeM (cont b)

@[simp]
theorem FreeM.toWOfIsEmpty_lift_bind [IsEmpty α] (a : P.A) (cont : P.B a → P.FreeM α) :
    toWOfIsEmpty ((lift a).bind (α := no_index (P.B a)) cont) =
      W.mk (.mk a fun b => toWOfIsEmpty (cont b)) := rfl

@[simp]
theorem FreeM.toWOfIsEmpty_lift_bind' {α : Type uB} [IsEmpty α] (a : P.A)
    (cont : P.B a → P.FreeM α) :
    toWOfIsEmpty (Bind.bind (α := no_index (P.B a)) (lift a) cont) =
      W.mk (.mk a fun b => toWOfIsEmpty (cont b)) := rfl

@[simp]
theorem W.toFreeM_mk (a : P.A) (cont : P.B a → P.W) :
    toFreeM (α := α) (W.mk (.mk a cont)) =
      (FreeM.lift a).bind (fun b => toFreeM (cont b)) := rfl

@[simp]
theorem FreeM.toWOfIsEmpty_toFreeM [IsEmpty α] (x : P.W) :
    toWOfIsEmpty (W.toFreeM (α := α) x) = x := by
  induction x with
  | mk a cont ih => exact congrArg (WType.mk a) (funext ih)

@[simp]
theorem W.toFreeM_toWOfIsEmpty [IsEmpty α] (x : P.FreeM α) :
    toFreeM (FreeM.toWOfIsEmpty x) = x := by
  induction x with
  | pure a => exact isEmptyElim a
  | lift_bind a cont ih => exact congrArg (FreeM.liftBind a) (funext ih)

/-- With an empty result type, the free polynomial monad is equivalent to its W-type. -/
@[simps]
def FreeM.equivWOfIsEmpty [IsEmpty α] : P.FreeM α ≃ P.W where
  toFun := toWOfIsEmpty
  invFun := W.toFreeM
  left_inv := W.toFreeM_toWOfIsEmpty
  right_inv := toWOfIsEmpty_toFreeM

end PFunctor
