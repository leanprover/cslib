/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Polynomial free monads as W-types

A tree in `P.FreeM α` is a W-tree whose nodes either return a value of `α` or perform an operation
of `P`: `PFunctor.FreeM.equivW` identifies `P.FreeM α` with the W-type of `C α + P`, the
polynomial of the functor `X ↦ α ⊕ P X` whose initial algebra is the free monad.

When `α` is empty, a tree has only operation nodes, and `PFunctor.FreeM.equivWOfIsEmpty` identifies
these trees with the W-type `P.W` itself.
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

/-- Regard a free program as a W-tree of `C α + P`, whose leaves carry the returned values. -/
def FreeM.toW : P.FreeM α → (C.{u, uB} α + P).W
  | .pure a => W.mk (.mk (.inl a) PEmpty.elim)
  | .liftBind a cont => W.mk (.mk (.inr a) fun b => FreeM.toW (cont b))

/-- Read a W-tree of `C α + P` as a free program. -/
def FreeM.ofW : (C.{u, uB} α + P).W → P.FreeM α
  | WType.mk (.inl a) _ => .pure a
  | WType.mk (.inr a) cont => .liftBind a fun b => FreeM.ofW (cont b)

@[simp]
theorem FreeM.toW_pure (a : α) :
    toW (pure a : P.FreeM α) = (W.mk (.mk (.inl a) PEmpty.elim) : (C.{u, uB} α + P).W) := rfl

@[simp]
theorem FreeM.toW_lift_bind (a : P.A) (cont : P.B a → P.FreeM α) :
    toW ((lift a).bind (α := no_index (P.B a)) cont) =
      (W.mk (.mk (.inr a) fun b => toW (cont b)) : (C.{u, uB} α + P).W) := rfl

@[simp]
theorem FreeM.toW_lift_bind' {α : Type uB} (a : P.A) (cont : P.B a → P.FreeM α) :
    toW (Bind.bind (α := no_index (P.B a)) (lift a) cont) =
      (W.mk (.mk (.inr a) fun b => toW (cont b)) : (C.{uB, uB} α + P).W) := rfl

@[simp]
theorem FreeM.ofW_toW (x : P.FreeM α) : ofW (toW x) = x := by
  induction x with
  | pure a => rfl
  | lift_bind a cont ih => exact congrArg (liftBind a) (funext ih)

@[simp]
theorem FreeM.toW_ofW (w : (C.{u, uB} α + P).W) : toW (ofW w) = w := by
  induction w with
  | mk a f ih =>
    cases a with
    | inl a => exact congrArg (fun f => (W.mk (.mk (.inl a) f) : (C α + P).W)) (funext (·.elim))
    | inr a => exact congrArg (fun f => (W.mk (.mk (.inr a) f) : (C α + P).W)) (funext ih)

/-- Free programs are the W-trees of `C α + P`. -/
@[simps]
def FreeM.equivW : P.FreeM α ≃ (C.{u, uB} α + P).W where
  toFun := toW
  invFun := ofW
  left_inv := ofW_toW
  right_inv := toW_ofW

end PFunctor
