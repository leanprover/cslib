/-
Copyright (c) 2025 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.Foundations.Control.Monad.Free
public import Std.Do.PredTrans
public import Std.Do.WP.Basic
public import Std.Do.WP.Monad
public import Std.Do.Triple

/-!
# Weakest preconditions for `FreeM` programs

Weakest-precondition interpretation of `FreeM F` programs through `Std.Do`'s
predicate-transformer monad `PredTrans ps`. The universal property of `FreeM` lifts any
effect handler `F ι → PredTrans ps ι` to a unique monad morphism `wpH H = liftM H`,
so weakest preconditions are compositional in `FreeM`'s monadic structure. A
`[HasHandler F ps]` instance plugs `FreeM F` into `Std.Do`'s `WP`/`WPMonad`/`Triple`
infrastructure.

The WP's structural rules (`wpH_pure`, `wpH_bind`, …) are immediate from `liftM` being a monad
morphism; the adequacy theorem `wpH_ofInterp_eq_wp_liftM` — that WP-via-handler agrees with
`Std.Do`'s WP of the `liftM` interpretation — is the same statement of uniqueness.

The design follows [Vistrup, Sammler, Jung. *Program Logics à la Carte.* POPL 2025], adapted
from coinductive ITrees to inductive `FreeM` and from Iris to `Std.Do`.
-/

@[expose] public section

set_option mvcgen.warning false

namespace Cslib

open Std.Do

namespace FreeM

universe u v w

variable {F G : Type u → Type v} {ps : PostShape.{u}} {α β : Type u}

/-- A logical handler: an effect handler from `F` into the predicate-transformer monad
`PredTrans ps`. -/
abbrev LHandler (F : Type u → Type v) (ps : PostShape.{u}) : Type (max (u + 1) v) :=
  ∀ {ι : Type u}, F ι → PredTrans ps ι

namespace LHandler

/-- Sum of handlers; the counterpart of the paper's `H₁ ⊕ H₂`. -/
def sum (H₁ : LHandler F ps) (H₂ : LHandler G ps) :
    LHandler (fun α => F α ⊕ G α) ps :=
  fun op => Sum.elim H₁ H₂ op

@[simp] theorem sum_inl (H₁ : LHandler F ps) (H₂ : LHandler G ps)
    {ι : Type u} (x : F ι) :
    LHandler.sum H₁ H₂ (Sum.inl x : F ι ⊕ G ι) = H₁ x := rfl

@[simp] theorem sum_inr (H₁ : LHandler F ps) (H₂ : LHandler G ps)
    {ι : Type u} (y : G ι) :
    LHandler.sum H₁ H₂ (Sum.inr y : F ι ⊕ G ι) = H₂ y := rfl

/-- Derive a logical handler from an effect handler into any `[WP m ps]` monad, by composing
with `m`'s WP. -/
def ofInterp {m : Type u → Type w} [WP m ps]
    (interp : ∀ ι : Type u, F ι → m ι) : LHandler F ps :=
  fun {ι} op => wp (interp ι op)

@[simp] theorem ofInterp_apply {m : Type u → Type w} [WP m ps]
    (interp : ∀ ι : Type u, F ι → m ι) {ι : Type u} (op : F ι) :
    LHandler.ofInterp interp op = wp (interp ι op) := rfl

end LHandler

/-- Weakest-precondition interpretation of a `FreeM F α` program against a logical handler `H`.
Defined as `FreeM.liftM` instantiated at `PredTrans ps`, the unique monad morphism
`FreeM F → PredTrans ps` extending `H` per the universal property of `FreeM`. -/
def wpH (H : LHandler F ps) (x : FreeM F α) : PredTrans ps α :=
  x.liftM H

@[simp] theorem wpH_pure (H : LHandler F ps) (a : α) :
    wpH H (pure a : FreeM F α) = Pure.pure a := rfl

@[simp] theorem wpH_liftBind (H : LHandler F ps) {ι : Type u}
    (op : F ι) (k : ι → FreeM F α) :
    wpH H (lift op >>= k) = H op >>= fun x => wpH H (k x) := rfl

@[simp] theorem wpH_lift (H : LHandler F ps) {ι : Type u} (op : F ι) :
    wpH H (lift op : FreeM F ι) = H op :=
  liftM_lift _ op

@[simp] theorem wpH_bind (H : LHandler F ps) (x : FreeM F α) (f : α → FreeM F β) :
    wpH H (x >>= f) = wpH H x >>= fun a => wpH H (f a) :=
  liftM_bind _ x f

/-- Adequacy theorem: WP via `FreeM` against an `ofInterp`-derived handler agrees with
`Std.Do`'s WP of the `liftM` interpretation. Equivalently, two monad morphisms
`FreeM F → PredTrans ps` extending the same handler are equal. -/
theorem wpH_ofInterp_eq_wp_liftM
    {m : Type u → Type w} [Monad m] [LawfulMonad m] [WPMonad m ps]
    (interp : ∀ ι : Type u, F ι → m ι) (x : FreeM F α) :
    wpH (LHandler.ofInterp interp) x = wp (x.liftM (fun {_} => interp _)) := by
  induction x with
  | pure a => simp [wpH, FreeM.liftM, WPMonad.wp_pure]
  | lift_bind op k ih =>
    simp [WPMonad.wp_bind, ih]

/-- Records a default logical handler for `F` at shape `ps`, enabling the global
`WP (FreeM F) ps` instance and any `Triple`/`mvcgen` reasoning over `FreeM F`. -/
class HasHandler (F : Type u → Type v) (ps : outParam (PostShape.{u})) where
  /-- The default logical handler for `F`. -/
  handler {ι : Type u} : F ι → PredTrans ps ι

instance instWPFreeM [HasHandler F ps] : WP (FreeM F) ps where
  wp := wpH HasHandler.handler

instance instWPMonadFreeM [HasHandler F ps] : WPMonad (FreeM F) ps where
  wp_pure _ := rfl
  wp_bind x f := wpH_bind _ x f

end FreeM

end Cslib
