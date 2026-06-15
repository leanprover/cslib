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
effect handler `F ι → PredTrans ps ι` to a unique monad morphism `liftM H`,
so weakest preconditions are compositional in `FreeM`'s monadic structure. A
`[FreeM.WP F ps]` instance plugs `FreeM F` into `Std.Do`'s `WP`/`WPMonad`/`Triple`
infrastructure.

The WP's structural rules are immediate from `liftM` being a monad morphism; the
adequacy theorem `liftM_wp_eq_wp_liftM` — that WP-via-handler agrees with
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

variable {F : Type u → Type v} {ps : PostShape.{u}} {α β : Type u}

/-- Adequacy theorem: WP via `FreeM` against a WP-derived handler agrees with
`Std.Do`'s WP of the `liftM` interpretation. Equivalently, two monad morphisms
`FreeM F → PredTrans ps` extending the same handler are equal. -/
theorem liftM_wp_eq_wp_liftM
    {m : Type u → Type w} [Monad m] [WPMonad m ps]
    (interp : ∀ ι : Type u, F ι → m ι) (x : FreeM F α) :
    x.liftM (fun {ι} op => wp (interp ι op)) =
      wp (x.liftM (fun {_} => interp _)) := by
  induction x with
  | pure a => simp [WPMonad.wp_pure]
  | lift_bind op k ih =>
    simp [WPMonad.wp_bind, ih]

/-- Records a default logical handler for `F` at shape `ps`, enabling the global
`WP (FreeM F) ps` instance and any `Triple`/`mvcgen` reasoning over `FreeM F`. -/
class WP (F : Type u → Type v) (ps : outParam (PostShape.{u})) where
  /-- The default logical handler for `F`. -/
  handler {ι : Type u} : F ι → PredTrans ps ι

instance instStdDoWP [WP F ps] : Std.Do.WP (FreeM F) ps where
  wp x := x.liftM WP.handler

instance instWPMonadFreeM [WP F ps] : WPMonad (FreeM F) ps where
  wp_pure _ := rfl
  wp_bind x f := liftM_bind _ x f

end FreeM

end Cslib
