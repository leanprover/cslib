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
public import Std.Do.WP.Adequate
public import Std.Do.Triple

/-!
# Weakest preconditions for `FreeM` programs

Weakest-precondition interpretation of `FreeM F` programs through `Std.Do`'s
predicate-transformer monad `PredTrans ps`. The universal property of `FreeM` lifts any
effect handler `F ι → PredTrans ps ι` to a unique monad morphism `liftM H`,
so weakest preconditions are compositional in `FreeM`'s monadic structure. A
`[FreeM.WP F ps]` instance plugs `FreeM F` into `Std.Do`'s `WP`/`WPMonad`/`Triple`
infrastructure.

The WP's structural rules are immediate from `liftM` being a monad morphism. The
coherence lemma `liftM_wp_eq_wp_liftM` states that WP-via-handler agrees with `Std.Do`'s WP of the
`liftM` interpretation, i.e. uniqueness of the lifted monad morphism. From it we derive
`ensures_liftM_of_wp`: a `wp`-provable postcondition holds for the program's interpretation into
any `WPAdequate` monad.

The design follows [VistrupSammlerJung2025], adapted from coinductive ITrees to inductive `FreeM`
and from Iris to `Std.Do`.

## Main results

- `liftM_wp_eq_wp_liftM`: WP-via-handler coincides with `Std.Do`'s WP of the `liftM`
  interpretation (uniqueness/coherence of the lifted monad morphism).
- `ensures_liftM_of_wp`: a `wp`-provable postcondition holds (as `Internal.Ensures`) for the
  program's interpretation into a `WPAdequate` monad.
- `wp_lift`: `wp` of a single lifted operation is the handler applied to it.

## References

See [VistrupSammlerJung2025] for the original account on ITree program logics.
-/

@[expose] public section

set_option mvcgen.warning false

namespace Cslib

open Std.Do

namespace FreeM

universe u v w

variable {F : Type u → Type v} {ps : PostShape.{u}} {α β : Type u}

/-- Coherence/uniqueness lemma: WP via `FreeM` against a WP-derived handler agrees with
`Std.Do`'s WP of the `liftM` interpretation. Equivalently, two monad morphisms
`FreeM F → PredTrans ps` extending the same handler are equal. This is the bridge from which the
entails-style adequacy lemma `ensures_liftM_of_wp` is derived. -/
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
protected class WP (F : Type u → Type v) (ps : outParam (PostShape.{u})) where
  /-- The default logical handler for `F`. -/
  handler {ι : Type u} : F ι → PredTrans ps ι

instance WP.toDoWP [FreeM.WP F ps] : WP (FreeM F) ps where
  wp x := x.liftM FreeM.WP.handler

instance [FreeM.WP F ps] : WPMonad (FreeM F) ps where
  wp_pure _ := rfl
  wp_bind x f := liftM_bind _ x f

/-- `wp` of a single lifted operation is the handler applied to that operation. -/
@[simp]
theorem wp_lift [FreeM.WP F ps] (op : F α) :
    wp (lift op : FreeM F α) = FreeM.WP.handler op :=
  liftM_lift (m := PredTrans ps) FreeM.WP.handler op

/-- If `wp⟦x⟧` proves postcondition `P`, then `x` interpreted into any `WPAdequate` monad `m`
via `interp` satisfies `Internal.Ensures P`. Follows from `liftM_wp_eq_wp_liftM` and `m`'s
adequacy. -/
theorem ensures_liftM_of_wp
    {m : Type u → Type w} [Monad m] [WPMonad m ps] [WPAdequate m ps]
    (interp : ∀ ι : Type u, F ι → m ι) (x : FreeM F α) {P : α → Prop}
    (hwp : ⊢ₛ (x.liftM (fun {ι} op => wp (interp ι op))).apply (⇓? a => ⌜P a⌝)) :
    Internal.Ensures P (x.liftM (fun {_} => interp _)) :=
  WPAdequate.ensures_of_wp (liftM_wp_eq_wp_liftM interp x ▸ hwp)

end FreeM

end Cslib
