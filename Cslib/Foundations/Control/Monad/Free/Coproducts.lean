/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.Foundations.Control.Monad.Coproducts
public import Cslib.Foundations.Control.Monad.Free

/-!
# Coproducts of free monads

The free monad on the pointwise sum of two effect signatures is a coproduct of their
free monads, exposed as `FreeM.Coproduct F G`. Its interpreter handles each operation
using the corresponding component.

## References

* [Wouter Swierstra, *Data types à la carte*, §6][Swierstra2008]
-/

@[expose] public section

namespace Cslib.FreeM

universe u v w

/-- The coproduct of `FreeM F` and `FreeM G`, constructed as the free monad on the
pointwise sum of their underlying effect signatures.

The `Monad` and `LawfulMonad` instances are inherited from `FreeM`. The inclusions
`FreeM.inl` and `FreeM.inr` satisfy the universal property `FreeM.isMonadCoproduct`. -/
abbrev Coproduct (F G : Type u → Type v) (α : Type w) :=
  FreeM (fun β => Sum (F β) (G β)) α

variable {F G : Type u → Type v}

/-- Include computations using the left effect signature into the combined free monad. -/
def inl {α : Type u} : FreeM F α → Coproduct F G α :=
  FreeM.liftM (fun op => lift (F := fun β => Sum (F β) (G β)) (Sum.inl op))

/-- Include computations using the right effect signature into the combined free monad. -/
def inr {α : Type u} : FreeM G α → Coproduct F G α :=
  FreeM.liftM (fun op => lift (F := fun β => Sum (F β) (G β)) (Sum.inr op))

/-- The left inclusion preserves monadic structure. -/
theorem isMonadHom_inl :
    IsMonadHom (FreeM F) (Coproduct F G) inl :=
  isMonadHom_liftM _

/-- The right inclusion preserves monadic structure. -/
theorem isMonadHom_inr :
    IsMonadHom (FreeM G) (Coproduct F G) inr :=
  isMonadHom_liftM _

/-- The left inclusion sends a lifted operation to the corresponding left operation. -/
@[simp]
theorem inl_lift {α : Type u} (op : F α) :
    inl (G := G) (lift op) = lift (F := fun β => Sum (F β) (G β)) (Sum.inl op) :=
  liftM_lift _ _

/-- The right inclusion sends a lifted operation to the corresponding right operation. -/
@[simp]
theorem inr_lift {α : Type u} (op : G α) :
    inr (F := F) (lift op) = lift (F := fun β => Sum (F β) (G β)) (Sum.inr op) :=
  liftM_lift _ _

/-- The free monad on a sum of effect signatures is a coproduct of their free monads.
The interpreter `desc` handles each operation using the corresponding component. -/
def isMonadCoproduct :
    IsMonadCoproduct (FreeM F) (FreeM G) (Coproduct F G) inl inr where
  inl_hom := isMonadHom_inl
  inr_hom := isMonadHom_inr
  desc := @fun _ _ _ f g _ _ =>
    FreeM.liftM fun op => Sum.elim (fun x => f (lift x)) (fun x => g (lift x)) op
  isMonadHom_desc _ _ := isMonadHom_liftM _
  desc_inl := @fun _ _ _ _ _ hf _ _ x => by simp [inl, liftM_comp, ← hf.map_freeMLiftM]
  desc_inr := @fun _ _ _ _ _ _ hg _ x => by simp [inr, liftM_comp, ← hg.map_freeMLiftM]
  desc_unique := @fun _ _ _ _ _ _ _ _ hk hinl hinr => by
    funext α x
    induction x using FreeM.induction with
    | pure a => exact hk.map_pure a
    | lift_bind op cont ih =>
      simp only [bind_eq_bind, hk.map_bind, liftM_lift_bind, ih]
      cases op with
      | inl op => rw [← inl_lift op, hinl]; rfl
      | inr op => rw [← inr_lift op, hinr]; rfl

end Cslib.FreeM
