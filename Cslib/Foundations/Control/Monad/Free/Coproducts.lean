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
free monads. Its interpreter handles each operation using the corresponding component.

## References

* [Wouter Swierstra, *Data types à la carte*, §6][Swierstra2008]
-/

@[expose] public section

namespace Cslib.FreeM

universe u v

variable {F G : Type u → Type v}

/-- Include computations using the left effect signature into the combined free monad. -/
def inl {α : Type u} : FreeM F α → FreeM (fun β => Sum (F β) (G β)) α :=
  FreeM.liftM (fun op => lift (F := fun β => Sum (F β) (G β)) (Sum.inl op))

/-- Include computations using the right effect signature into the combined free monad. -/
def inr {α : Type u} : FreeM G α → FreeM (fun β => Sum (F β) (G β)) α :=
  FreeM.liftM (fun op => lift (F := fun β => Sum (F β) (G β)) (Sum.inr op))

/-- The left inclusion preserves monadic structure. -/
theorem isMonadHom_inl :
    IsMonadHom (FreeM F) (FreeM (fun β => Sum (F β) (G β))) inl :=
  isMonadHom_liftM _

/-- The right inclusion preserves monadic structure. -/
theorem isMonadHom_inr :
    IsMonadHom (FreeM G) (FreeM (fun β => Sum (F β) (G β))) inr :=
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

/-- The free monad on a sum of effect signatures is a coproduct of their free monads. -/
theorem isMonadCoproduct :
    IsMonadCoproduct (FreeM F) (FreeM G)
      (FreeM (fun β => Sum (F β) (G β))) inl inr where
  inl_hom := isMonadHom_inl
  inr_hom := isMonadHom_inr
  universal t _ _ f g hf hg := by
    let handler : ∀ {α}, Sum (F α) (G α) → t α :=
      fun op => Sum.elim (fun x => f (lift x)) (fun x => g (lift x)) op
    apply ExistsUnique.intro (fun {_} x => FreeM.liftM handler x)
    · exact ⟨isMonadHom_liftM handler,
        fun x => by simp [inl, liftM_comp, handler, ← hf.map_freeMLiftM],
        fun x => by simp [inr, liftM_comp, handler, ← hg.map_freeMLiftM]⟩
    · intro k hk
      funext α x
      induction x with
      | pure a => exact hk.1.map_pure a
      | lift_bind op cont ih =>
        simp only [bind_eq_bind, hk.1.map_bind, liftM_lift_bind, ih]
        cases op with
        | inl op => rw [← inl_lift op, hk.2.1]; rfl
        | inr op => rw [← inr_lift op, hk.2.2]; rfl

end Cslib.FreeM
