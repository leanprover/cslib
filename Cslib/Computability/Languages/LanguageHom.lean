/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Computability.Language

/-!
# Language homomorphism
-/

@[expose] public section

namespace Language

variable {α β : Type*}

/-- A language homomorphism from `α` to `β` is a map from `List α` to `List β` which
preserves the empty word `[]` and concatenation `(· ++ ·)`. -/
@[ext]
structure Hom (α β : Type*) where
  /-- The map of a language homomorphism. -/
  toFun : List α → List β
  map_nil' : toFun [] = []
  map_append' (as as' : List α) : toFun (as ++ as') = toFun as ++ toFun as'

/-- This is to support the function application notation for language homomorphisms. -/
instance : FunLike (Hom α β) (List α) (List β) where
  coe (f : Hom α β) := f.toFun
  coe_injective (_ _ : Hom α β) := by
    intro _
    ext1
    assumption

namespace Hom

theorem ext_iff' (f f' : Hom α β) :
    f = f' ↔ ∀ as, f as = f' as := by
  constructor
  · grind
  · intro h
    ext1
    ext1 as
    exact h as

@[simp, scoped grind =]
theorem map_nil (f : Hom α β) : f [] = [] := f.map_nil'

@[simp, scoped grind =]
theorem map_append (f : Hom α β) (as as' : List α) : f (as ++ as') = (f as) ++ (f as') :=
  f.map_append' as as'

@[scoped grind =]
theorem map_cons (f : Hom α β) (a : α) (as : List α) :
    f (a :: as) = f [a] ++ f as := by
  rw [← List.singleton_append, map_append]

/-- This auxiliary function should not be used outside this file.
Instead, use the equivalence `lift` below. -/
def liftAux (f : α → List β) : Hom α β where
  toFun := List.flatMap f
  map_nil' := List.flatMap_nil
  map_append' := fun _ _ ↦ List.flatMap_append

theorem liftAux_eq_flatMap (f : α → List β) : liftAux f = List.flatMap f :=
  rfl

theorem listAux_left_inv (f : α → List β) :
    (fun f a ↦ f [a]) (liftAux f) = f := by
  simp [liftAux_eq_flatMap]

theorem listAux_right_inv (f : Hom α β) :
    liftAux (fun a ↦ f [a]) = f := by
  rw [ext_iff']
  intro as
  induction as with
  | nil => simp [map_nil]
  | cons a as h_ind =>
    rw [map_cons f, ← h_ind]
    simp [liftAux_eq_flatMap]

/-- An equivalence from `f : α → List β` to `Hom α β`, whose forward direction can be
used to define language homomorphisms conveniently. -/
def lift : (α → List β) ≃ (Hom α β) where
  toFun := liftAux
  invFun := fun f a ↦ f [a]
  left_inv := listAux_left_inv
  right_inv := listAux_right_inv

/-- `lift.toFun` is in fact `List.flatMap`. -/
theorem lift_eq_flatMap (f : α → List β) : lift f = List.flatMap f :=
  rfl

end Hom

section ImagePreimage

/-- The image of a language under a function `f`, which need not be a language homomorphism. -/
def image (f : List α → List β) (l : Language α) : Language β :=
  f '' l

/-- The preimage of a language under a function `f`, which need not be a language homomorphism. -/
def preimage (f : List α → List β) (l : Language β) : Language α :=
  f ⁻¹' l

variable (f : List α → List β)

@[simp, scoped grind =]
theorem mem_image (l : Language α) (bs : List β) :
    bs ∈ l.image f ↔ ∃ as, as ∈ l ∧ f as = bs := by
  rfl

@[simp, scoped grind =]
theorem mem_preimage (l : Language β) (as : List α) :
    as ∈ l.preimage f ↔ f as ∈ l := by
  rfl

end ImagePreimage

end Language
