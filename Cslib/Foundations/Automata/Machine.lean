/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.Data.Stream.Init

@[expose] public section

/-! # Category of machines

## References

* [J. A. Goguen, *Minimal realization of machines in closed categories*][Goguen1972]

-/

namespace CsLib.Automata

universe u

/-- Category of machines with objects as types and morphisms as stream functions. -/
def Machine := Type u

namespace Machine

variable {X Y Z : Machine.{u}}

/-- Homomorphism as a stream function. -/
def Hom (X Y : Machine.{u}) := Stream' X → Stream' Y

def id (X : Machine.{u}) : Stream' X → Stream' X := fun x => x

def comp (f : Hom X Y) (g : Hom Y Z) := g ∘ f

open CategoryTheory

instance : LargeCategory Machine where
  Hom
  id
  comp

def tensorObj (X Y : Machine.{u}) : Machine := X × Y

def tensorHom
    {X₁ Y₁ X₂ Y₂ : Machine.{u}}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂)
    (v : Stream' (X₁ × X₂)) :
    Stream' (Y₁ × Y₂) :=
  let x₁s := f (Stream'.map (fun p => p.1) v)
  let x₂s := g (Stream'.map (fun p => p.2) v)
  Stream'.zip Prod.mk x₁s x₂s

def whiskerLeft
    (X : Machine.{u}) {Y₁ Y₂ : Machine.{u}} : (Y₁ ⟶ Y₂) → (tensorObj X Y₁ ⟶ tensorObj X Y₂) :=
  tensorHom (𝟙 X)

def whiskerRight
    {X₁ X₂ : Machine.{u}} (f : X₁ ⟶ X₂) (Y : Machine.{u}) : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom f (𝟙 Y)

def tensorUnit : Machine := PUnit

section associators

def associator_hom : Stream' ((X × Y) × Z) → Stream' (X × (Y × Z)) :=
  Stream'.map fun ((a, b), c) => (a, (b, c))

def associator_inv : Stream' (X × (Y × Z)) → Stream' ((X × Y) × Z) :=
  Stream'.map fun (a, (b, c)) => ((a, b), c)

theorem associator_hom_inv : associator_hom ≫ associator_inv = 𝟙 (tensorObj (tensorObj X Y) Z) :=
  rfl

theorem associator_inv_hom : associator_inv ≫ associator_hom = 𝟙 (tensorObj X (tensorObj Y Z)) :=
  rfl

def associator
    (X Y Z : Machine.{u}) : tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) where
  hom := associator_hom
  inv := associator_inv
  hom_inv_id := associator_hom_inv
  inv_hom_id := associator_inv_hom

end associators

def leftUnitor_hom : Stream' (PUnit × X) → Stream' X := Stream'.map Prod.snd

def leftUnitor_inv : Stream' X → Stream' (PUnit × X) := Stream'.map fun x => (PUnit.unit, x)

theorem leftUnitor_hom_inv_id : leftUnitor_hom ≫ leftUnitor_inv = 𝟙 (tensorObj tensorUnit X) := rfl

theorem leftUnitor_inv_hom_id : leftUnitor_inv ≫ leftUnitor_hom = 𝟙 X := rfl

def leftUnitor (X : Machine.{u}) : tensorObj tensorUnit X ≅ X where
  hom := leftUnitor_hom
  inv := leftUnitor_inv
  hom_inv_id := leftUnitor_hom_inv_id
  inv_hom_id := leftUnitor_inv_hom_id

def rightUnitor_hom : Stream' (X × PUnit) → Stream' X := Stream'.map Prod.fst

def rightUnitor_inv : Stream' X → Stream' (X × PUnit) := Stream'.map fun x => (x, PUnit.unit)

theorem rightUnitor_hom_inv_id : rightUnitor_hom ≫ rightUnitor_inv = 𝟙 (tensorObj X tensorUnit) :=
  rfl

theorem rightUnitor_inv_hom_id : rightUnitor_inv ≫ rightUnitor_hom = 𝟙 X := rfl

def rightUnitor (X : Machine.{u}) : tensorObj X tensorUnit ≅ X where
  hom := rightUnitor_hom
  inv := rightUnitor_inv
  hom_inv_id := rightUnitor_hom_inv_id
  inv_hom_id := rightUnitor_inv_hom_id

instance : MonoidalCategory Machine where
  tensorObj
  tensorHom
  whiskerLeft
  whiskerRight
  tensorUnit
  associator
  leftUnitor
  rightUnitor

open MonoidalCategory

def braiding_hom (X Y : Machine.{u}) : Stream' (X × Y) → Stream' (Y × X) := Stream'.map Prod.swap

theorem braiding_hom_inv_id (X Y : Machine.{u}) : braiding_hom X Y ≫ braiding_hom Y X = 𝟙 (X ⊗ Y) :=
  rfl

def braiding (X Y : Machine.{u}) : X ⊗ Y ≅ Y ⊗ X where
  hom := braiding_hom X Y
  inv := braiding_hom Y X
  hom_inv_id := braiding_hom_inv_id X Y
  inv_hom_id := braiding_hom_inv_id Y X

instance : SymmetricCategory Machine where
  braiding

def rightAdj {X : Machine.{u}} : Machine ⥤ Machine where
  obj Y := Stream' X → Y
  map f s n xs := f (fun m => s m xs) n

def toFun (f : (tensorLeft X).obj A ⟶ Y) (a : Stream' A) (n : ℕ) (xs : Stream' X) : Y :=
  f (Stream'.zip Prod.mk xs a) n

def invFun (g : Z ⟶ X.rightAdj.obj Y) (xas : Stream' (X × Z)) (n : ℕ) : Y :=
  g (Stream'.map Prod.snd xas) n (Stream'.map Prod.fst xas)

theorem left_inv (f : (tensorLeft X).obj A ⟶ Y) : invFun (toFun f) = f := rfl

theorem right_inv (g : A ⟶ X.rightAdj.obj Y) : toFun (invFun g) = g := rfl

def inv : ((tensorLeft X).obj A ⟶ Y) ≃ (A ⟶ X.rightAdj.obj Y) where
  toFun
  invFun
  left_inv
  right_inv

def adj_eq : (Y Z : Machine.{u}) → ((tensorLeft X).obj Y ⟶ Z) ≃ (Y ⟶ X.rightAdj.obj Z) :=
  fun _ _ => inv

open Adjunction

def adj_hom_eq : CoreHomEquiv (tensorLeft X) X.rightAdj where
  homEquiv := adj_eq

def adj : tensorLeft X ⊣ X.rightAdj := mkOfHomEquiv adj_hom_eq

@[implicit_reducible]
def closed (X : Machine.{u}) : Closed X where
  rightAdj
  adj

instance : MonoidalClosed Machine where
  closed

end Machine

end CsLib.Automata
