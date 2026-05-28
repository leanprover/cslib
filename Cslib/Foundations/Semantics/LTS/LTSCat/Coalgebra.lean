/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.LTSCat.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Labelled transition systems as coalgebras

For a label set `L`, a labelled transition system on `X` is the same datum as a
coalgebra `α : X → Set (L × X)` for the `Set`-endofunctor `F_L X = Set (L × X)`.
This file defines `F_L` as an endofunctor of `Type u`, exhibits LTSs as
coalgebras via Mathlib's `CategoryTheory.Endofunctor.Coalgebra`, and proves
that Mathlib's coalgebra morphisms coincide with functional bisimulations on
the underlying LTSs.

## Main definitions

- `LTS.Endo`: the endofunctor `F_L X = Set (L × X)` on `Type u`.
- `LTS.Coalgebra.toLTSCat`: the forgetful functor from coalgebras of `F_L` to
  `LTSCat` that maps a functional bisimulation to its underlying simulation.

## Main results

- `LTS.Coalgebra.instFaithful`: `toLTSCat` is faithful.
- `LTS.Coalgebra.graphBisimEquiv`: coalgebra morphisms `V ⟶ W` are in bijection
  with the state maps `V.V → W.V` whose graph is a functional bisimulation
  between the underlying LTSs.

## References

* [J. Rutten, *Universal coalgebra: a theory of systems*][Rutten2000]
* [G. Winskel and M. Nielsen, *Models for concurrency*][WinskelNielsen1995]
-/

@[expose] public section

namespace Cslib

universe u

open CategoryTheory TypeCat Endofunctor

namespace LTS

/-- Action on morphisms of the LTS endofunctor: image of a set under
`(l, x) ↦ (l, f x)`. -/
def Endo.mapFn (Label : Type u) {X Y : Type u} (f : X → Y) (S : Set (Label × X)) :
    Set (Label × Y) :=
  {p | ∃ x : X, (p.1, x) ∈ S ∧ f x = p.2}

namespace Endo

variable {Label : Type u} {X Y Z : Type u}

@[simp] lemma mem_mapFn (f : X → Y) (S : Set (Label × X)) (p : Label × Y) :
    p ∈ mapFn Label f S ↔ ∃ x : X, (p.1, x) ∈ S ∧ f x = p.2 := Iff.rfl

lemma mapFn_id : mapFn Label (_root_.id : X → X) = _root_.id := by
  funext S
  ext ⟨l, x⟩
  constructor
  · rintro ⟨_, hw, rfl⟩
    exact hw
  · exact fun hx => ⟨x, hx, rfl⟩

lemma mapFn_comp (f : X → Y) (g : Y → Z) :
    mapFn Label (g ∘ f) = mapFn Label g ∘ mapFn Label f := by
  funext S
  ext ⟨l, z⟩
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

end Endo

/-- The `Set`-endofunctor `F_L X = Set (L × X)` on `Type u`. -/
@[reducible] def Endo (Label : Type u) : Type u ⥤ Type u where
  obj X := Set (Label × X)
  map {_ _} f := ofHom (Endo.mapFn Label f)
  map_id _ := by aesop
  map_comp f g := by aesop

/-- The category of LTS-coalgebras for a fixed label set, as Mathlib's
`Endofunctor.Coalgebra` applied to `Endo Label`. Morphisms are the strict
commuting-square coalgebra morphisms, which are precisely the functional
bisimulations on the underlying LTSs (see `Coalgebra.graph_isBisimulation` and
`Coalgebra.homOfGraphBisim`). -/
abbrev Coalgebra (Label : Type u) : Type (u + 1) := Endofunctor.Coalgebra (Endo Label)

namespace Coalgebra

variable {Label : Type u}

/-- The LTS underlying a coalgebra of `Endo Label`. -/
abbrev toLTS (V : Coalgebra Label) : LTS V.V Label where
  Tr s l s' := (l, s') ∈ (V.str : V.V → _) s

@[simp] lemma toLTS_Tr (V : Coalgebra Label) (s : V.V) (l : Label) (s' : V.V) :
    (toLTS V).Tr s l s' ↔ (l, s') ∈ (V.str : V.V → _) s := Iff.rfl

variable (Label) in
/-- The forgetful functor `Coalgebra Label ⥤ LTSCat` mapping each functional
bisimulation to its underlying simulation. -/
def toLTSCat : Coalgebra Label ⥤ LTSCat.{u, u} where
  obj V := ({ State := V.V, Label := Label, lts := toLTS V } : LTSCat.{u, u})
  map {V W} f :=
    { stateMap := (f.f : V.V → W.V)
      labelMap := pure
      labelMap_tr := by
        intro s s' l h
        have hcomm := ConcreteCategory.congr_hom f.h s
        simp_all only [types_comp_apply, Endo, ofHom_apply, withIdle, toLTS]
        rw [← hcomm]
        exact ⟨s', h, rfl⟩ }
  map_id _ := rfl
  map_comp _ _ := by
    apply Morphism.ext
    · rfl
    · exact (fish_pure pure).symm

/-- `toLTSCat` is faithful: a functional bisimulation is determined by its
underlying state map. -/
instance : (toLTSCat Label).Faithful where
  map_injective {_ _} _ _ h := by
    apply Endofunctor.Coalgebra.Hom.ext
    apply Hom.ext
    apply Fun.ext
    funext x
    exact congrFun (congrArg Morphism.stateMap h) x

/-- Mathlib's coalgebra morphisms are precisely the functional bisimulations of
the underlying LTSs. Forward direction: every coalgebra morphism, viewed as the
graph of its underlying state map, is an `LTS.IsBisimulation`. -/
theorem graph_isBisimulation {V W : Coalgebra Label} (f : V ⟶ W) :
    LTS.IsBisimulation (toLTS V) (toLTS W) (fun s t => (f.f : V.V → W.V) s = t) := by
  intro s t hst l
  have hcomm := ConcreteCategory.congr_hom f.h s
  simp_all only [types_comp_apply, Endo, ofHom_apply]
  constructor
  · intro s' h
    exact ⟨(f.f : V.V → W.V) s', hcomm ▸ ⟨s', h, rfl⟩, rfl⟩
  · intro t' h
    obtain ⟨s', hs', rfl⟩ := hcomm ▸ h
    exact ⟨s', hs', rfl⟩

/-- Backward direction: any function whose graph is an LTS bisimulation is the
underlying state map of a (unique) coalgebra morphism. -/
def homOfGraphBisim {V W : Coalgebra Label} (f : V.V → W.V)
    (h : LTS.IsBisimulation (toLTS V) (toLTS W) (fun s t => f s = t)) : V ⟶ W where
  f := ofHom f
  h := by
    apply Hom.ext
    apply Fun.ext
    funext s
    ext ⟨l, t'⟩
    simp only [Endo]
    constructor
    · rintro ⟨s', hs', rfl⟩
      obtain ⟨_, ht₂, rfl⟩ := (h rfl l).1 _ hs'
      exact ht₂
    · intro ht'
      obtain ⟨s', hs', rfl⟩ := (h rfl l).2 _ ht'
      exact ⟨s', hs', rfl⟩

/-- Coalgebra morphisms `V ⟶ W` are in bijection with the state maps `V.V → W.V` whose graph is
a functional bisimulation between the underlying LTSs. -/
def graphBisimEquiv {V W : Coalgebra Label} :
    (V ⟶ W) ≃
      { f : V.V → W.V //
          LTS.IsBisimulation (toLTS V) (toLTS W) (fun s t => f s = t) } where
  toFun φ := ⟨φ.f, graph_isBisimulation φ⟩
  invFun p := homOfGraphBisim p.1 p.2
  left_inv φ := by
    apply Endofunctor.Coalgebra.Hom.ext
    rfl
  right_inv _ := rfl

end Coalgebra

end LTS

end Cslib
