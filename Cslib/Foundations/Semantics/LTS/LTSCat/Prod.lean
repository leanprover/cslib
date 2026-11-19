/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

module

public import Cslib.Foundations.Semantics.LTS.LTSCat.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-! # Categorical Products of Labelled Transition Systems

This file constructs binary products and the terminal object (hence all finite products) in the
category `LTSCat` of labelled transition systems and partial-label morphisms, following Winskel
and Nielsen [WinskelNielsen1995].

In `LTSCat`, morphisms carry partial functions `L₁ → Option L₂` on labels. Categorically, the label
component lives in the Kleisli category of `Option` (sets and partial functions), where the binary
product of alphabets `L₁` and `L₂` is `LTS.ProdLabel L₁ L₂` (isomorphic to
`(L₁ × {∗}) ⊔ ({∗} × L₂) ⊔ (L₁ × L₂)`). Accordingly, transitions in the product LTS allow the left
component to step while the right idles (`ProdLabel.left`), the right component to step while the
left idles (`ProdLabel.right`), or both components to step synchronously (`ProdLabel.both`).

## Main definitions

* `LTS.ProdLabel`: The product label alphabet for categorical products of LTSs, together with
  partial projections `ProdLabel.fst`, `ProdLabel.snd` and partial pairing `ProdLabel.mkOption`.
* `LTS.catProd`: The categorical product of two `LTS` structures on `State₁ × State₂` and
  `LTS.ProdLabel Label₁ Label₂`.
* `LTSCat.prod`: The binary product object of two objects in `LTSCat`.
* `LTSCat.fst`, `LTSCat.snd`, `LTSCat.lift`: Projection and pairing morphisms in `LTSCat`.
* `LTSCat.prodBinaryFan`, `LTSCat.prodIsLimit`: The limit binary fan in `LTSCat`.
* `LTSCat.terminal`, `LTSCat.terminalIsTerminal`: The terminal object in `LTSCat` with a single
  state and empty label alphabet.

## Main results

* `LTSCat.hasBinaryProducts`: `LTSCat.{u, v}` has all binary products.
* `LTSCat.hasTerminal`: `LTSCat.{u, v}` has a terminal object.
* `LTSCat.hasFiniteProducts`: `LTSCat.{u, v}` has all finite products.

## References

* [G. Winskel and M. Nielsen, *Models for Concurrency*][WinskelNielsen1995]
-/

@[expose] public section

namespace Cslib

open CategoryTheory

universe u v u₁ u₂ v₁ v₂

namespace LTS

section WithIdle

variable {State : Type u} {Label : Type v} {lts : LTS State Label}

/-- An idle (`none`) step in `LTS.withIdle` holds if and only if the source and target states are
equal. -/
@[simp]
theorem withIdle_tr_none {s s' : State} :
    (withIdle lts).Tr s none s' ↔ s = s' :=
  Iff.rfl

/-- A labelled (`some μ`) step in `LTS.withIdle` holds if and only if the underlying LTS has that
transition. -/
@[simp]
theorem withIdle_tr_some {s s' : State} {μ : Label} :
    (withIdle lts).Tr s (some μ) s' ↔ lts.Tr s μ s' :=
  Iff.rfl

/-- Multistep transitions in `LTS.withIdle` correspond to multistep transitions in `lts` along the
non-idle labels. -/
@[simp]
theorem withIdle_mTr {s s' : State} {μs : List (Option Label)} :
    (withIdle lts).MTr s μs s' ↔ lts.MTr s (μs.filterMap id) s' := by
  induction μs generalizing s with
  | nil => simp
  | cons o μs ih => cases o <;> simp [MTr.cons_iff, ih]

end WithIdle

/-! ## Product label alphabet -/

/-- Synchronized or unsynchronized label pairs for the categorical binary product of LTSs.

In the Kleisli category of `Option` (sets and partial functions), `ProdLabel L₁ L₂` is the
binary product of `L₁` and `L₂`. -/
inductive ProdLabel (L₁ : Type v₁) (L₂ : Type v₂) : Type (max v₁ v₂) where
  /-- Left component transitions alone while right component idles. -/
  | left (l₁ : L₁)
  /-- Right component transitions alone while left component idles. -/
  | right (l₂ : L₂)
  /-- Both components transition synchronously. -/
  | both (l₁ : L₁) (l₂ : L₂)
  deriving DecidableEq

namespace ProdLabel

variable {L₁ : Type v₁} {L₂ : Type v₂}

instance [Inhabited L₁] : Inhabited (ProdLabel L₁ L₂) :=
  ⟨.left default⟩

instance [Nonempty L₁] : Nonempty (ProdLabel L₁ L₂) :=
  Nonempty.map .left ‹_›

/-- Partial projection onto the left label alphabet. -/
def fst : ProdLabel L₁ L₂ → Option L₁
  | .left l₁ => some l₁
  | .right _ => none
  | .both l₁ _ => some l₁

/-- Partial projection onto the right label alphabet. -/
def snd : ProdLabel L₁ L₂ → Option L₂
  | .left _ => none
  | .right l₂ => some l₂
  | .both _ l₂ => some l₂

/-- Combines two optional labels into an optional `ProdLabel`, returning `none` only when both
inputs are `none`. This is morphism pairing in the Kleisli category of `Option`. -/
def mkOption : Option L₁ → Option L₂ → Option (ProdLabel L₁ L₂)
  | none, none => none
  | some l₁, none => some (.left l₁)
  | none, some l₂ => some (.right l₂)
  | some l₁, some l₂ => some (.both l₁ l₂)

@[simp]
theorem fst_left (l₁ : L₁) : (left l₁ : ProdLabel L₁ L₂).fst = some l₁ :=
  rfl

@[simp]
theorem fst_right (l₂ : L₂) : (right l₂ : ProdLabel L₁ L₂).fst = none :=
  rfl

@[simp]
theorem fst_both (l₁ : L₁) (l₂ : L₂) : (both l₁ l₂).fst = some l₁ :=
  rfl

@[simp]
theorem snd_left (l₁ : L₁) : (left l₁ : ProdLabel L₁ L₂).snd = none :=
  rfl

@[simp]
theorem snd_right (l₂ : L₂) : (right l₂ : ProdLabel L₁ L₂).snd = some l₂ :=
  rfl

@[simp]
theorem snd_both (l₁ : L₁) (l₂ : L₂) : (both l₁ l₂).snd = some l₂ :=
  rfl

@[simp]
theorem mkOption_none_none : mkOption (none : Option L₁) (none : Option L₂) = none :=
  rfl

@[simp]
theorem mkOption_some_none (l₁ : L₁) :
    mkOption (some l₁) (none : Option L₂) = some (.left l₁) :=
  rfl

@[simp]
theorem mkOption_none_some (l₂ : L₂) :
    mkOption (none : Option L₁) (some l₂) = some (.right l₂) :=
  rfl

@[simp]
theorem mkOption_some_some (l₁ : L₁) (l₂ : L₂) :
    mkOption (some l₁) (some l₂) = some (.both l₁ l₂) :=
  rfl

/-- Projecting the first component after `ProdLabel.mkOption` recovers the first optional label. -/
@[simp]
theorem bind_fst (o₁ : Option L₁) (o₂ : Option L₂) : (mkOption o₁ o₂).bind fst = o₁ := by
  cases o₁ <;> cases o₂ <;> rfl

/-- Projecting the second component after `ProdLabel.mkOption` recovers the second optional
label. -/
@[simp]
theorem bind_snd (o₁ : Option L₁) (o₂ : Option L₂) : (mkOption o₁ o₂).bind snd = o₂ := by
  cases o₁ <;> cases o₂ <;> rfl

/-- Recombining the projections of a `ProdLabel` via `ProdLabel.mkOption` yields `some` of that
label. -/
@[simp]
theorem mkOption_fst_snd (μ : ProdLabel L₁ L₂) : mkOption μ.fst μ.snd = some μ := by
  cases μ <;> rfl

/-- Recombining the monadic projections of an optional `ProdLabel` recovers the original option. -/
@[simp]
theorem mkOption_bind_fst_bind_snd (o : Option (ProdLabel L₁ L₂)) :
    mkOption (o.bind fst) (o.bind snd) = o := by
  cases o <;> simp

/-- Two `ProdLabel` values are equal if their left and right partial projections coincide. -/
@[ext]
theorem ext {μ₁ μ₂ : ProdLabel L₁ L₂} (h₁ : μ₁.fst = μ₂.fst) (h₂ : μ₁.snd = μ₂.snd) :
    μ₁ = μ₂ := by
  cases μ₁ <;> cases μ₂ <;> simp_all

end ProdLabel

/-! ## Categorical product of LTSs -/

section CatProd

variable {State₁ : Type u₁} {Label₁ : Type v₁} {State₂ : Type u₂} {Label₂ : Type v₂}
  {lts₁ : LTS State₁ Label₁} {lts₂ : LTS State₂ Label₂}

/-- The categorical product of two labelled transition systems, allowing asynchronous transitions of
either component as well as synchronous transitions of both components [WinskelNielsen1995]. -/
def catProd (lts₁ : LTS State₁ Label₁) (lts₂ : LTS State₂ Label₂) :
    LTS (State₁ × State₂) (ProdLabel Label₁ Label₂) where
  Tr s μ s' := (withIdle lts₁).Tr s.1 μ.fst s'.1 ∧ (withIdle lts₂).Tr s.2 μ.snd s'.2

/-- Unfolded characterization of transitions in `LTS.catProd` in terms of `LTS.withIdle`. -/
theorem catProd_tr {s s' : State₁ × State₂} {μ : ProdLabel Label₁ Label₂} :
    (catProd lts₁ lts₂).Tr s μ s' ↔
      (withIdle lts₁).Tr s.1 μ.fst s'.1 ∧ (withIdle lts₂).Tr s.2 μ.snd s'.2 :=
  Iff.rfl

/-- A `ProdLabel.left` transition in `LTS.catProd` steps the first component and leaves the second
idle. -/
@[simp]
theorem catProd_tr_left {s s' : State₁ × State₂} {l₁ : Label₁} :
    (catProd lts₁ lts₂).Tr s (.left l₁) s' ↔ lts₁.Tr s.1 l₁ s'.1 ∧ s.2 = s'.2 :=
  Iff.rfl

/-- A `ProdLabel.right` transition in `LTS.catProd` leaves the first component idle and steps the
second. -/
@[simp]
theorem catProd_tr_right {s s' : State₁ × State₂} {l₂ : Label₂} :
    (catProd lts₁ lts₂).Tr s (.right l₂) s' ↔ s.1 = s'.1 ∧ lts₂.Tr s.2 l₂ s'.2 :=
  Iff.rfl

/-- A `ProdLabel.both` transition in `LTS.catProd` steps both components synchronously. -/
@[simp]
theorem catProd_tr_both {s s' : State₁ × State₂} {l₁ : Label₁} {l₂ : Label₂} :
    (catProd lts₁ lts₂).Tr s (.both l₁ l₂) s' ↔ lts₁.Tr s.1 l₁ s'.1 ∧ lts₂.Tr s.2 l₂ s'.2 :=
  Iff.rfl

/-- Transitions in `withIdle (catProd lts₁ lts₂)` along `ProdLabel.mkOption o₁ o₂` correspond to
pairs of `withIdle` transitions in `lts₁` and `lts₂`. -/
@[simp]
theorem withIdle_catProd_tr_mkOption {s s' : State₁ × State₂}
    {o₁ : Option Label₁} {o₂ : Option Label₂} :
    (withIdle (catProd lts₁ lts₂)).Tr s (ProdLabel.mkOption o₁ o₂) s' ↔
      (withIdle lts₁).Tr s.1 o₁ s'.1 ∧ (withIdle lts₂).Tr s.2 o₂ s'.2 := by
  cases o₁ <;> cases o₂ <;> simp [Prod.ext_iff]

/-- Projecting a multistep execution of `LTS.catProd` onto the first component yields a multistep
execution of `lts₁` along `μs.filterMap ProdLabel.fst`. -/
theorem catProd_mTr_fst {s s' : State₁ × State₂} {μs : List (ProdLabel Label₁ Label₂)}
    (h : (catProd lts₁ lts₂).MTr s μs s') :
    lts₁.MTr s.1 (μs.filterMap ProdLabel.fst) s'.1 := by
  induction h with
  | refl => exact .refl
  | @stepL s₁ μ s₂ μs s₃ htr _ ih =>
    cases μ with
    | left l₁ =>
      simp only [List.filterMap_cons, ProdLabel.fst_left]
      exact .stepL htr.1 ih
    | right l₂ =>
      simp only [List.filterMap_cons, ProdLabel.fst_right]
      exact htr.1 ▸ ih
    | both l₁ l₂ =>
      simp only [List.filterMap_cons, ProdLabel.fst_both]
      exact .stepL htr.1 ih

/-- Projecting a multistep execution of `LTS.catProd` onto the second component yields a multistep
execution of `lts₂` along `μs.filterMap ProdLabel.snd`. -/
theorem catProd_mTr_snd {s s' : State₁ × State₂} {μs : List (ProdLabel Label₁ Label₂)}
    (h : (catProd lts₁ lts₂).MTr s μs s') :
    lts₂.MTr s.2 (μs.filterMap ProdLabel.snd) s'.2 := by
  induction h with
  | refl => exact .refl
  | @stepL s₁ μ s₂ μs s₃ htr _ ih =>
    cases μ with
    | left l₁ =>
      simp only [List.filterMap_cons, ProdLabel.snd_left]
      exact htr.2 ▸ ih
    | right l₂ =>
      simp only [List.filterMap_cons, ProdLabel.snd_right]
      exact .stepL htr.2 ih
    | both l₁ l₂ =>
      simp only [List.filterMap_cons, ProdLabel.snd_both]
      exact .stepL htr.2 ih

/-- Multistep executions of `LTS.catProd` consisting solely of `ProdLabel.left` steps correspond to
multistep executions of `lts₁` with the second state held fixed. -/
@[simp]
theorem catProd_mTr_map_left {s₁ s₁' : State₁} {s₂ s₂' : State₂} {μs₁ : List Label₁} :
    (catProd lts₁ lts₂).MTr (s₁, s₂) (μs₁.map ProdLabel.left) (s₁', s₂') ↔
      lts₁.MTr s₁ μs₁ s₁' ∧ s₂ = s₂' := by
  induction μs₁ generalizing s₁ s₂ with
  | nil => simp
  | cons l₁ μs₁ ih =>
    rw [List.map_cons, MTr.cons_iff, MTr.cons_iff]
    constructor
    · rintro ⟨⟨z₁, z₂⟩, ⟨htr, rfl⟩, hmtr⟩
      obtain ⟨hmtr₁, rfl⟩ := ih.mp hmtr
      exact ⟨⟨z₁, htr, hmtr₁⟩, rfl⟩
    · rintro ⟨⟨z₁, htr, hmtr₁⟩, rfl⟩
      exact ⟨(z₁, s₂), ⟨htr, rfl⟩, ih.mpr ⟨hmtr₁, rfl⟩⟩

/-- Multistep executions of `LTS.catProd` consisting solely of `ProdLabel.right` steps correspond to
multistep executions of `lts₂` with the first state held fixed. -/
@[simp]
theorem catProd_mTr_map_right {s₁ s₁' : State₁} {s₂ s₂' : State₂} {μs₂ : List Label₂} :
    (catProd lts₁ lts₂).MTr (s₁, s₂) (μs₂.map ProdLabel.right) (s₁', s₂') ↔
      s₁ = s₁' ∧ lts₂.MTr s₂ μs₂ s₂' := by
  induction μs₂ generalizing s₁ s₂ with
  | nil => simp
  | cons l₂ μs₂ ih =>
    rw [List.map_cons, MTr.cons_iff, MTr.cons_iff]
    constructor
    · rintro ⟨⟨z₁, z₂⟩, ⟨rfl, htr⟩, hmtr⟩
      obtain ⟨rfl, hmtr₂⟩ := ih.mp hmtr
      exact ⟨rfl, ⟨z₂, htr, hmtr₂⟩⟩
    · rintro ⟨rfl, ⟨z₂, htr, hmtr₂⟩⟩
      exact ⟨(s₁, z₂), ⟨rfl, htr⟩, ih.mpr ⟨rfl, hmtr₂⟩⟩

end CatProd

/-! ## Extensionality and multistep preservation for `LTS.Morphism` -/

namespace Morphism

variable {X Y : LTSCat.{u, v}}

/-- Two LTS morphisms are equal if their state maps and partial label maps are equal. -/
@[ext]
theorem ext {f g : Morphism X Y} (hState : f.stateMap = g.stateMap)
    (hLabel : f.labelMap = g.labelMap) : f = g := by
  cases f; cases g; cases hState; cases hLabel; rfl

/-- Every `LTS.Morphism` maps multistep executions to multistep executions along `List.filterMap` of
its partial label map. -/
theorem mTr (f : Morphism X Y) {s s' : X.State} {μs : List X.Label} (h : X.lts.MTr s μs s') :
    Y.lts.MTr (f.stateMap s) (μs.filterMap f.labelMap) (f.stateMap s') := by
  induction h with
  | refl => exact .refl
  | @stepL s₁ μ s₂ μs s₃ htr _ ih =>
    have hstep := f.labelMap_tr s₁ s₂ μ htr
    cases hμ : f.labelMap μ with
    | none =>
      rw [hμ] at hstep
      simp only [List.filterMap_cons, hμ]
      exact hstep ▸ ih
    | some ν =>
      rw [hμ] at hstep
      simp only [List.filterMap_cons, hμ]
      exact .stepL hstep ih

end Morphism

end LTS

/-! ## Binary products and terminal object in `LTSCat` -/

namespace LTSCat

/-- Pointwise extensionality for morphisms in `LTSCat`. -/
theorem ext_hom {X Y : LTSCat.{u, v}} {f g : X ⟶ Y}
    (hState : ∀ s, f.stateMap s = g.stateMap s)
    (hLabel : ∀ l, f.labelMap l = g.labelMap l) : f = g :=
  LTS.Morphism.ext (funext hState) (funext hLabel)

@[simp]
theorem id_stateMap (X : LTSCat.{u, v}) (s : X.State) :
    LTS.Morphism.stateMap (𝟙 X) s = s :=
  rfl

@[simp]
theorem id_labelMap (X : LTSCat.{u, v}) (l : X.Label) :
    LTS.Morphism.labelMap (𝟙 X) l = some l :=
  rfl

@[simp]
theorem comp_stateMap {X Y Z : LTSCat.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : X.State) :
    LTS.Morphism.stateMap (f ≫ g) s = g.stateMap (f.stateMap s) :=
  rfl

@[simp]
theorem comp_labelMap {X Y Z : LTSCat.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z) (l : X.Label) :
    LTS.Morphism.labelMap (f ≫ g) l = (f.labelMap l).bind g.labelMap :=
  rfl

/-! ### Binary products -/

/-- The binary product of two objects in `LTSCat`. -/
def prod (X Y : LTSCat.{u, v}) : LTSCat.{u, v} where
  State := X.State × Y.State
  Label := LTS.ProdLabel X.Label Y.Label
  lts := LTS.catProd X.lts Y.lts

/-- The state space of `X.prod Y` is `X.State × Y.State`. -/
theorem prod_state (X Y : LTSCat.{u, v}) : (X.prod Y).State = (X.State × Y.State) :=
  rfl

/-- The label alphabet of `X.prod Y` is `LTS.ProdLabel X.Label Y.Label`. -/
theorem prod_label (X Y : LTSCat.{u, v}) : (X.prod Y).Label = LTS.ProdLabel X.Label Y.Label :=
  rfl

/-- The underlying LTS of `X.prod Y` is `LTS.catProd X.lts Y.lts`. -/
@[simp]
theorem prod_lts (X Y : LTSCat.{u, v}) : (X.prod Y).lts = LTS.catProd X.lts Y.lts :=
  rfl

/-- First projection morphism `X.prod Y ⟶ X` in `LTSCat`. -/
def fst {X Y : LTSCat.{u, v}} : X.prod Y ⟶ X where
  stateMap := Prod.fst
  labelMap := LTS.ProdLabel.fst
  labelMap_tr _ _ _ h := h.1

/-- Second projection morphism `X.prod Y ⟶ Y` in `LTSCat`. -/
def snd {X Y : LTSCat.{u, v}} : X.prod Y ⟶ Y where
  stateMap := Prod.snd
  labelMap := LTS.ProdLabel.snd
  labelMap_tr _ _ _ h := h.2

/-- Pairing morphism `Z ⟶ X.prod Y` induced by `f : Z ⟶ X` and `g : Z ⟶ Y` in `LTSCat`. -/
def lift {Z X Y : LTSCat.{u, v}} (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ X.prod Y where
  stateMap s := (f.stateMap s, g.stateMap s)
  labelMap l := LTS.ProdLabel.mkOption (f.labelMap l) (g.labelMap l)
  labelMap_tr s s' l h :=
    LTS.withIdle_catProd_tr_mkOption.mpr ⟨f.labelMap_tr s s' l h, g.labelMap_tr s s' l h⟩

@[simp]
theorem fst_stateMap {X Y : LTSCat.{u, v}} :
    (fst (X := X) (Y := Y)).stateMap = Prod.fst :=
  rfl

@[simp]
theorem fst_labelMap {X Y : LTSCat.{u, v}} :
    (fst (X := X) (Y := Y)).labelMap = LTS.ProdLabel.fst :=
  rfl

@[simp]
theorem snd_stateMap {X Y : LTSCat.{u, v}} :
    (snd (X := X) (Y := Y)).stateMap = Prod.snd :=
  rfl

@[simp]
theorem snd_labelMap {X Y : LTSCat.{u, v}} :
    (snd (X := X) (Y := Y)).labelMap = LTS.ProdLabel.snd :=
  rfl

@[simp]
theorem lift_stateMap {Z X Y : LTSCat.{u, v}} (f : Z ⟶ X) (g : Z ⟶ Y) (s : Z.State) :
    (lift f g).stateMap s = (f.stateMap s, g.stateMap s) :=
  rfl

@[simp]
theorem lift_labelMap {Z X Y : LTSCat.{u, v}} (f : Z ⟶ X) (g : Z ⟶ Y) (l : Z.Label) :
    (lift f g).labelMap l = LTS.ProdLabel.mkOption (f.labelMap l) (g.labelMap l) :=
  rfl

/-- Composing `LTSCat.lift f g` with `LTSCat.fst` recovers `f`. -/
@[reassoc (attr := simp)]
theorem lift_fst {Z X Y : LTSCat.{u, v}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    lift f g ≫ fst = f :=
  ext_hom (fun _ => rfl) fun l => LTS.ProdLabel.bind_fst (f.labelMap l) (g.labelMap l)

/-- Composing `LTSCat.lift f g` with `LTSCat.snd` recovers `g`. -/
@[reassoc (attr := simp)]
theorem lift_snd {Z X Y : LTSCat.{u, v}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    lift f g ≫ snd = g :=
  ext_hom (fun _ => rfl) fun l => LTS.ProdLabel.bind_snd (f.labelMap l) (g.labelMap l)

/-- Universal uniqueness of `LTSCat.lift`: any morphism `h : Z ⟶ X.prod Y` whose projections
equal `f` and `g` must equal `lift f g`. -/
theorem hom_ext {Z X Y : LTSCat.{u, v}} {f : Z ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X.prod Y}
    (hf : h ≫ fst = f) (hg : h ≫ snd = g) : h = lift f g := by
  subst hf hg
  exact ext_hom (fun _ => rfl) fun l =>
    (LTS.ProdLabel.mkOption_bind_fst_bind_snd (h.labelMap l)).symm

/-- Two morphisms into `X.prod Y` are equal if their compositions with `fst` and `snd` agree. -/
theorem prod_hom_ext {Z X Y : LTSCat.{u, v}} {h₁ h₂ : Z ⟶ X.prod Y}
    (hfst : h₁ ≫ fst = h₂ ≫ fst) (hsnd : h₁ ≫ snd = h₂ ≫ snd) : h₁ = h₂ := by
  rw [hom_ext hfst hsnd, ← hom_ext rfl rfl]

/-- Pairing the two projections yields the identity morphism on `X.prod Y`. -/
@[simp]
theorem lift_fst_snd {X Y : LTSCat.{u, v}} :
    lift (fst (X := X) (Y := Y)) snd = 𝟙 (X.prod Y) :=
  (hom_ext (Category.id_comp _) (Category.id_comp _)).symm

/-- The binary fan exhibiting `X.prod Y` with projections `LTSCat.fst` and `LTSCat.snd`. -/
def prodBinaryFan (X Y : LTSCat.{u, v}) : Limits.BinaryFan X Y :=
  Limits.BinaryFan.mk fst snd

@[simp]
theorem prodBinaryFan_pt (X Y : LTSCat.{u, v}) : (prodBinaryFan X Y).pt = X.prod Y :=
  rfl

@[simp]
theorem prodBinaryFan_fst (X Y : LTSCat.{u, v}) : (prodBinaryFan X Y).fst = fst :=
  rfl

@[simp]
theorem prodBinaryFan_snd (X Y : LTSCat.{u, v}) : (prodBinaryFan X Y).snd = snd :=
  rfl

/-- The binary fan `LTSCat.prodBinaryFan X Y` is a limit cone in `LTSCat`. -/
def prodIsLimit (X Y : LTSCat.{u, v}) : Limits.IsLimit (prodBinaryFan X Y) :=
  Limits.BinaryFan.IsLimit.mk (prodBinaryFan X Y)
    (fun f g => lift f g)
    (fun f g => lift_fst f g)
    (fun f g => lift_snd f g)
    (fun _ _ _ hf hg => hom_ext hf hg)

/-- Every pair of objects in `LTSCat.{u, v}` has a categorical binary product. -/
instance hasBinaryProduct (X Y : LTSCat.{u, v}) : Limits.HasBinaryProduct X Y :=
  Limits.HasLimit.mk ⟨prodBinaryFan X Y, prodIsLimit X Y⟩

/-- The category `LTSCat.{u, v}` has all binary products. -/
instance hasBinaryProducts : Limits.HasBinaryProducts LTSCat.{u, v} :=
  Limits.hasBinaryProducts_of_hasLimit_pair LTSCat.{u, v}

/-- Canonical isomorphism between the abstract categorical product `X ⨯ Y` and `X.prod Y`. -/
noncomputable def prodIso (X Y : LTSCat.{u, v}) : Limits.prod X Y ≅ X.prod Y :=
  Limits.IsLimit.conePointUniqueUpToIso (Limits.limit.isLimit _) (prodIsLimit X Y)

/-! ### Terminal object and finite products -/

/-- The terminal object in `LTSCat.{u, v}`, having a single state, empty label alphabet, and no
transitions. -/
def terminal : LTSCat.{u, v} where
  State := PUnit
  Label := PEmpty
  lts := ⟨fun _ l _ => l.elim⟩

instance : Inhabited LTSCat.{u, v} :=
  ⟨terminal⟩

/-- The unique morphism from any `X : LTSCat.{u, v}` to `LTSCat.terminal`, mapping every state to
`PUnit.unit` and every label to `none` (idle). -/
def terminalFrom (X : LTSCat.{u, v}) : X ⟶ terminal.{u, v} where
  stateMap _ := PUnit.unit
  labelMap _ := none
  labelMap_tr _ _ _ _ := rfl

/-- There is a unique morphism from any `X : LTSCat.{u, v}` into `LTSCat.terminal`. -/
instance uniqueToTerminal (X : LTSCat.{u, v}) : Unique (X ⟶ terminal.{u, v}) where
  default := terminalFrom X
  uniq f :=
    ext_hom (fun s => by cases f.stateMap s; rfl) fun l => by
      cases h : f.labelMap l with
      | none => rfl
      | some e => exact e.elim

/-- `LTSCat.terminal` is a terminal object in `LTSCat.{u, v}`. -/
def terminalIsTerminal : Limits.IsTerminal terminal.{u, v} :=
  Limits.IsTerminal.ofUnique terminal.{u, v}

/-- The category `LTSCat.{u, v}` has a terminal object. -/
instance hasTerminal : Limits.HasTerminal LTSCat.{u, v} :=
  terminalIsTerminal.hasTerminal

/-- Canonical isomorphism between `⊤_ LTSCat.{u, v}` and `LTSCat.terminal`. -/
noncomputable def terminalIso : ⊤_ LTSCat.{u, v} ≅ terminal.{u, v} :=
  Limits.terminalIsoIsTerminal terminalIsTerminal

/-- The category `LTSCat.{u, v}` has all finite products. -/
instance hasFiniteProducts : Limits.HasFiniteProducts LTSCat.{u, v} :=
  hasFiniteProducts_of_has_binary_and_terminal

end LTSCat

end Cslib
