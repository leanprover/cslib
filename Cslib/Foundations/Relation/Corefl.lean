/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Foundations.Relation.Defs
public import Cslib.Foundations.Relation.Euclidean
public import Mathlib.Order.BooleanAlgebra.Basic

/-! # Relations: Definitions

## References

* [*Term Rewriting and All That*][Baader1998]
* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

open Relator

namespace Relation

variable {α : Type*} (r r₁ r₂ : α → α → Prop)

theorem corefl_union_trans (h₁ : Corefl r₁) (h₂ : IsTrans α r₂) : IsTrans α (r₁ ⊔ r₂) where
  trans a b c ab bc := by
    rcases ab with ab₁ | ab₂
    · rcases bc with bc₁ | _
      · left
        grind [h₁ ab₁, h₁ bc₁]
      · right
        grind [h₁ ab₁]
    · rcases bc with bc₁ | bc₂ <;> right
      · grind [h₁ bc₁]
      · exact _root_.trans ab₂ bc₂

theorem corefl_refl_eq (h : Corefl r) [Std.Refl r] : r = Eq := by
  ext
  exact ⟨h, of_eq⟩

theorem corefl_leftTotal_eq (h₁ : Corefl r) (h₂ : LeftTotal r) : r = Eq := by
  ext a b
  exact ⟨h₁, by grind [h₁ (h₂ a).choose_spec]⟩

theorem corefl_rightTotal_eq (h₁ : Corefl r) (h₂ : RightTotal r) : r = Eq := by
  ext a b
  exact ⟨h₁, by grind [h₁ (h₂ a).choose_spec]⟩

theorem rightQuasiRefl_leftUnique_corefl (h₁ : RightQuasiRefl r) (h₂ : LeftUnique r) : Corefl r :=
  fun ab => h₂ ab <| h₁ _ ⟨_, ab⟩

theorem leftQuasiRefl_rightUnique_corefl (h₁ : LeftQuasiRefl r) (h₂ : RightUnique r) : Corefl r :=
  fun ab => h₂ (h₁ _ ⟨_, ab⟩) ab

theorem refl_quasiRefl [Std.Refl r] : QuasiRefl r :=
  ⟨fun a _ => refl a, fun a _ => refl a⟩

-- TODO: change name of LeftEuclidean.reflOn_dom ?? needs better ergonomics too above ↑
-- TODO: some of the quasi refl stuff split out????

theorem leftEuclidean_rightUnique_corefl [LeftEuclidean r] (h : RightUnique r) : Corefl r :=
  leftQuasiRefl_rightUnique_corefl r LeftEuclidean.reflOn_dom h

theorem rightEuclidean_leftUnique_corefl [RightEuclidean r] (h : LeftUnique r) : Corefl r :=
  rightQuasiRefl_leftUnique_corefl r RightEuclidean.reflOn_cod h

theorem refl_leftUnique_corefl [Std.Refl r] (h : LeftUnique r) : Corefl r :=
  rightQuasiRefl_leftUnique_corefl r (refl_quasiRefl r |>.right) h

theorem refl_rightUnique_corefl [Std.Refl r] (h : RightUnique r) : Corefl r :=
  leftQuasiRefl_rightUnique_corefl r (refl_quasiRefl r |>.left) h

theorem symm_antisymm_corefl [Std.Symm r] [Std.Antisymm r] : Corefl r :=
  fun ab => Std.Antisymm.antisymm _ _ ab (symm ab)

end Relation
