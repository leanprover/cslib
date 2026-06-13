/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Foundations.Relation.Defs

/-! # Relations: Properties on sestrictions

## References

* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

namespace Relation

variable (r : α → α → Prop) (s : Set α)

@[simp]
theorem refl_iff_reflOn : Std.Refl (α := s) r ↔ ReflOn r s := by
  constructor
  · exact fun ⟨h⟩ a ha => h ⟨a, ha⟩
  · exact fun h ↦ ⟨fun ⟨a, ha⟩ ↦ h a ha⟩

@[simp]
theorem symm_iff_symmOn : Std.Symm (α := s) r ↔ SymmOn r s := by
  constructor
  · intro ⟨h⟩ a ha b hb ab
    exact h ⟨a, ha⟩ ⟨b, hb⟩ ab
  · intro h
    constructor
    intro ⟨a, ha⟩ ⟨b, hb⟩ ab
    exact h a ha b hb ab

@[simp]
theorem rightEuclidean_iff_rightEuclideanOn (s : Set α) :
    RightEuclidean (α := s) r ↔ RightEuclideanOn r s := by
  constructor
  · intro ⟨h⟩ a ha b hb c hc ab ac
    exact @h ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ab ac
  · intro h
    constructor
    intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ab ac
    exact h a ha b hb c hc ab ac

instance [RightEuclidean r] (s : Set α) : RightEuclidean (α := s) r :=
  ⟨RightEuclidean.rightEuclidean⟩

end Relation
