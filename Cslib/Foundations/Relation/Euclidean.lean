/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Foundations.Relation.Domain
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.TFAE

/-! # Relations: Euclidean Relations

This module proves basic properties about left and right Euclidean relations, which are use
in modal logic.

TODO: develop an attribute to dualize theorems to the converse of a relation

## References

* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

open Relator

namespace Relation

variable {α : Type*} {r : α → α → Prop}

@[scoped grind →]
lemma refl_serial (r : α → α → Prop) (h : Std.Refl r) : Serial r where
  serial a := ⟨a, h.refl a⟩

instance [instRefl : Std.Refl r] : Serial r := refl_serial r instRefl

namespace RightEuclidean

variable [RightEuclidean r]

/-- A `RightEuclidean` relation is reflexive on its range -/
theorem refl_cod (ab : r a b) : r b b := rightEuclidean ab ab

theorem refl_cod' : b ∈ cod r → r b b := fun ⟨_, ab⟩ ↦ refl_cod ab

/-- The converse of a `RightEuclidean` relation is `LeftEuclidean` -/
theorem leftEuclidean_swap : LeftEuclidean (fun a b => r b a) where
  leftEuclidean ca cb := rightEuclidean cb ca

instance [Std.Refl r] : Std.Symm r where
  symm a _ ab := rightEuclidean ab (refl a)

theorem trichotomous_trans [Std.Trichotomous r] : IsTrans α r where
  trans a b c ab bc := by
    have := Std.Trichotomous.trichotomous (r := r) a c
    have cc := refl_cod bc
    have (ca : r c a) := rightEuclidean ca cc
    grind

theorem antisymm_rightUnique [Std.Antisymm r] : Relator.RightUnique r := by
  intros a b c ab ac
  exact antisymm (rightEuclidean ab ac) (rightEuclidean ac ab)

theorem rightUnique_antisymm (h : Relator.RightUnique r) : Std.Antisymm r where
  antisymm _ _ ab ba := h ba (refl_cod ab)

theorem rightUnique_trans (h : Relator.RightUnique r) : IsTrans α r where
  trans a b c ab bc := by
    have eq : c = b := h bc (refl_cod ab)
    simpa [eq]

theorem rightTotal_equiv (h : Relator.RightTotal r) : IsEquiv α r := by
  have : Std.Refl r := ⟨fun a => refl_cod (h a).choose_spec⟩
  exact {toIsTrans := ⟨fun _ _ _ ab bc => rightEuclidean (symm ab) bc⟩}

omit [RightEuclidean r] in
theorem leftTotal_rightUnique_trans (h₁ : LeftTotal r) (h₂ : RightUnique r) [IsTrans α r] :
    RightEuclidean r where
  rightEuclidean {a b c} ab ac := by
    obtain ⟨d, dc⟩ := h₁ c
    have : b = c := h₂ ab ac
    have : d = c := h₂ (_root_.trans ac dc) ac
    grind

private theorem three_contra [Std.Trichotomous r] [Std.Antisymm r] :
    ¬ ∃ (a b c : α), a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  rintro ⟨a, b, c, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a b
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a c
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ b c
  have := antisymm_rightUnique (r := r)
  have := @refl_cod (r := r)
  grind [Relator.RightUnique]

theorem trichotomous_antisymm_finite [Std.Trichotomous r] [Std.Antisymm r] : Finite α := by
  classical
  by_contra! h
  apply three_contra (r := r)
  have ⟨_, hcard⟩ := Infinite.exists_subset_card_eq α 3
  have ⟨a, b, c, _, _, _, _⟩ := Finset.card_eq_three.mp hcard
  use a, b, c

theorem trichotomous_antisymm_card [Std.Trichotomous r] [Std.Antisymm r] [Fintype α] :
    Fintype.card α ≤ 2 := by
  by_contra! h
  apply three_contra (r := r)
  have ⟨a, b, c, _⟩ := Fintype.two_lt_card_iff.mp h
  use a, b, c

theorem cod_subset_dom : cod r ⊆ dom r := fun b ⟨_, ab⟩ ↦ ⟨b, refl_cod ab⟩

instance : RightEuclidean (α := cod r) r where
  rightEuclidean := rightEuclidean

instance : RightEuclidean (α := dom r) r where
  rightEuclidean := rightEuclidean

theorem rightTotal_cod : Relator.RightTotal (α := cod r) (β := cod r) r :=
  fun ⟨_, _, h⟩ => ⟨_, refl_cod h⟩

theorem equiv_cod : IsEquiv (cod r) r := rightTotal_equiv rightTotal_cod

end RightEuclidean

namespace LeftEuclidean

variable [LeftEuclidean r]

/-- A `LeftEuclidean` relation is reflexive on its domain -/
theorem refl_dom (ab : r a b) : r a a := leftEuclidean ab ab

theorem refl_dom' : a ∈ dom r → r a a := fun ⟨_, ab⟩ ↦ refl_dom ab

/-- The converse of a `LeftEuclidean` relation is `RightEuclidean` -/
theorem rightEuclidean_swap : RightEuclidean (fun a b => r b a) where
  rightEuclidean ab ac := leftEuclidean ac ab

instance [Std.Refl r] : Std.Symm r where
  symm _ b ab := leftEuclidean (refl b) ab

theorem trichotomous_trans [Std.Trichotomous r] : IsTrans α r where
  trans a b c ab bc := by
    have := Std.Trichotomous.trichotomous (r := r) a c
    have aa := refl_dom ab
    have (ca : r c a) := leftEuclidean aa ca
    grind

theorem antisymm_leftUnique [Std.Antisymm r] : Relator.LeftUnique r := by
  intros a b c ac bc
  exact antisymm (leftEuclidean ac bc) (leftEuclidean bc ac)

theorem leftUnique_antisymm (h : Relator.LeftUnique r) : Std.Antisymm r where
  antisymm _ _ ab ba := h ab (refl_dom ba)

theorem leftUnique_trans (h : Relator.LeftUnique r) : IsTrans α r where
  trans a b c ab bc := by
    have eq : a = b := h ab (refl_dom bc)
    simpa [eq]

theorem leftTotal_equiv (h : Relator.LeftTotal r) : IsEquiv α r := by
  have : Std.Refl r := ⟨fun a => refl_dom (h a).choose_spec⟩
  exact {toIsTrans := ⟨fun _ _ _ ab bc => leftEuclidean ab (symm bc)⟩}

omit [LeftEuclidean r] in
theorem rightTotal_leftUnique_trans (h₁ : RightTotal r) (h₂ : LeftUnique r) [IsTrans α r] :
    LeftEuclidean r where
  leftEuclidean {a b c} ac bc := by
    obtain ⟨d, da⟩ := h₁ a
    have : a = b := h₂ ac bc
    have : a = d := h₂ ac (_root_.trans da ac)
    grind

private theorem three_contra [Std.Trichotomous r] [Std.Antisymm r] :
    ¬ ∃ (a b c : α), a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  rintro ⟨a, b, c, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a b
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a c
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ b c
  have := antisymm_leftUnique (r := r)
  have := @refl_dom (r := r)
  grind [Relator.LeftUnique]

theorem trichotomous_antisymm_finite [Std.Trichotomous r] [Std.Antisymm r] : Finite α := by
  classical
  by_contra! h
  apply three_contra (r := r)
  have ⟨_, hcard⟩ := Infinite.exists_subset_card_eq α 3
  have ⟨a, b, c, _, _, _, _⟩ := Finset.card_eq_three.mp hcard
  use a, b, c

theorem trichotomous_antisymm_card [Std.Trichotomous r] [Std.Antisymm r] [Fintype α] :
    Fintype.card α ≤ 2 := by
  by_contra! h
  apply three_contra (r := r)
  have ⟨a, b, c, _⟩ := Fintype.two_lt_card_iff.mp h
  use a, b, c

theorem dom_subset_cod : dom r ⊆ cod r := fun a ⟨_, ab⟩ ↦ ⟨a, refl_dom ab⟩

instance : LeftEuclidean (α := cod r) r where
  leftEuclidean := leftEuclidean

instance : LeftEuclidean (α := dom r) r where
  leftEuclidean := leftEuclidean

theorem leftTotal_dom : Relator.LeftTotal (α := dom r) (β := dom r) r :=
  fun ⟨_, _, h⟩ => ⟨_, refl_dom h⟩

theorem equiv_dom : IsEquiv (dom r) r := leftTotal_equiv leftTotal_dom

end LeftEuclidean

section euclidean_symm

variable [Std.Symm r]

open RightEuclidean LeftEuclidean in
private theorem symm_equivalents : [RightEuclidean r, LeftEuclidean r, IsTrans α r].TFAE := by
  tfae_have 1 → 2 := fun _ => ⟨fun ac bc => rightEuclidean (symm ac) (symm bc)⟩
  tfae_have 2 → 3 := fun _ => ⟨fun _ _ _ ab bc => leftEuclidean ab (symm bc)⟩
  tfae_have 3 → 1 := fun _ => ⟨fun ab ac => _root_.trans (symm ab) ac⟩
  tfae_finish

/-- For a symmetric relation, `LeftEuclidean` and `RightEuclidean` are equivalent. -/
theorem symm_leftEuclidean_iff_rightEuclidean : LeftEuclidean r ↔ RightEuclidean r :=
  List.TFAE.out symm_equivalents 1 0

/-- For a symmetric relation, `LeftEuclidean` and transitivity are equivalent. -/
theorem symm_leftEuclidean_iff_trans : LeftEuclidean r ↔  IsTrans α r :=
  List.TFAE.out symm_equivalents 1 2

/-- For a symmetric relation, `RightEuclidean` and transitivity are equivalent. -/
theorem symm_rightEuclidean_iff_trans : RightEuclidean r ↔ IsTrans α r :=
  List.TFAE.out symm_equivalents 0 2

end euclidean_symm

theorem leftEuclidean_rightEuclidean_dom_cod_eq [LeftEuclidean r] [RightEuclidean r] :
    dom r = cod r := by
  have : dom r ⊆ cod r := LeftEuclidean.dom_subset_cod
  have : cod r ⊆ dom r := RightEuclidean.cod_subset_dom
  grind

theorem dom_cod_leftEuclidean (eq : dom r = cod r) [equiv_dom : IsEquiv (dom r) r] :
    LeftEuclidean r where
  leftEuclidean {a b c} ac bc := by
    have cb : r c b := equiv_dom.symm ⟨_, _, bc⟩ ⟨c, by grind⟩ bc
    exact equiv_dom.trans ⟨_, _, ac⟩ ⟨_, _, cb⟩ ⟨_, by grind⟩ ac cb

lemma dom_cod_rightEuclidean (eq : dom r = cod r) [equiv_dom : IsEquiv (dom r) r] :
    RightEuclidean r where
  rightEuclidean {a b c} ab ac := by
    have ba : r b a := equiv_dom.symm ⟨a, _, ab⟩ ⟨b, by grind⟩ ab
    exact equiv_dom.trans ⟨_, _, ba⟩ ⟨_, _, ac⟩ ⟨c, by grind⟩ ba ac

/-- A relation is both left and right Euclidean if and only if the relation is an equivalence on
  coinciding domain and codomain. -/
theorem leftEuclidean_rightEuclidean_iff_dom_cod :
    LeftEuclidean r ∧ RightEuclidean r ↔ dom r = cod r ∧ IsEquiv (dom r) r where
  mp := fun ⟨_, _⟩ ↦ ⟨leftEuclidean_rightEuclidean_dom_cod_eq, LeftEuclidean.equiv_dom⟩
  mpr := fun ⟨eq, _⟩ ↦ ⟨dom_cod_leftEuclidean eq, dom_cod_rightEuclidean eq⟩

end Relation
