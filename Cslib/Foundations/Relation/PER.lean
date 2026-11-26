/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Relation.Basic
public import Cslib.Foundations.Relation.Restriction
public import Mathlib.Order.SetNotation

/-!-/

@[expose] public section

namespace Relation

variable {α : Type*} {r : α → α → Prop} {x x' y y' : α}

lemma mem_dom_PER_iff [Std.Symm r] [IsTrans α r] : x ∈ dom r ↔ r x x :=
  ⟨fun ⟨_, h⟩ ↦ rfl_of_rel h, fun h ↦ ⟨x, h⟩⟩

variable (r) in
lemma eqvGen_per [Std.Symm r] [IsTrans α r] : EqvGen r = ReflGen r := by
  have : IsEquiv α (ReflGen r) := {}
  exact le_antisymm (eqvGen_le ReflGen.le_reflGen) (reflGen_le_eqvGen r)

lemma eqvGen_per_iff_of_mem_dom [Std.Symm r] [IsTrans α r] (hx : x ∈ dom r) :
    EqvGen r x y ↔ r x y := by
  simp +contextual [eqvGen_per r, reflGen_iff, mem_dom_PER_iff.mp hx]

-- def partialSetoid (r : α → α → Prop) [Std.Symm r] [IsTrans α r] : Setoid (dom r) where
--   r a b := r a b
--   iseqv := by
--     refine { refl := ?_, symm := symm, trans := _root_.trans }
--     intro ⟨x, y, h⟩
--     exact _root_.trans h (symm h)

def PQuot (r : α → α → Prop) : Type _ := Quot (r : dom r → dom r → Prop)

namespace PQuot

variable {s : Set α}

protected def mk (h : x ∈ dom r) : PQuot r := Quot.mk _ ⟨x, h⟩

protected theorem eq [Std.Symm r] [IsTrans α r] (hx : x ∈ dom r) (hy : y ∈ dom r) :
    PQuot.mk hx = PQuot.mk hy ↔ r x y := by
  convert! Quot.eq
  simp [(Equivalence.of_isEquiv _).eqvGen_eq]

protected def lift {β : Sort*} (f : α → β) (h : ∀ x y : α, r x y → f x = f y) :
  PQuot r → β := Quot.lift (f ·) <| fun x y (hxy : r x y) ↦  h ↑x ↑y hxy

@[simp]
protected lemma lift_mk {β : Sort*} (f : α → β) (hf : ∀ x y : α, r x y → f x = f y)
    (hx : x ∈ dom r) : PQuot.lift f hf (.mk hx) = f x := Quot.lift_mk f hf x

protected theorem inductionOn [Std.Symm r] [IsTrans α r] {motive : PQuot r → Prop} (q : PQuot r)
    (h : ∀ x : α, (h : r x x) → motive (.mk <| of_dom h)) : motive q :=
  Quot.inductionOn q fun ⟨x, _, hx⟩ ↦ h x (rfl_of_rel hx)

end PQuot

variable [Std.Symm r] [IsTrans α r]

variable (r) in
def pEqvClass : PQuot r → Set α := PQuot.lift (fun x ↦ {y | r x y}) <| by
  intro x y (h : r _ _)
  ext z
  exact ⟨_root_.trans (symm h), _root_.trans h⟩

@[simp] theorem mem_pEqvClass_mk (hx : x ∈ dom r) : y ∈ pEqvClass r (.mk hx) ↔ r x y := by
  simp [pEqvClass]

lemma mem_pEqvClass_self (hx : x ∈ dom r) : x ∈ pEqvClass r (.mk hx) :=
    (mem_pEqvClass_mk hx).mpr (mem_dom_PER_iff.mp hx)

theorem pairwiseDisjoint_pEqvClass : Set.univ.PairwiseDisjoint (pEqvClass r) := by
  intro p _; apply p.inductionOn fun x hx ↦ ?_
  intro q _; apply q.inductionOn fun y hy ↦ ?_
  simp_rw [ne_eq, PQuot.eq, Set.disjoint_iff, Set.subset_def, Set.mem_inter_iff, mem_pEqvClass_mk]
  intro hxy z ⟨hxz, hyz⟩
  exact hxy <| _root_.trans hxz (symm hyz)

theorem iUnion_pEqvClass : ⋃ p, pEqvClass r p = dom r := by
  ext x
  constructor
  · rintro ⟨_, ⟨⟨y, hy⟩, rfl⟩, (h : x ∈ pEqvClass r (.mk hy))⟩
    use y
    simpa [comm] using h
  · intro ⟨y, hy⟩
    refine ⟨_, ⟨PQuot.mk ⟨x, symm hy⟩, rfl⟩, ?_⟩
    exact mem_pEqvClass_mk ⟨x, symm hy⟩ |>.mpr (symm hy)

end Relation
