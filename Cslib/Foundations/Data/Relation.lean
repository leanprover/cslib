/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

import Cslib.Init
import Mathlib.Logic.Relation
import Mathlib.Data.List.TFAE

/-! # Relations -/

namespace Relation

variable {α : Type*} {r : α → α → Prop}

attribute [scoped grind] ReflGen TransGen ReflTransGen EqvGen

theorem ReflGen.to_eqvGen (h : ReflGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem TransGen.to_eqvGen (h : TransGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem ReflTransGen.to_eqvGen (h : ReflTransGen r a b) : EqvGen r a b := by
  induction h <;> grind

attribute [scoped grind →] ReflGen.to_eqvGen TransGen.to_eqvGen ReflTransGen.to_eqvGen

/-- The relation `r` 'up to' the relation `s`. -/
def UpTo (r s : α → α → Prop) : α → α → Prop := Comp s (Comp r s)

/-- A relation has the diamond property when all reductions with a common origin are joinable -/
abbrev Diamond (r : α → α → Prop) := ∀ {A B C : α}, r A B → r A C → Join r B C

/-- A relation is confluent when its reflexive transitive closure has the diamond property. -/
abbrev Confluent (r : α → α → Prop) := Diamond (ReflTransGen r)

/-- A relation is semi-confluent when single and multiple steps with common origin
  are multi-joinable. -/
abbrev SemiConfluent (r : α → α → Prop) :=
  ∀ {x y₁ y₂}, ReflTransGen r x y₂ → r x y₁ → Join (ReflTransGen r) y₁ y₂

/-- A relation has the Church Rosser property when equivalence implies multi-joinability. -/
abbrev ChurchRosser (r : α → α → Prop) := ∀ {x y}, EqvGen r x y → Join (ReflTransGen r) x y

/-- Extending a multistep reduction by a single step preserves multi-joinability. -/
lemma Diamond.extend (h : Diamond r) :
    ReflTransGen r A B → r A C → Join (ReflTransGen r) B C := by
  intros AB AC
  induction AB using ReflTransGen.head_induction_on generalizing C
  case refl => exists C, .single AC
  case head A'_C' _ ih =>
    obtain ⟨D, CD, C'_D⟩ := h AC A'_C'
    obtain ⟨D', B_D', D_D'⟩ := ih C'_D
    exact ⟨D', B_D', .head CD D_D'⟩

/-- The diamond property implies confluence. -/
theorem Diamond.toConfluent (h : Diamond r) : Confluent r := by
  intros A B C AB BC
  induction AB using ReflTransGen.head_induction_on generalizing C
  case refl => exists C
  case head _ _ A'_C' _ ih =>
    obtain ⟨D, CD, C'_D⟩ := h.extend BC A'_C'
    obtain ⟨D', B_D', D_D'⟩ := ih C'_D
    exact ⟨D', B_D', .trans CD D_D'⟩

theorem Confluent.toChurchRosser (h : Confluent r) : ChurchRosser r := by
  intro x y h_eqv
  induction h_eqv with
  | rel _ b => exists b; grind [ReflTransGen.single]
  | refl a => exists a
  | symm a b _ ih => exact symmetric_join ih
  | trans _ _ _ _ _ ih1 ih2 =>
      obtain ⟨u, _, hbu⟩ := ih1
      obtain ⟨v, hbv, _⟩ := ih2
      obtain ⟨w, _, _⟩ := h hbu hbv
      exists w
      grind [ReflTransGen.trans]

theorem SemiConfluent.toConfluent (h : SemiConfluent r) : Confluent r := by
  intro x y1 y2 h_xy1 h_xy2
  induction h_xy1 with
  | refl => use y2
  | tail h_xz h_zy1 ih =>
      obtain ⟨u, h_zu, _⟩ := ih
      obtain ⟨v, _, _⟩ := h h_zu h_zy1
      exists v
      grind [ReflTransGen.trans]

attribute [scoped grind →] Confluent.toChurchRosser SemiConfluent.toConfluent

private theorem confluent_equivalents : [ChurchRosser r, SemiConfluent r, Confluent r].TFAE := by
  grind [List.tfae_cons_cons, List.tfae_singleton]

theorem SemiConfluent_iff_ChurchRosser : SemiConfluent r ↔ ChurchRosser r :=
  List.TFAE.out confluent_equivalents 1 0

theorem Confluent_iff_ChurchRosser : Confluent r ↔ ChurchRosser r :=
  List.TFAE.out confluent_equivalents 2 0

theorem Confluent_iff_SemiConfluent : Confluent r ↔ SemiConfluent r :=
  List.TFAE.out confluent_equivalents 2 1

/-- An element is reducible with respect to a relation if there is a value it is related to. -/
abbrev Reducible (r : α → α → Prop) (x : α) : Prop := ∃ y, r x y

/-- An element is normal if it is not reducible. -/
abbrev Normal (r : α → α → Prop) (x : α) : Prop := ¬ Reducible r x

/-- A multi-step from a normal form must be reflexive. -/
@[grind =>]
theorem Normal.reflTransGen_eq (h : Normal r x) (xy : ReflTransGen r x y) : x = y := by
  induction xy <;> grind

/-- For a Church-Rosser relation, elements in an equivalence class must be multi-step related. -/
theorem ChurchRosser.normal_eqvGen_reflTransGen (cr : ChurchRosser r) (norm : Normal r x)
    (xy : EqvGen r y x) : ReflTransGen r y x := by
  have ⟨_, _, _⟩ := cr xy
  grind

/-- For a Church-Rosser relation there is one normal form in each equivalence class. -/
theorem ChurchRosser.normal_eq (cr : ChurchRosser r) (nx : Normal r x) (ny : Normal r y)
    (xy : EqvGen r x y) : x = y := by
  have ⟨_, _, _⟩ := cr xy
  grind

/-- A pair of subrelations lifts to transitivity on the relation. -/
def trans_of_subrelation (s s' r : α → α → Prop) (hr : Transitive r)
    (h : Subrelation s r) (h' : Subrelation s' r) : Trans s s' r where
  trans hab hbc := hr (h hab) (h' hbc)

/-- A subrelation lifts to transitivity on the left of the relation. -/
def trans_of_subrelation_left (s r : α → α → Prop) (hr : Transitive r)
    (h : Subrelation s r) : Trans s r r where
  trans hab hbc := hr (h hab) hbc

/-- A subrelation lifts to transitivity on the right of the relation. -/
def trans_of_subrelation_right (s r : α → α → Prop) (hr : Transitive r)
    (h : Subrelation s r) : Trans r s r where
  trans hab hbc := hr hab (h hbc)

/-- The diamond property implies that multi-step joinability is an equivalence. -/
theorem Diamond.equivalence_join_reflTransGen (h : Diamond r) :
    Equivalence (Join (ReflTransGen r)) := by
  apply Relation.equivalence_join reflexive_reflTransGen transitive_reflTransGen
  intro a b c hab hac
  exact h.toConfluent hab hac

end Relation
