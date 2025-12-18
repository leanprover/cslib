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

/-- Confluence implies that multi-step joinability is an equivalence. -/
theorem Confluent.equivalence_join_reflTransGen (h : Confluent r) :
    Equivalence (Join (ReflTransGen r)) := by
  grind [equivalence_join, reflexive_reflTransGen, transitive_reflTransGen]

abbrev Terminating (r : α → α → Prop) := WellFounded (fun a b => TransGen r b a)

/-- A relation is locally confluent when all reductions with a common origin are multi-joinable -/
abbrev LocallyConfluent (r : α → α → Prop) :=
  ∀ {A B C : α}, r A B → r A C → Join (ReflTransGen r) B C

theorem Confluent.toLocallyConfluent (h : Confluent r) : LocallyConfluent r := by
  intro _ _ _ AB AC
  exact h (.single AB) (.single AC)

/-- Newman's lemma: a terminating, locally confluent relation is confluent. -/
theorem LocallyConfluent.Terminating_toConfluent (h : LocallyConfluent r) (wf : Terminating r) :
    Confluent r := by
  intro X
  induction X using wf.induction with
  | h X ih =>
    intro Y Z XY XZ
    cases XY.cases_head with
    | inl => exists Z; grind
    | inr h =>
      obtain ⟨Y₁, X_Y₁, Y₁_Y⟩ := h
      cases XZ.cases_head with
      | inl => exists Y; grind
      | inr h =>
        obtain ⟨Z₁, X_Z₁, Z₁_Z⟩ := h
        have ⟨U, Z₁_U, Y₁_U⟩ := h X_Z₁ X_Y₁
        have ⟨V, UV, YV⟩ : Join (ReflTransGen r) U Y := by grind
        have ⟨W, VW, ZW⟩ : Join (ReflTransGen r) V Z := by grind [ReflTransGen.trans]
        exact ⟨W, .trans YV VW, ZW⟩

abbrev StronglyConfluent (r : α → α → Prop) :=
  ∀ {X Y₁ Y₂}, r X Y₁ → r X Y₂ → ∃ Z, ReflGen r Y₁ Z ∧ ReflTransGen r Y₂ Z

/-- Generalization of `Confluent` to two relations. -/
def Commute (r₁ r₂ : α → α → Prop) := ∀ {X Y₁ Y₂},
  ReflTransGen r₁ X Y₁ → ReflTransGen r₂ X Y₂ → ∃ Z, ReflTransGen r₂ Y₁ Z ∧ ReflTransGen r₁ Y₂ Z

theorem Commute.toConfluent : Commute r r = Confluent r := rfl

/-- Generalization of `StronglyConfluent` to two relations. -/
def StronglyCommute (r₁ r₂ : α → α → Prop) :=
  ∀ {X Y₁ Y₂}, r₁ X Y₁ → r₂ X Y₂ → ∃ Z, ReflGen r₂ Y₁ Z ∧ ReflTransGen r₁ Y₂ Z

theorem StronglyCommute.toStronglyConfluent : StronglyCommute r r = StronglyConfluent r := rfl

/-- Generalization of `Diamond` to two relations. -/
def DiamondCommute (r₁ r₂ : α → α → Prop) :=
  ∀ {X Y₁ Y₂}, r₁ X Y₁ → r₂ X Y₂ → ∃ Z, r₂ Y₁ Z ∧ r₁ Y₂ Z

theorem DiamondCommute.toDiamond : DiamondCommute r r = Diamond r := by rfl

theorem StronglyCommute.extend (h : StronglyCommute r₁ r₂) (xy : ReflTransGen r₁ x y)
    (xz : r₂ x z) : ∃ w, ReflGen r₂ y w ∧ ReflTransGen r₁ z w := by
  induction xy with
  | refl => exact ⟨z, .single xz, .refl⟩
  | @tail b c _ bc ih =>
    obtain ⟨w, bw, zw⟩ := ih
    cases bw with
    | refl => exact ⟨c, .refl, zw.trans (.single bc)⟩
    | single bw => cases h bc bw; grind [ReflTransGen.trans]

theorem StronglyCommute.toCommute (h : StronglyCommute r₁ r₂) : Commute r₁ r₂ := by
  intro X Y₁ Y₂ X_Y₁ X_Y₂
  induction X_Y₂ with
  | refl => exists Y₁
  | @tail A B XA AB ih =>
    obtain ⟨Z, Y₁_Z, Y₂_Z⟩ := ih
    obtain ⟨W, ZW, BW⟩ := h.extend Y₂_Z AB
    exact ⟨W, Y₁_Z.trans ZW.to_reflTransGen, BW⟩

theorem StronglyConfluent.toConfluent (h : StronglyConfluent r) : Confluent r :=
  StronglyCommute.toCommute h

abbrev Union (r₁ r₂ : α → α → Prop) (a₁ a₂) := r₁ a₁ a₂ ∨ r₂ a₁ a₂

proof_wanted union_Confluent (c₁ : Confluent r₁) (c₂ : Confluent r₂) (comm : Commute r₁ r₂) :
    Confluent (Union r₁ r₂)

/-- If a relation is squeezed by a relation and its multi-step closure, they are multi-step equal -/
theorem reflTransGen_mono_closed (h₁ : Subrelation r₁ r₂) (h₂ : Subrelation r₂ (ReflTransGen r₁)) :
    ReflTransGen r₁ = ReflTransGen r₂ := by
  ext
  exact ⟨ReflTransGen.mono @h₁, reflTransGen_closed @h₂⟩

end Relation
