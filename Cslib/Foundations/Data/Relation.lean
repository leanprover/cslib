/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import Mathlib.Order.Comparable
public import Mathlib.Order.WellFounded
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Data.Fintype.EquivFin

/-! # Relations

## References

* [*Term Rewriting and All That*][Baader1998]
* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

open Relator

variable {α : Type*} {r r₁ r₂ : α → α → Prop}

theorem WellFounded.ofTransGen (trans_wf : WellFounded (Relation.TransGen r)) : WellFounded r := by
  grind [WellFounded.wellFounded_iff_has_min, Relation.TransGen]

@[simp, grind =]
theorem WellFounded.iff_transGen : WellFounded (Relation.TransGen r) ↔ WellFounded r :=
  ⟨ofTransGen, transGen⟩

namespace Relation

/-- The empty (heterogeneous) relation, which always returns `False`. -/
@[nolint unusedArguments]
def emptyHRelation {α : Sort u} {β : Sort v} (_ : α) (_ : β) := False

@[simp, grind =]
theorem emptyHRelation_emptyRelation : (emptyHRelation : α → α → Prop) = emptyRelation := rfl

@[simp, grind =]
theorem emptyHrelation_apply (a : α) (b : β) : emptyHRelation a b ↔ False := .rfl

section dom_cod

variable {β : Type*} {r : α → β → Prop}

/-- Domain of a relation. -/
def dom (r : α → β → Prop) : Set α := {a | ∃ b, r a b}

/-- Codomain of a relation, aka range. -/
def cod (r : α → β → Prop) : Set β := {b | ∃ a, r a b}

@[simp, grind =] lemma mem_dom : a ∈ dom r ↔ ∃ b, r a b := .rfl
@[simp, grind =] lemma mem_cod : b ∈ cod r ↔ ∃ a, r a b := .rfl

@[gcongr] lemma dom_mono (h : r₁ ≤ r₂) : dom r₁ ⊆ dom r₂ := fun a ⟨b, hab⟩ => ⟨b, h a b hab⟩
@[gcongr] lemma cod_mono (h : r₁ ≤ r₂) : cod r₁ ⊆ cod r₂ := fun b ⟨a, hab⟩ => ⟨a, h a b hab⟩

@[simp, grind =]
lemma dom_empty : dom (emptyHRelation : α → β → Prop) = ∅ := by grind

@[simp, grind =]
lemma cod_empty : cod (emptyHRelation : α → β → Prop) = ∅ := by grind

@[simp, grind =]
lemma dom_eq_empty_iff : dom r = ∅ ↔ r = emptyHRelation where
  mp h := by
    ext a b
    simp
    grind => have : a ∈ dom r; finish
  mpr := by grind

@[simp, grind =]
lemma cod_eq_empty_iff : cod r = ∅ ↔ r = emptyHRelation where
  mp h := by
    ext a b
    simp
    grind => have : b ∈ cod r; finish
  mpr h := by grind

@[simp]
lemma cod_inv : cod (fun a b => r b a) = dom r := rfl

@[simp]
lemma dom_inv : dom (fun a b => r b a) = cod r := rfl

end dom_cod

instance : CoeDep (α → α → Prop) r (dom r → dom r → Prop) where
  coe a b := r a b

instance : CoeDep (α → α → Prop) r (cod r → cod r → Prop) where
  coe a b := r a b

theorem _root_.Std.Trichotomous.subsingleton_cod [Std.Trichotomous r] :
    Subsingleton ((cod r)ᶜ : Set α) := by
  constructor
  rintro ⟨b₁, _⟩ ⟨b₂, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ b₁ b₂
  grind

theorem _root_.Std.Trichotomous.subsingleton_dom [Std.Trichotomous r] :
    Subsingleton ((dom r)ᶜ : Set α) := by
  constructor
  rintro ⟨a₁, _⟩ ⟨a₂, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a₁ a₂
  grind

attribute [scoped grind] ReflGen TransGen ReflTransGen EqvGen CompRel

theorem ReflGen.to_eqvGen (h : ReflGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem TransGen.to_eqvGen (h : TransGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem ReflTransGen.to_eqvGen (h : ReflTransGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem SymmGen.to_eqvGen (h : SymmGen r a b) : EqvGen r a b := by
  induction h <;> grind

attribute [scoped grind →] ReflGen.to_eqvGen TransGen.to_eqvGen ReflTransGen.to_eqvGen
  SymmGen.to_eqvGen

/-- The join of the reflexive transitive closure. This is not named in Mathlib, but see
  `#loogle Relation.Join (Relation.ReflTransGen ?r)` -/
abbrev MJoin (r : α → α → Prop) := Join (ReflTransGen r)

theorem MJoin.refl (a : α) : MJoin r a a := by
  use a

theorem MJoin.symm : Symmetric (MJoin r) := Relation.symmetric_join

theorem MJoin.single (h : ReflTransGen r a b) : MJoin r a b := by
  use b

/-- The relation `r` 'up to' the relation `s`. -/
def UpTo (r s : α → α → Prop) : α → α → Prop := Comp s (Comp r s)

/-- A relation `r` is (right) Euclidean if `r a b` and `r a c` guarantee `r b c`. -/
class RightEuclidean (r : α → α → Prop) where
  rightEuclidean : r a b → r a c → r b c

/-- A relation `r` is (left) Euclidean if `r a c` and `r b c` guarantee `r a b`. -/
class LeftEuclidean (r : α → α → Prop) where
  leftEuclidean {a b c} : r a c → r b c → r a b

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

/-- A relation has the diamond property when all reductions with a common origin are joinable -/
abbrev Diamond (r : α → α → Prop) := ∀ {a b c : α}, r a b → r a c → Join r b c

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
    ReflTransGen r a b → r a c → Join (ReflTransGen r) b c := by
  intros ab ac
  induction ab using ReflTransGen.head_induction_on generalizing c
  case refl => exists c, .single ac
  case head a'_c' _ ih =>
    obtain ⟨d, cd, c'_d⟩ := h ac a'_c'
    obtain ⟨d', b_d', d_d'⟩ := ih c'_d
    exact ⟨d', b_d', .head cd d_d'⟩

/-- The diamond property implies confluence. -/
theorem Diamond.toConfluent (h : Diamond r) : Confluent r := by
  intros a b c ab bc
  induction ab using ReflTransGen.head_induction_on generalizing c
  case refl => exists c
  case head _ _ a'_c' _ ih =>
    obtain ⟨d, cd, c'_d⟩ := h.extend bc a'_c'
    obtain ⟨d', b_d', d_d'⟩ := ih c'_d
    exact ⟨d', b_d', .trans cd d_d'⟩

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

theorem Confluent_of_unique_end {x : α} (h : ∀ y : α, ReflTransGen r y x) : Confluent r := by
  intro a b c hab hac
  exact ⟨x, h b, h c⟩

/-- An element is reducible with respect to a relation if there is a value it is related to. -/
abbrev Reducible (r : α → α → Prop) (x : α) : Prop := ∃ y, r x y

/-- A relation `r` is serial if every element is `Reducible`, i.e. `Relator.LeftTotal`. -/
class Serial (r : α → α → Prop) where
  serial : Relator.LeftTotal r

@[scoped grind →]
lemma refl_serial (r : α → α → Prop) (h : Std.Refl r) : Relation.Serial r where
  serial a := ⟨a, h.refl a⟩

instance [instRefl : Std.Refl r] : Relation.Serial r := refl_serial r instRefl

/-- An element is normal if it is not reducible. -/
abbrev Normal (r : α → α → Prop) (x : α) : Prop := ¬ Reducible r x

theorem Normal_iff (r : α → α → Prop) (x : α) : Normal r x ↔ ∀ y, ¬ r x y := by
  rw [Normal, not_exists]

/-- An element is normalizable if it is related to a normal element. -/
abbrev Normalizable (r : α → α → Prop) (x : α) : Prop :=
  ∃ n, ReflTransGen r x n ∧ Normal r n

/-- A relation is normalizing when every element is normalizable. -/
abbrev Normalizing (r : α → α → Prop) : Prop :=
  ∀ x, Normalizable r x

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
  have ⟨z, _, _⟩ := cr xy
  grind

/-- A pair of subrelations lifts to transitivity on the relation. -/
@[implicit_reducible]
def transLeftRight (s s' r : α → α → Prop) [IsTrans α r] (h : s ≤ r) (h' : s' ≤ r) :
    Trans s s' r where
  trans hab hbc := _root_.trans (h _ _ hab) (h' _ _ hbc)

/-- A subrelation lifts to transitivity on the left of the relation. -/
@[implicit_reducible]
def transLeft (s r : α → α → Prop) [IsTrans α r] (h : s ≤ r) : Trans s r r where
  trans hab hbc := _root_.trans (h _ _ hab) hbc

/-- A subrelation lifts to transitivity on the right of the relation. -/
@[implicit_reducible]
def transRight (s r : α → α → Prop) [IsTrans α r] (h : s ≤ r) : Trans r s r where
  trans hab hbc := _root_.trans hab (h _ _ hbc)

/-- Confluence implies that multi-step joinability is an equivalence. -/
theorem Confluent.equivalence_join_reflTransGen (h : Confluent r) :
    Equivalence (Join (ReflTransGen r)) := by
  apply equivalence_join
  grind

/-- An element `x` is `SN` (for strongly-normalising) for a relation `r` if it is accesible under
the inverse of `r`. -/
abbrev SN (r : α → α → Prop) := Acc (fun a b => r b a)

set_option linter.tacticAnalysis.verifyGrindOnly false in
lemma SN_iff_SN_of_rel (x : α) : SN r x ↔ ∀ y, r x y → SN r y := by grind only [Acc]

lemma SN.intro : (h : ∀ y, r x y → SN r y) → SN r x := (SN_iff_SN_of_rel x).mpr

lemma SN.of_rel (hx : SN r x) (h : r x y) : SN r y := Acc.inv hx h

@[grind →]
lemma SN.of_rel_reflTransGen (hx : SN r x) (h : ReflTransGen r x y) : SN r y := by
  induction h with
  | refl => exact hx
  | tail _ h ih => exact ih.of_rel h

lemma SN.transGen (hx : SN r x) : SN (TransGen r) x := by
  have eq : TransGen (Function.swap r) = (fun a b => TransGen r b a) := by
    ext
    exact transGen_swap
  simpa [eq] using Acc.transGen hx

lemma SN.of_le {r' : α → α → Prop} (hx : SN r x) (h : r' ≤ r) : SN r' x := by
  refine Subrelation.accessible ?_ hx
  exact subrelation_iff_le.mpr fun {x y} => h y x

@[simp]
lemma SN.iff_transGen (x : α) : SN (TransGen r) x ↔ SN r x :=
  ⟨fun hx => hx.of_le <| fun _ _ => TransGen.single, transGen⟩

/-- `SN r x` is equivalent to the more elementary definition, that there is no infinite sequence
of reductions starting with `x`. -/
theorem SN.iff_isEmpty_chain :
    SN r x ↔ IsEmpty {f : ℕ → α | f 0 = x ∧ ∀ n, r (f n) (f (n + 1))} :=
  acc_iff_isEmpty_descending_chain

lemma SN.onFun_of_image {r : β → β → Prop} {f : α → β} (hx : SN r (f x)) :
    SN (Function.onFun r f) x := InvImage.accessible f hx

lemma SN.of_normal (hx : Normal r x) : SN r x := SN.intro fun y hy => (hx ⟨y, hy⟩).elim

/-- A relation is terminating when the inverse of its transitive closure is well-founded.
  Note that this is also called Noetherian or strongly normalizing in the literature. -/
abbrev Terminating (r : α → α → Prop) := WellFounded (fun a b => r b a)

lemma Terminating.apply (hr : Terminating r) (x : α) : SN r x := WellFounded.apply hr x

lemma Terminating.iff_forall_sn : Terminating r ↔ ∀ x, SN r x :=
  ⟨WellFounded.apply, WellFounded.intro⟩

theorem Terminating.toTransGen (ht : Terminating r) : Terminating (TransGen r) := by
  simp_rw [iff_forall_sn, SN.iff_transGen] at ht ⊢
  exact ht

theorem Terminating.ofTransGen : Terminating (TransGen r) → Terminating r := by
  simp_rw [iff_forall_sn, SN.iff_transGen]
  exact id

theorem Terminating.iff_transGen : Terminating (TransGen r) ↔ Terminating r := by
  simp_rw [iff_forall_sn, SN.iff_transGen]

theorem Terminating.iff_isEmpty_chain :
    Terminating r ↔ IsEmpty {f : ℕ → α // ∀ n, r (f n) (f (n + 1))} :=
  wellFounded_iff_isEmpty_descending_chain

theorem Terminating.of_le {r' : α → α → Prop} (hr : Terminating r) (h : r' ≤ r) :
    Terminating r' := by
  rw [iff_forall_sn] at hr ⊢
  exact fun x => (hr x).of_le h

lemma Terminating.subtype_sn (r : α → α → Prop) :
    Terminating (α := {x // SN r x}) (fun a b => r a b) :=
  iff_forall_sn.mpr fun x => x.property.onFun_of_image

theorem SN.isNormalizable (hx : SN r x) : Normalizable r x := by
  -- restrict to the subtype where all elements are `SN`, so `flip r` is well-founded
  obtain ⟨⟨y, hsn⟩, hred : ReflTransGen r x y, hnorm⟩ :=
    (Terminating.subtype_sn r).has_min
    (s := Subtype.val ⁻¹' ({y | ReflTransGen r x y})) ⟨⟨x, hx⟩, ReflTransGen.refl⟩
  use y, hred
  intro ⟨z, hyz⟩
  exact hnorm ⟨z, hsn.of_rel hyz⟩ (.tail hred hyz) hyz

theorem Terminating.isNormalizing (hr : Terminating r) : Normalizing r :=
  fun x => (hr.apply x).isNormalizable

theorem Terminating.isConfluent_iff_all_unique_Normal (ht : Terminating r) :
    Confluent r ↔ ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n := by
  have hn : Normalizing r := ht.isNormalizing
  constructor
  · intro hc a
    apply existsUnique_of_exists_of_unique (hn a)
    rintro n₁ n₂ ⟨hr₁, hn₁⟩ ⟨hr₂, hn₂⟩
    have hj : Join (ReflTransGen r) n₁ n₂ := hc hr₁ hr₂
    obtain ⟨m, h₁, h₂⟩ := hj
    rw [Normal.reflTransGen_eq hn₁ h₁, Normal.reflTransGen_eq hn₂ h₂]
  · intro h a b c hab hac
    obtain ⟨na, ⟨han, hnnor⟩, H⟩ := h a
    use na
    obtain ⟨nb, hbnb, hnb⟩ := hn b
    obtain ⟨nc, hcnc, hnc⟩ := hn c
    have hanb : (ReflTransGen r) a nb := ReflTransGen.trans hab hbnb
    have hanc : (ReflTransGen r) a nc := ReflTransGen.trans hac hcnc
    have hnanb : nb = na := H nb ⟨hanb, hnb⟩
    have hnanc : nc = na := H nc ⟨hanc, hnc⟩
    rw [hnanb] at hbnb
    rw [hnanc] at hcnc
    exact ⟨hbnb, hcnc⟩

/-- A relation is convergent when it is both confluent and terminating. -/
abbrev Convergent (r : α → α → Prop) := Confluent r ∧ Terminating r

theorem Convergent.isTerminating (h : Convergent r) : Terminating r := h.right

theorem Convergent.isConfluent (h : Convergent r) : Confluent r := h.left

theorem Convergent.isNormalizing (h : Convergent r) : Normalizing r := h.isTerminating.isNormalizing

theorem Convergent.unique_Normal (h : Convergent r) :
    ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n :=
  h.isTerminating.isConfluent_iff_all_unique_Normal.mp h.isConfluent

/-- A relation is locally confluent when all reductions with a common origin are multi-joinable -/
abbrev LocallyConfluent (r : α → α → Prop) :=
  ∀ {a b c : α}, r a b → r a c → Join (ReflTransGen r) b c

theorem Confluent.toLocallyConfluent (h : Confluent r) : LocallyConfluent r := by
  intro _ _ _ ab ac
  exact h (.single ab) (.single ac)

/-- Newman's lemma: a terminating, locally confluent relation is confluent. -/
theorem LocallyConfluent.Terminating_toConfluent (hlc : LocallyConfluent r) (ht : Terminating r) :
    Confluent r := by
  intro x
  induction x using ht.induction with
  | h x ih =>
    intro y z xy xz
    cases xy.cases_head with
    | inl => exists z; grind
    | inr h =>
      obtain ⟨y₁, x_y₁, y₁_y⟩ := h
      cases xz.cases_head with
      | inl => exists y; grind
      | inr h =>
        obtain ⟨z₁, x_z₁, z₁_z⟩ := h
        have ⟨u, z₁_u, y₁_u⟩ := hlc x_z₁ x_y₁
        have ⟨v, uv, yv⟩ : Join (ReflTransGen r) u y := by grind
        have ⟨w, vw, zw⟩ : Join (ReflTransGen r) v z := by grind [ReflTransGen.trans]
        exact ⟨w, .trans yv vw, zw⟩

/-- A relation is strongly confluent when single steps are reflexive- and multi-joinable. -/
abbrev StronglyConfluent (r : α → α → Prop) :=
  ∀ {x y₁ y₂}, r x y₁ → r x y₂ → ∃ z, ReflGen r y₁ z ∧ ReflTransGen r y₂ z

/-- Generalization of `Confluent` to two relations. -/
def Commute (r₁ r₂ : α → α → Prop) := ∀ {x y₁ y₂},
  ReflTransGen r₁ x y₁ → ReflTransGen r₂ x y₂ → ∃ z, ReflTransGen r₂ y₁ z ∧ ReflTransGen r₁ y₂ z

theorem Commute.symmetric : Symmetric (@Commute α) := by
  intro r₁ r₂ h x y₁ y₂ x_y₁ x_y₂
  obtain ⟨_, _, _⟩ := h x_y₂ x_y₁
  grind

theorem Commute.toConfluent : Commute r r = Confluent r := rfl

/-- Generalization of `StronglyConfluent` to two relations. -/
def StronglyCommute (r₁ r₂ : α → α → Prop) :=
  ∀ {x y₁ y₂}, r₁ x y₁ → r₂ x y₂ → ∃ z, ReflGen r₂ y₁ z ∧ ReflTransGen r₁ y₂ z

theorem StronglyCommute.toStronglyConfluent : StronglyCommute r r = StronglyConfluent r := rfl

/-- Generalization of `Diamond` to two relations. -/
def DiamondCommute (r₁ r₂ : α → α → Prop) :=
  ∀ {x y₁ y₂}, r₁ x y₁ → r₂ x y₂ → ∃ z, r₂ y₁ z ∧ r₁ y₂ z

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
  intro x y₁ y₂ x_y₁ x_y₂
  induction x_y₂ with
  | refl => exists y₁
  | @tail a b xa ab ih =>
    obtain ⟨z, y₁_z, y₂_z⟩ := ih
    obtain ⟨w, zw, bw⟩ := h.extend y₂_z ab
    exact ⟨w, y₁_z.trans zw.to_reflTransGen, bw⟩

theorem StronglyConfluent.toConfluent (h : StronglyConfluent r) : Confluent r :=
  StronglyCommute.toCommute h

variable {r₁ r₂ : α → α → Prop}

@[scoped grind <=]
theorem join_inl (r₁_ab : r₁ a b) : (r₁ ⊔ r₂) a b :=
  Or.inl r₁_ab

@[scoped grind <=]
theorem join_inr (r₂_ab : r₂ a b) : (r₁ ⊔ r₂) a b :=
  Or.inr r₂_ab

@[scoped grind <=]
theorem join_inl_reflTransGen (r₁_ab : ReflTransGen r₁ a b) : ReflTransGen (r₁ ⊔ r₂) a b := by
  induction r₁_ab <;> grind

@[scoped grind <=]
theorem join_inr_reflTransGen (r₂_ab : ReflTransGen r₂ a b) : ReflTransGen (r₁ ⊔ r₂) a b := by
  induction r₂_ab <;> grind

lemma Commute.join_left (c₁ : Commute r₁ r₃) (c₂ : Commute r₂ r₃) : Commute (r₁ ⊔ r₂) r₃ := by
  intro x y z xy xz
  induction xy with
  | refl => grind
  | @tail b c _ bc ih =>
    have ⟨w, bw, _⟩ := ih
    cases bc with
    | inl bc =>
      obtain ⟨_, _, _⟩ := c₁ (.single bc) bw
      grind [ReflTransGen.trans]
    | inr bc =>
      obtain ⟨_, _, _⟩ := c₂ (.single bc) bw
      grind [ReflTransGen.trans]

theorem Commute.join_confluent (c₁ : Confluent r₁) (c₂ : Confluent r₂) (comm : Commute r₁ r₂) :
    Confluent (r₁ ⊔ r₂) := by
  intro a b c ab ac
  induction ab generalizing c with
  | refl => exists c
  | @tail x y ax xy ih =>
    have h_comm : Commute (r₁ ⊔ r₂) (r₁ ⊔ r₂) := by apply_rules [join_left, symmetric]
    obtain ⟨z, xz, cz⟩ := ih ac
    obtain ⟨w, yw, zw⟩ := h_comm (.single xy) xz
    exact ⟨w, yw, cz.trans zw⟩

/-- If a relation is squeezed by a relation and its multi-step closure, they are multi-step equal -/
theorem reflTransGen_mono_closed (h₁ : r₁ ≤ r₂) (h₂ : r₂ ≤ ReflTransGen r₁) :
    ReflTransGen r₁ = ReflTransGen r₂ := by
  ext
  exact ⟨ReflTransGen.mono @h₁, reflTransGen_closed @h₂⟩

lemma ReflGen.compRel_symm : ReflGen (SymmGen r) a b → ReflGen (SymmGen r) b a
| .refl => .refl
| .single (.inl h) => .single (.inr h)
| .single (.inr h) => .single (.inl h)

@[simp, grind =]
theorem reflTransGen_compRel : ReflTransGen (SymmGen r) = EqvGen r := by
  ext a b
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | tail hab hbc ih =>
      cases hbc with
      | inl h => exact ih.trans _ _ _ (.rel _ _ h)
      | inr h => exact ih.trans _ _ _ (.symm _ _ (.rel _ _ h))
  · intro h
    induction h with
    | rel _ _ ih => exact .single (.inl ih)
    | refl x => exact .refl
    | symm x y eq ih =>
      rw [symmGen_swap]
      exact reflTransGen_swap.mp ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `Relator.RightUnique` corresponds to deterministic reductions, which are confluent, as all
multi-reductions with a common origin start the same (this fact is
`Relation.ReflTransGen.total_of_right_unique`.) -/
theorem RightUnique.toConfluent (hr : Relator.RightUnique r) : Confluent r := by
  intro a b c ab ac
  obtain (h | h) := ReflTransGen.total_of_right_unique hr ab ac
  · use c
  · use b

public meta section

open Lean Elab Meta Command Term

/--
  This command adds notations for relations. This should not usually be called directly, but from
  the `reduction_sys` attribute.

  As an example `reduction_notation foo "β"` will add the notations "⭢β" and "↠β".

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax attrKind "reduction_notation" ident (str)? : command
macro_rules
  | `($kind:attrKind reduction_notation $rel $sym) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ⭢" $sym:str t':39 => $rel t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ↠" $sym:str t':39 => Relation.ReflTransGen $rel t t'
     )
  | `($kind:attrKind reduction_notation $rel) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ⭢ " t':39 => $rel t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ↠ " t':39 => Relation.ReflTransGen $rel t t'
     )


/--
  This attribute calls the `reduction_notation` command for the annotated declaration, such as in:

  ```
  @[reduction_sys "ₙ", simp]
  def PredReduction (a b : ℕ) : Prop := a = b + 1
  ```
-/
syntax (name := reductionSys) "reduction_sys" (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `reductionSys
  descr := "Register notation for a relation and its closures."
  add := fun decl stx _ => MetaM.run' do
    let currNamespace ← getCurrNamespace
    match stx with
    | `(attr | reduction_sys $sym) =>
        let mut sym := sym
        unless sym.getString.endsWith " " do
          sym := Syntax.mkStrLit (sym.getString ++ " ")
        liftCommandElabM <| do
          modifyScope ({ · with currNamespace })
          elabCommand (← `(scoped reduction_notation $(mkIdent decl) $sym))
    | `(attr | reduction_sys) =>
        liftCommandElabM <| do
          modifyScope ({ · with currNamespace })
          elabCommand (← `(scoped reduction_notation $(mkIdent decl)))
    | _ => throwError "invalid syntax for 'reduction_sys' attribute"
}

end

end Relation
