/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Data.List.Pairwise
public import Mathlib.Order.Comparable
public import Mathlib.Order.WellFounded

/-! # Relations: Confluence and Termination

This module proves some properties regarding confluence and termination that are used for both
lambda calculi and combinatory logic. Some notable theorems:

* `Diamond.toConfluent`: the diamond property implies confluence
* `LocallyConfluent.Terminating_toConfluent`: Newman's lemma

## References

* [*Term Rewriting and All That*][Baader1998]

-/

@[expose] public section

variable {α : Type*} {r r₁ r₂ : α → α → Prop}

theorem WellFounded.ofTransGen (trans_wf : WellFounded (Relation.TransGen r)) : WellFounded r := by
  grind [WellFounded.wellFounded_iff_has_min, Relation.TransGen]

@[simp, grind =]
theorem WellFounded.iff_transGen : WellFounded (Relation.TransGen r) ↔ WellFounded r :=
  ⟨ofTransGen, transGen⟩

namespace Relation

attribute [scoped grind] ReflGen TransGen ReflTransGen EqvGen

theorem ReflGen.to_eqvGen (h : ReflGen r a b) : EqvGen r a b :=
  EqvGen.reflGen_le_eqvGen r _ _ h

theorem TransGen.to_eqvGen (h : TransGen r a b) : EqvGen r a b :=
  EqvGen.transGen_le_eqvGen r _ _ h

theorem ReflTransGen.to_eqvGen (h : ReflTransGen r a b) : EqvGen r a b :=
  EqvGen.reflTransGen_le_eqvGen r _ _ h

theorem SymmGen.to_eqvGen (h : SymmGen r a b) : EqvGen r a b :=
  EqvGen.symmGen_le_eqvGen r _ _ h

attribute [scoped grind →] ReflGen.to_eqvGen TransGen.to_eqvGen ReflTransGen.to_eqvGen
  SymmGen.to_eqvGen

theorem MJoin.refl (a : α) : MJoin r a a := by
  use a

theorem MJoin.single (h : ReflTransGen r a b) : MJoin r a b := by
  use b

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
theorem Diamond.to_confluent (h : Diamond r) : Confluent r := by
  intros a b c ab bc
  induction ab using ReflTransGen.head_induction_on generalizing c
  case refl => exists c
  case head _ _ a'_c' _ ih =>
    obtain ⟨d, cd, c'_d⟩ := h.extend bc a'_c'
    obtain ⟨d', b_d', d_d'⟩ := ih c'_d
    exact ⟨d', b_d', .trans cd d_d'⟩

@[deprecated (since := "2026-09-03")] alias Diamond.toConfluent := Diamond.to_confluent

theorem Confluent.to_churchRosser (h : Confluent r) : ChurchRosser r := by
  intro x y h_eqv
  induction h_eqv with
  | rel _ b => exists b; grind [ReflTransGen.single]
  | refl a => exists a
  | symm a b _ ih => exact symm ih
  | trans _ _ _ _ _ ih1 ih2 =>
      obtain ⟨u, _, hbu⟩ := ih1
      obtain ⟨v, hbv, _⟩ := ih2
      obtain ⟨w, _, _⟩ := h hbu hbv
      exists w
      grind [ReflTransGen.trans]

@[deprecated (since := "2026-09-03")] alias Confluent.toChurchRosser := Confluent.to_churchRosser

theorem SemiConfluent.to_confluent (h : SemiConfluent r) : Confluent r := by
  intro x y1 y2 h_xy1 h_xy2
  induction h_xy1 with
  | refl => use y2
  | tail h_xz h_zy1 ih =>
      obtain ⟨u, h_zu, _⟩ := ih
      obtain ⟨v, _, _⟩ := h h_zu h_zy1
      exists v
      grind [ReflTransGen.trans]

@[deprecated (since := "2026-09-03")] alias SemiConfluent.toConfluent := SemiConfluent.to_confluent

attribute [scoped grind →] Confluent.to_churchRosser SemiConfluent.to_confluent

private theorem confluent_equivalents : [ChurchRosser r, SemiConfluent r, Confluent r].TFAE := by
  grind [List.tfae_cons_cons, List.tfae_singleton]

theorem semiConfluent_iff_churchRosser : SemiConfluent r ↔ ChurchRosser r :=
  List.TFAE.out confluent_equivalents 2 1

@[deprecated (since := "2026-09-03")] alias SemiConfluent_iff_ChurchRosser :=
  semiConfluent_iff_churchRosser

theorem confluent_iff_churchRosser : Confluent r ↔ ChurchRosser r :=
  List.TFAE.out confluent_equivalents 3 1

@[deprecated (since := "2026-09-03")] alias Confluent_iff_ChurchRosser := confluent_iff_churchRosser

theorem confluent_iff_semiConfluent : Confluent r ↔ SemiConfluent r :=
  List.TFAE.out confluent_equivalents 3 2

@[deprecated (since := "2026-09-03")] alias Confluent_iff_SemiConfluent :=
  confluent_iff_semiConfluent

theorem confluent_of_unique_end {x : α} (h : ∀ y : α, ReflTransGen r y x) : Confluent r := by
  intro a b c hab hac
  exact ⟨x, h b, h c⟩

@[deprecated (since := "2026-09-03")] alias Confluent_of_unique_end := confluent_of_unique_end

theorem normal_iff (r : α → α → Prop) (x : α) : Normal r x ↔ ∀ y, ¬ r x y := by
  rw [Normal, not_exists]

@[deprecated (since := "2026-09-03")] alias Normal_iff := normal_iff

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

/-- Confluence implies that multi-step joinability is an equivalence. -/
theorem Confluent.equivalence_join_reflTransGen (h : Confluent r) :
    Equivalence (Join (ReflTransGen r)) := by
  apply equivalence_join
  grind

lemma SN_iff_SN_of_rel (x : α) : SN r x ↔ ∀ y, r x y → SN r y := by grind [Acc]

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

theorem SN.normalizable (hx : SN r x) : Normalizable r x := by
  induction hx with | intro x h ih =>
  by_cases hy: (∃ y, r x y)
  · obtain ⟨y, hy⟩ := hy
    obtain ⟨z, hz, hnormal⟩ := ih y hy
    exact ⟨z, .head hy hz, hnormal⟩
  · exists x

lemma Terminating.apply (hr : Terminating r) (x : α) : SN r x := WellFounded.apply hr x

lemma Terminating.iff_forall_sn : Terminating r ↔ ∀ x, SN r x :=
  ⟨WellFounded.apply, WellFounded.intro⟩

theorem Terminating.to_transGen (ht : Terminating r) : Terminating (TransGen r) := by
  simp_rw [iff_forall_sn, SN.iff_transGen] at ht ⊢
  exact ht

@[deprecated (since := "2026-09-03")] alias Terminating.toTransGen := Terminating.to_transGen

/-- A terminating relation is acyclic. -/
theorem Terminating.to_acyclic (ht : Terminating r) : Acyclic r :=
  ⟨fun x hx => ht.to_transGen.irrefl.irrefl x hx⟩

@[deprecated (since := "2026-09-03")] alias Terminating.toAcyclic := Terminating.to_acyclic

theorem Terminating.of_transGen : Terminating (TransGen r) → Terminating r := by
  simp_rw [iff_forall_sn, SN.iff_transGen]
  exact id

@[deprecated (since := "2026-09-03")] alias Terminating.ofTransGen := Terminating.of_transGen

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

theorem Terminating.to_normalizing (hr : Terminating r) : Normalizing r :=
  fun x => (hr.apply x).normalizable

@[deprecated (since := "2026-09-03")] alias Terminating.isNormalizing := Terminating.to_normalizing

theorem Terminating.confluent_iff_forall_unique_normal (ht : Terminating r) :
    Confluent r ↔ ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n := by
  have hn : Normalizing r := ht.to_normalizing
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

@[deprecated (since := "2026-09-03")] alias Terminating.isConfluent_iff_all_unique_Normal :=
  Terminating.confluent_iff_forall_unique_normal

theorem Convergent.to_terminating (h : Convergent r) : Terminating r := h.right

@[deprecated (since := "2026-09-03")] alias Convergent.isTerminating := Convergent.to_terminating

theorem Convergent.to_confluent (h : Convergent r) : Confluent r := h.left

@[deprecated (since := "2026-09-03")] alias Convergent.isConfluent := Convergent.to_confluent

theorem Convergent.to_normalizing (h : Convergent r) : Normalizing r :=
  h.to_terminating.to_normalizing

@[deprecated (since := "2026-09-03")] alias Convergent.isNormalizing := Convergent.to_normalizing

theorem Convergent.unique_normal (h : Convergent r) :
    ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n :=
  h.to_terminating.confluent_iff_forall_unique_normal.mp h.to_confluent

@[deprecated (since := "2026-09-03")] alias Convergent.unique_Normal := Convergent.unique_normal

theorem Confluent.to_locallyConfluent (h : Confluent r) : LocallyConfluent r := by
  intro _ _ _ ab ac
  exact h (.single ab) (.single ac)

@[deprecated (since := "2026-09-03")] alias Confluent.toLocallyConfluent :=
  Confluent.to_locallyConfluent

/-- Newman's lemma: a terminating, locally confluent relation is confluent. -/
theorem LocallyConfluent.terminating_toConfluent (hlc : LocallyConfluent r) (ht : Terminating r) :
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

@[deprecated (since := "2026-09-03")] alias LocallyConfluent.Terminating_toConfluent :=
  LocallyConfluent.terminating_toConfluent

instance : Std.Symm (@Commute α) where
  symm r₁ r₂ h x y₁ y₂ x_y₁ x_y₂ := by grind [h x_y₂ x_y₁]

theorem Commute.to_confluent : Commute r r = Confluent r := rfl

@[deprecated (since := "2026-09-03")] alias Commute.toConfluent := Commute.to_confluent

theorem StronglyCommute.to_stronglyConfluent : StronglyCommute r r = StronglyConfluent r := rfl

@[deprecated (since := "2026-09-03")] alias StronglyCommute.toStronglyConfluent :=
  StronglyCommute.to_stronglyConfluent

theorem DiamondCommute.to_diamond : DiamondCommute r r = Diamond r := by rfl

@[deprecated (since := "2026-09-03")] alias DiamondCommute.toDiamond := DiamondCommute.to_diamond

theorem StronglyCommute.extend (h : StronglyCommute r₁ r₂) (xy : ReflTransGen r₁ x y)
    (xz : r₂ x z) : ∃ w, ReflGen r₂ y w ∧ ReflTransGen r₁ z w := by
  induction xy with
  | refl => exact ⟨z, .single xz, .refl⟩
  | @tail b c _ bc ih =>
    obtain ⟨w, bw, zw⟩ := ih
    cases bw with
    | refl => exact ⟨c, .refl, zw.tail bc⟩
    | single bw => cases h bc bw; grind [ReflTransGen.trans]

theorem StronglyCommute.to_commute (h : StronglyCommute r₁ r₂) : Commute r₁ r₂ := by
  intro x y₁ y₂ x_y₁ x_y₂
  induction x_y₂ with
  | refl => exists y₁
  | @tail a b xa ab ih =>
    obtain ⟨z, y₁_z, y₂_z⟩ := ih
    obtain ⟨w, zw, bw⟩ := h.extend y₂_z ab
    exact ⟨w, y₁_z.trans zw.to_reflTransGen, bw⟩

@[deprecated (since := "2026-09-03")] alias StronglyCommute.toCommute := StronglyCommute.to_commute

theorem StronglyConfluent.to_confluent (h : StronglyConfluent r) : Confluent r :=
  StronglyCommute.to_commute h

@[deprecated (since := "2026-09-03")] alias StronglyConfluent.toConfluent :=
  StronglyConfluent.to_confluent

variable {r₁ r₂ : α → α → Prop}

@[scoped grind <=]
theorem join_inl (r₁_ab : r₁ a b) : (r₁ ⊔ r₂) a b :=
  Or.inl r₁_ab

@[scoped grind <=]
theorem join_inr (r₂_ab : r₂ a b) : (r₁ ⊔ r₂) a b :=
  Or.inr r₂_ab

@[scoped grind <=]
theorem join_inl_reflTransGen (r₁_ab : ReflTransGen r₁ a b) : ReflTransGen (r₁ ⊔ r₂) a b :=
  ReflTransGen.mono le_sup_left _ _ r₁_ab

@[scoped grind <=]
theorem join_inr_reflTransGen (r₂_ab : ReflTransGen r₂ a b) : ReflTransGen (r₁ ⊔ r₂) a b :=
  ReflTransGen.mono le_sup_right _ _ r₂_ab

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
  rw [← Commute.to_confluent]
  apply_rules [join_left, symm]

/-- If a relation is squeezed by a relation and its multi-step closure, they are multi-step equal -/
theorem reflTransGen_mono_closed (h₁ : r₁ ≤ r₂) (h₂ : r₂ ≤ ReflTransGen r₁) :
    ReflTransGen r₁ = ReflTransGen r₂ := by
  ext a b
  exact ⟨ReflTransGen.mono h₁ a b, reflTransGen_closed h₂ a b⟩

@[deprecated Relation.ReflGen.stdSymm (since := "2026-09-03")]
lemma ReflGen.symmGen_symm : ReflGen (SymmGen r) a b → ReflGen (SymmGen r) b a :=
  Std.Symm.symm a b

@[simp, grind =]
theorem reflTransGen_symmGen : ReflTransGen (SymmGen r) = EqvGen r := EqvGen.reflTransGen_symmGen r

/-- `Relator.RightUnique` corresponds to deterministic reductions, which are confluent, as all
multi-reductions with a common origin start the same (this fact is
`Relation.ReflTransGen.total_of_right_unique`.) -/
theorem RightUnique.to_confluent (hr : Relator.RightUnique r) : Confluent r := by
  intro a b c ab ac
  obtain (h | h) := ReflTransGen.total_of_right_unique hr ab ac
  · use c
  · use b

@[deprecated (since := "2026-09-03")] alias RightUnique.toConfluent := RightUnique.to_confluent

end Relation
