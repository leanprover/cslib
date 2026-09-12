/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Foundations.Relation.Termination
public import Mathlib.Tactic.TFAE

/-! # Relations: Confluence

This module proves some properties regarding confluence that are used for both lambda calculi and
combinatory logic. Some notable theorems:

* `Diamond.to_confluent`: the diamond property implies confluence
* `LocallyConfluent.terminating_toConfluent`: Newman's lemma

We prove most results first for two relations, where `Confluent r` becomes `Commute r₁ r₂`, then
specialize to the classical case where `r₁ = r₂`.

## References

* [*Term Rewriting and All That*][Baader1998]

-/

@[expose] public section

variable {α : Type*} {r r₁ r₂ : α → α → Prop}

namespace Relation

open Function ReflTransGen

theorem Commute.to_confluent : Commute r r = Confluent r := rfl

@[deprecated (since := "2026-09-03")] alias Commute.toConfluent := Commute.to_confluent

@[simp] theorem StronglyCommute.to_stronglyConfluent :
  StronglyCommute r r = StronglyConfluent r := rfl

@[deprecated (since := "2026-09-03")] alias StronglyCommute.toStronglyConfluent :=
  StronglyCommute.to_stronglyConfluent

@[simp] theorem DiamondCommute.to_diamond : DiamondCommute r r = Diamond r := rfl

@[deprecated (since := "2026-09-03")] alias DiamondCommute.toDiamond := DiamondCommute.to_diamond

@[simp] theorem SemiCommute.to_semiConfluent : SemiCommute r r = SemiConfluent r := rfl

@[simp] theorem LocallyCommute.to_locallyConfluent : LocallyCommute r r = LocallyConfluent r := rfl

instance : Std.Symm (@Commute α) where
  symm r₁ r₂ h x y₁ y₂ x_y₁ x_y₂ := by grind [h x_y₂ x_y₁, Join₂]

lemma DiamondCommute.diamond_commute_reflTransGen_right (h : DiamondCommute r₁ r₂) :
    DiamondCommute r₁ (ReflTransGen r₂) := by
  intro a b c h₁ h₂
  induction h₂ using ReflTransGen.head_induction_on generalizing b with
  | refl => exact Join₂.single_right h₁
  | head ha _ ih =>
    obtain ⟨d, hbd, hcd⟩ := h h₁ ha
    obtain ⟨d', hdd', hcd'⟩ := ih hcd
    exact ⟨d', hdd'.head hbd, hcd'⟩

lemma DiamondCommute.to_semiCommute (h : DiamondCommute r₁ r₂) : SemiCommute r₁ r₂ :=
  fun h₁ h₂ => Join₂.mono le_rfl ReflTransGen.le_reflTransGen _ _ <|
    h.diamond_commute_reflTransGen_right h₁ h₂

/-- Extending a multistep reduction by a single step preserves multi-joinability. -/
lemma Diamond.to_semiConfluent (h : Diamond r) : SemiConfluent r := DiamondCommute.to_semiCommute h

@[deprecated (since := "2026-09-12")] alias Diamond.extend := Diamond.to_semiConfluent

theorem Commute.isTrans_join₂_reflTransGen (h : Commute r₁ r₂) :
    IsTrans α (Join₂ (ReflTransGen r₁) (ReflTransGen r₂)) where
  trans a b c := by
    intro ⟨d, had, hbd⟩ ⟨d', hbd', hcd'⟩
    obtain ⟨e, he, he'⟩ := h hbd' hbd
    exact ⟨e, had.trans he', hcd'.trans he⟩

theorem Confluent.isTrans_join_reflTransGen (h : Confluent r) : IsTrans α (Join (ReflTransGen r)) :=
  Commute.isTrans_join₂_reflTransGen h

theorem SemiCommute.to_commute (h : SemiCommute r₁ r₂) : Commute r₁ r₂ := by
  intro a b₁ b₂ hab₁ hab₂
  induction hab₁ with
  | refl => use b₂
  | tail hab hbb' ih =>
    obtain ⟨d, hd, hd'⟩ := ih
    obtain ⟨e, he, he'⟩ := h hbb' hd
    use e, he, hd'.trans he'

theorem SemiConfluent.to_confluent (h : SemiConfluent r) : Confluent r := SemiCommute.to_commute h

@[deprecated (since := "2026-09-03")] alias SemiConfluent.toConfluent := SemiConfluent.to_confluent

theorem commute_equivalents :
    [SemiCommute r₁ r₂, Commute r₁ r₂, IsTrans α (Join₂ (ReflTransGen r₁) (ReflTransGen r₂)),
      ReflTransGen (r₁ ⊔ swap r₂) ≤ Join₂ (ReflTransGen r₁) (ReflTransGen r₂),
      ReflTransGen (r₁ ⊔ swap r₂) = Join₂ (ReflTransGen r₁) (ReflTransGen r₂)].TFAE := by
  tfae_have 1 → 2 := SemiCommute.to_commute
  tfae_have 2 → 3 := Commute.isTrans_join₂_reflTransGen
  tfae_have 3 → 4 := fun h => reflTransGen_le_of_le <|
    sup_le left_le_join₂_reflTransGen swap_right_le_join₂_reflTransGen
  tfae_have 4 → 5 := fun h => h.antisymm <|
    join₂_reflTransGen_le (le_sup_left.trans le_reflTransGen) (le_sup_right.trans le_reflTransGen)
  tfae_have 5 → 1 := by
    intro h a b₁ b₂ h₁ h₂
    rw [Join₂.swap_iff, ← h]
    exact (ReflTransGen.mono le_sup_right _ _ <| reflTransGen_swap.mpr h₂).tail (Or.inl h₁)
  tfae_finish

theorem semiCommute_iff_commute : SemiCommute r₁ r₂ ↔ Commute r₁ r₂ := commute_equivalents.out 1 2

theorem DiamondCommute.to_commute (h : DiamondCommute r₁ r₂) : Commute r₁ r₂ :=
  semiCommute_iff_commute.mp h.to_semiCommute

theorem churchRosser_iff_eqvGen_le_join_reflTransGen :
    ChurchRosser r ↔ EqvGen r ≤ Join (ReflTransGen r) :=
  Iff.rfl

theorem confluent_equivalents :
    [ChurchRosser r, SemiConfluent r, Confluent r, IsTrans α (Join (ReflTransGen r)),
      EqvGen r ≤ Join (ReflTransGen r), EqvGen r = Join (ReflTransGen r)].TFAE := by
  refine (List.tfae_cons ?_).mpr ⟨churchRosser_iff_eqvGen_le_join_reflTransGen, ?_⟩
  · grind
  · simpa [reflTransGen_symmGen] using commute_equivalents (r₁ := r) (r₂ := r)

theorem semiConfluent_iff_churchRosser : SemiConfluent r ↔ ChurchRosser r :=
  List.TFAE.out confluent_equivalents 2 1

@[deprecated (since := "2026-09-03")] alias SemiConfluent_iff_ChurchRosser :=
  semiConfluent_iff_churchRosser

theorem confluent_iff_churchRosser : Confluent r ↔ ChurchRosser r :=
  List.TFAE.out confluent_equivalents 3 1

alias ⟨_, Confluent.to_churchRosser⟩ := confluent_iff_churchRosser

@[deprecated (since := "2026-09-03")] alias Confluent_iff_ChurchRosser := confluent_iff_churchRosser

attribute [scoped grind →] Confluent.to_churchRosser SemiConfluent.to_confluent

theorem confluent_iff_semiConfluent : Confluent r ↔ SemiConfluent r :=
  List.TFAE.out confluent_equivalents 3 2

@[deprecated (since := "2026-09-03")] alias Confluent_iff_SemiConfluent :=
  confluent_iff_semiConfluent

theorem Diamond.to_confluent (h : Diamond r) : Confluent r := DiamondCommute.to_commute h

@[deprecated (since := "2026-09-03")] alias Diamond.toConfluent := Diamond.to_confluent

theorem confluent_of_unique_end {x : α} (h : ∀ y : α, ReflTransGen r y x) : Confluent r := by
  intro a b c hab hac
  exact ⟨x, h b, h c⟩

@[deprecated (since := "2026-09-03")] alias Confluent_of_unique_end := confluent_of_unique_end

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

theorem Normalizing.confluent_iff_forall_unique_normal (hn : Normalizing r) :
    Confluent r ↔ ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n := by
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
    grind

theorem Terminating.confluent_iff_forall_unique_normal (ht : Terminating r) :
    Confluent r ↔ ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n :=
  ht.to_normalizing.confluent_iff_forall_unique_normal

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

theorem LocallyCommute.commute_of_terminating_sup (hlc : LocallyCommute r₁ r₂)
    (ht : Terminating (r₁ ⊔ r₂)) : Commute r₁ r₂ := by
  intro x
  induction x using ht.induction with
  | h x ih =>
    intro y z hy hz
    rcases hy.cases_head with (rfl | ⟨y', hy, hy'⟩)
    · use z
    · rcases hz.cases_head with (rfl | ⟨z', hz, hz'⟩)
      · use y
      · obtain ⟨u, hyu, hzu⟩ := hlc hy hz
        obtain ⟨v, hyv, huv⟩ := ih y' (join_inl hy) hy' hyu
        obtain ⟨w, hvw, hzw⟩ := ih z' (join_inr hz) (hzu.trans huv) hz'
        exact ⟨w, hyv.trans hvw, hzw⟩

/-- Newman's lemma: a terminating, locally confluent relation is confluent. -/
theorem LocallyConfluent.terminating_toConfluent (hlc : LocallyConfluent r) (ht : Terminating r) :
    Confluent r := LocallyCommute.commute_of_terminating_sup hlc ((sup_idem r).symm ▸ ht)

@[deprecated (since := "2026-09-03")] alias LocallyConfluent.Terminating_toConfluent :=
  LocallyConfluent.terminating_toConfluent

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

lemma Commute.join_left (c₁ : Commute r₁ r₃) (c₂ : Commute r₂ r₃) : Commute (r₁ ⊔ r₂) r₃ := by
  intro x y z xy xz
  induction xy with
  | refl => grind [Join₂]
  | @tail b c _ bc ih =>
    have ⟨w, bw, _⟩ := ih
    cases bc with
    | inl bc =>
      obtain ⟨_, _, _⟩ := c₁ (.single bc) bw
      grind [Join₂, ReflTransGen.trans]
    | inr bc =>
      obtain ⟨_, _, _⟩ := c₂ (.single bc) bw
      grind [Join₂, ReflTransGen.trans]

theorem Commute.join_confluent (c₁ : Confluent r₁) (c₂ : Confluent r₂) (comm : Commute r₁ r₂) :
    Confluent (r₁ ⊔ r₂) := by
  rw [← Commute.to_confluent]
  apply_rules [join_left, symm]

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
