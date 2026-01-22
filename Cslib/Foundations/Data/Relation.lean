/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Logic.Relation
public import Mathlib.Data.List.TFAE
public import Mathlib.Order.WellFounded
public import Mathlib.Order.BooleanAlgebra.Basic

@[expose] public section

variable {α : Type*} {r : α → α → Prop}

theorem WellFounded.ofTransGen (trans_wf : WellFounded (Relation.TransGen r)) : WellFounded r := by
  grind [WellFounded.wellFounded_iff_has_min, Relation.TransGen]

@[simp, grind =]
theorem WellFounded.iff_transGen : WellFounded (Relation.TransGen r) ↔ WellFounded r :=
  ⟨ofTransGen, transGen⟩

/-! # Relations

## References

* [*Term Rewriting and All That*][Baader1998]

-/

namespace Relation

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

/-- A relation is terminating when the inverse of its transitive closure is well-founded.
  Note that this is also called Noetherian or strongly normalizing in the literature. -/
abbrev Terminating (r : α → α → Prop) := WellFounded (fun a b => r b a)

theorem Terminating.toTransGen (ht : Terminating r) : Terminating (TransGen r) := by
  simp only [Terminating]
  convert WellFounded.transGen ht using 1
  grind [transGen_swap, WellFounded.transGen]

theorem Terminating.ofTransGen : Terminating (TransGen r) → Terminating r := by
  simp only [Terminating]
  convert @WellFounded.ofTransGen α (Function.swap r) using 2
  grind [transGen_swap]

theorem Terminating.iff_transGen : Terminating (TransGen r) ↔ Terminating r :=
  ⟨ofTransGen, toTransGen⟩

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
theorem reflTransGen_mono_closed (h₁ : Subrelation r₁ r₂) (h₂ : Subrelation r₂ (ReflTransGen r₁)) :
    ReflTransGen r₁ = ReflTransGen r₂ := by
  ext
  exact ⟨ReflTransGen.mono @h₁, reflTransGen_closed @h₂⟩

section Steps

/--
A relation `r` relates two elements of `α` in `n` steps
if there is a chain of `n` pairs `(t_i, t_{i+1})` such that `r t_i t_{i+1}` for each `i`,
starting from the first element and ending at the second.
-/
inductive relatesInSteps (r : α → α → Prop) : α → α → ℕ → Prop
  | refl (t : α) : relatesInSteps r t t 0
  | cons (t t' t'' : α) (n : ℕ) (h₁ : r t t') (h₂ : relatesInSteps r t' t'' n) :
      relatesInSteps r t t'' (n + 1)

lemma relatesInSteps.single {a b : α} (h : r a b) :
    relatesInSteps r a b 1 := by
  exact relatesInSteps.cons a b b 0 h (relatesInSteps.refl b)

lemma relatesInSteps.zero {a b : α} (h : relatesInSteps r a b 0) : a = b := by
  cases h
  rfl

@[simp]
lemma relatesInSteps.zero_iff {a b : α} : relatesInSteps r a b 0 ↔ a = b := by
  constructor
  · exact relatesInSteps.zero
  · intro rfl
    exact relatesInSteps.refl a

lemma relatesInSteps.trans {a b c : α} {n m : ℕ}
    (h₁ : relatesInSteps r a b n) (h₂ : relatesInSteps r b c m) :
    relatesInSteps r a c (n + m) := by
  induction h₁ with
  | refl _ =>
    rw [Nat.zero_add]
    exact h₂
  | cons t t' t'' k h_red _ ih =>
    rw [Nat.add_right_comm]
    exact relatesInSteps.cons t t' c (k + m) h_red (ih h₂)

lemma relatesInSteps.succ {a b : α} {n : ℕ} (h : relatesInSteps r a b (n + 1)) :
    ∃ t', r a t' ∧ relatesInSteps r t' b n := by
  cases h with
  | cons _ t' _ _ h_red h_steps => exact ⟨t', h_red, h_steps⟩

lemma relatesInSteps.succ_iff {a b : α} {n : ℕ} :
    relatesInSteps r a b (n + 1) ↔ ∃ t', r a t' ∧ relatesInSteps r t' b n := by
  constructor
  · exact relatesInSteps.succ
  · rintro ⟨t', h_red, h_steps⟩
    exact relatesInSteps.cons a t' b n h_red h_steps

lemma relatesInSteps.succ' {a b : α} {n : ℕ} (h : relatesInSteps r a b (n + 1)) :
    ∃ t', relatesInSteps r a t' n ∧ r t' b := by
  induction n generalizing a b with
  | zero =>
    obtain ⟨t', h_red, h_steps⟩ := succ h
    rw [zero_iff] at h_steps
    subst h_steps
    exact ⟨a, relatesInSteps.refl a, h_red⟩
  | succ k ih =>
    obtain ⟨t', h_red, h_steps⟩ := succ h
    obtain ⟨t'', h_steps', h_red'⟩ := ih h_steps
    exact ⟨t'', relatesInSteps.cons a t' t'' k h_red h_steps', h_red'⟩

lemma relatesInSteps.succ'_iff {a b : α} {n : ℕ} :
    relatesInSteps r a b (n + 1) ↔ ∃ t', relatesInSteps r a t' n ∧ r t' b := by
  constructor
  · exact succ'
  · rintro ⟨t', h_steps, h_red⟩
    have h_succ := trans h_steps (cons t' b b 0 h_red (refl b))
    exact h_succ

/--
If `h : α → ℕ` increases by at most 1 on each step of `r`,
then the value of `h` at the output is at most `h` at the input plus the number of steps.
-/
lemma relatesInSteps.apply_le_apply_add {a b : α} (h : α → ℕ)
    (h_step : ∀ a b, r a b → h b ≤ h a + 1)
    (m : ℕ) (hevals : relatesInSteps r a b m) :
    h b ≤ h a + m := by
  induction hevals with
  | refl _ => simp
  | cons t t' t'' k h_red _ ih =>
    have h_step' := h_step t t' h_red
    omega

/--
If `g` is a homomorphism from `r` to `r'` (i.e., it preserves the reduction relation),
then `relatesInSteps` is preserved under `g`.
-/
lemma relatesInSteps.map {α α' : Type*}
    {r : α → α → Prop} {r' : α' → α' → Prop}
    (g : α → α') (hg : ∀ a b, r a b → r' (g a) (g b))
    {a b : α} {n : ℕ} (h : relatesInSteps r a b n) :
    relatesInSteps r' (g a) (g b) n := by
  induction h with
  | refl t => exact relatesInSteps.refl (g t)
  | cons t t' t'' m h_red h_steps ih =>
    exact relatesInSteps.cons (g t) (g t') (g t'') m (hg t t' h_red) ih

/--
`relatesWithinSteps` is a variant of `relatesInSteps` that allows for a loose bound.
It states that `a` relates to `b` in *at most* `n` steps.
-/
def relatesWithinSteps (r : α → α → Prop) (a b : α) (n : ℕ) : Prop :=
  ∃ m ≤ n, relatesInSteps r a b m

/-- `relatesInSteps` implies `relatesWithinSteps` with the same bound. -/
lemma relatesWithinSteps.of_relatesInSteps {a b : α} {n : ℕ} (h : relatesInSteps r a b n) :
    relatesWithinSteps r a b n :=
  ⟨n, Nat.le_refl n, h⟩

lemma relatesWithinSteps.refl (a : α) : relatesWithinSteps r a a 0 :=
  relatesWithinSteps.of_relatesInSteps (relatesInSteps.refl a)

lemma relatesWithinSteps.single {a b : α} (h : r a b) : relatesWithinSteps r a b 1 :=
  relatesWithinSteps.of_relatesInSteps (relatesInSteps.single h)

lemma relatesWithinSteps.zero {a b : α} (h : relatesWithinSteps r a b 0) : a = b := by
  obtain ⟨m, hm, hevals⟩ := h
  have : m = 0 := Nat.le_zero.mp hm
  subst this
  exact relatesInSteps.zero hevals

@[simp]
lemma relatesWithinSteps.zero_iff {a b : α} : relatesWithinSteps r a b 0 ↔ a = b := by
  constructor
  · exact relatesWithinSteps.zero
  · intro h
    subst h
    exact relatesWithinSteps.refl a

/-- Transitivity of `relatesWithinSteps` in the sum of the step bounds. -/
@[trans]
lemma relatesWithinSteps.trans {a b c : α} {n₁ n₂ : ℕ}
    (h₁ : relatesWithinSteps r a b n₁) (h₂ : relatesWithinSteps r b c n₂) :
    relatesWithinSteps r a c (n₁ + n₂) := by
  obtain ⟨m₁, hm₁, hevals₁⟩ := h₁
  obtain ⟨m₂, hm₂, hevals₂⟩ := h₂
  use m₁ + m₂
  constructor
  · omega
  · exact relatesInSteps.trans hevals₁ hevals₂

lemma relatesWithinSteps.of_le {a b : α} {n₁ n₂ : ℕ}
    (h : relatesWithinSteps r a b n₁) (hn : n₁ ≤ n₂) :
    relatesWithinSteps r a b n₂ := by
  obtain ⟨m, hm, hevals⟩ := h
  exact ⟨m, Nat.le_trans hm hn, hevals⟩

/-- If `h : α → ℕ` increases by at most 1 on each step of `r`,
then the value of `h` at the output is at most `h` at the input plus the step bound. -/
lemma relatesWithinSteps.apply_le_apply_add {a b : α} (h : α → ℕ)
    (h_step : ∀ a b, r a b → h b ≤ h a + 1)
    (n : ℕ) (hevals : relatesWithinSteps r a b n) :
    h b ≤ h a + n := by
  obtain ⟨m, hm, hevals_m⟩ := hevals
  have := relatesInSteps.apply_le_apply_add h h_step m hevals_m
  omega

/--
If `g` is a homomorphism from `r` to `r'` (i.e., it preserves the reduction relation),
then `relatesWithinSteps` is preserved under `g`.
-/
lemma relatesWithinSteps.map {α α' : Type*} {r : α → α → Prop} {r' : α' → α' → Prop}
    (g : α → α') (hg : ∀ a b, r a b → r' (g a) (g b))
    {a b : α} {n : ℕ} (h : relatesWithinSteps r a b n) :
    relatesWithinSteps r' (g a) (g b) n := by
  obtain ⟨m, hm, hevals⟩ := h
  exact ⟨m, hm, relatesInSteps.map g hg hevals⟩

end Steps

end Relation
