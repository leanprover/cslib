/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Logic.Relation
public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Comparable
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

attribute [scoped grind] ReflGen TransGen ReflTransGen EqvGen CompRel

theorem ReflGen.to_eqvGen (h : ReflGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem TransGen.to_eqvGen (h : TransGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem ReflTransGen.to_eqvGen (h : ReflTransGen r a b) : EqvGen r a b := by
  induction h <;> grind

-- TODO: topNamespace environment linter fails for CompRel.to_eqvGen
@[nolint topNamespace]
theorem _root_.CompRel.to_eqvGen (h : CompRel r a b) : EqvGen r a b := by
  induction h <;> grind

attribute [scoped grind →] ReflGen.to_eqvGen TransGen.to_eqvGen ReflTransGen.to_eqvGen
  CompRel.to_eqvGen

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

lemma ReflGen.compRel_symm : ReflGen (CompRel r) a b → ReflGen (CompRel r) b a
| .refl => .refl
| .single (.inl h) => .single (.inr h)
| .single (.inr h) => .single (.inl h)

@[simp, grind =]
theorem reflTransGen_compRel : ReflTransGen (CompRel r) = EqvGen r := by
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
      rw [compRel_swap]
      exact reflTransGen_swap.mp ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

section Steps

variable {a b c : α}

/--
A relation `r` relates two elements of `α` in `n` steps
if there is a chain of `n` pairs `(t_i, t_{i+1})` such that `r t_i t_{i+1}` for each `i`,
starting from the first element and ending at the second.
-/
inductive RelatesInSteps (r : α → α → Prop) : α → α → ℕ → Prop
  | refl (a : α) : RelatesInSteps r a a 0
  | tail (t t' t'' : α) (n : ℕ) (h₁ : RelatesInSteps r t t' n) (h₂ : r t' t'') :
      RelatesInSteps r t t'' (n + 1)

theorem RelatesInSteps.reflTransGen (h : RelatesInSteps r a b n) : ReflTransGen r a b := by
  induction h with
  | refl => rfl
  | tail _ _ _ _ h ih => exact .tail ih h

theorem ReflTransGen.RelatesInSteps (h : ReflTransGen r a b) : ∃ n, RelatesInSteps r a b n := by
  induction h with
  | refl => exact ⟨0, .refl a⟩
  | tail _ _ ih =>
    obtain ⟨n, _⟩ := ih
    exact ⟨n + 1, by grind [RelatesInSteps]⟩

lemma RelatesInSteps.single {a b : α} (h : r a b) : RelatesInSteps r a b 1 :=
  tail a a b 0 (refl a) h

theorem RelatesInSteps.head (t t' t'' : α) (n : ℕ) (h₁ : r t t')
    (h₂ : RelatesInSteps r t' t'' n) : RelatesInSteps r t t'' (n+1) := by
  induction h₂ with
  | refl =>
    exact single h₁
  | tail _ _ n _ hcd hac =>
    exact tail _ _ _ (n + 1) hac hcd

@[elab_as_elim]
theorem RelatesInSteps.head_induction_on {motive : ∀ (a : α) (n : ℕ), RelatesInSteps r a b n → Prop}
    {a : α} {n : ℕ} (h : RelatesInSteps r a b n) (hrefl : motive b 0 (.refl b))
    (hhead : ∀ {a c n} (h' : r a c) (h : RelatesInSteps r c b n),
      motive c n h → motive a (n + 1) (h.head a c b n h')) :
    motive a n h := by
  induction h with
  | refl => exact hrefl
  | tail t' b' m hstep hrt'b' hstep_ih =>
    apply hstep_ih
    · exact hhead hrt'b' _ hrefl
    · exact fun h1 h2 ↦ hhead h1 (.tail _ t' b' _ h2 hrt'b')

lemma RelatesInSteps.zero {a b : α} (h : RelatesInSteps r a b 0) : a = b := by
  cases h
  rfl

@[simp]
lemma RelatesInSteps.zero_iff {a b : α} : RelatesInSteps r a b 0 ↔ a = b := by
  constructor
  · exact RelatesInSteps.zero
  · intro rfl
    exact RelatesInSteps.refl a

lemma RelatesInSteps.trans {a b c : α} {n m : ℕ}
    (h₁ : RelatesInSteps r a b n) (h₂ : RelatesInSteps r b c m) :
    RelatesInSteps r a c (n + m) := by
  induction h₂ generalizing a n with
  | refl => simp [h₁]
  | tail t' t'' k hsteps hstep ih =>
    rw [← Nat.add_assoc]
    exact .tail _ t' t'' (n + k) (ih h₁) hstep

lemma RelatesInSteps.succ {a b : α} {n : ℕ} (h : RelatesInSteps r a b (n + 1)) :
    ∃ t', RelatesInSteps r a t' n ∧ r t' b := by
  cases h with
  | tail t' _ _ hsteps hstep => exact ⟨t', hsteps, hstep⟩

lemma RelatesInSteps.succ_iff {a b : α} {n : ℕ} :
    RelatesInSteps r a b (n + 1) ↔ ∃ t', RelatesInSteps r a t' n ∧ r t' b := by
  constructor
  · exact RelatesInSteps.succ
  · rintro ⟨t', h_steps, h_red⟩
    exact .tail _ t' b n h_steps h_red

lemma RelatesInSteps.succ' {a b : α} : ∀ {n : ℕ}, RelatesInSteps r a b (n + 1) →
    ∃ t', r a t' ∧ RelatesInSteps r t' b n := by
  intro n h
  obtain ⟨t', hsteps, hstep⟩ := succ h
  cases n with
  | zero =>
    rw [zero_iff] at hsteps
    subst hsteps
    exact ⟨b, hstep, .refl _⟩
  | succ k' =>
    obtain ⟨t''', h_red''', h_steps'''⟩ := succ' hsteps
    exact ⟨t''', h_red''', .tail _ _ b k' h_steps''' hstep⟩

lemma RelatesInSteps.succ'_iff {a b : α} {n : ℕ} :
    RelatesInSteps r a b (n + 1) ↔ ∃ t', r a t' ∧ RelatesInSteps r t' b n := by
  constructor
  · exact succ'
  · rintro ⟨t', h_red, h_steps⟩
    exact h_steps.head a t' b n h_red

/--
If `h : α → ℕ` increases by at most 1 on each step of `r`,
then the value of `h` at the output is at most `h` at the input plus the number of steps.
-/
lemma RelatesInSteps.apply_le_apply_add {a b : α} (h : α → ℕ)
    (h_step : ∀ a b, r a b → h b ≤ h a + 1)
    (m : ℕ) (hevals : RelatesInSteps r a b m) :
    h b ≤ h a + m := by
  induction hevals with
  | refl => simp
  | tail t' t'' k _ hstep ih =>
    have h_step' := h_step t' t'' hstep
    lia

/--
If `g` is a homomorphism from `r` to `r'` (i.e., it preserves the reduction relation),
then `RelatesInSteps` is preserved under `g`.
-/
lemma RelatesInSteps.map {α α' : Type*}
    {r : α → α → Prop} {r' : α' → α' → Prop}
    (g : α → α') (hg : ∀ a b, r a b → r' (g a) (g b))
    {a b : α} {n : ℕ} (h : RelatesInSteps r a b n) :
    RelatesInSteps r' (g a) (g b) n := by
  induction h with
  | refl => exact RelatesInSteps.refl (g _)
  | tail t' t'' m _ hstep ih =>
    exact .tail (g _) (g t') (g t'') m ih (hg t' t'' hstep)

/--
`RelatesWithinSteps` is a variant of `RelatesInSteps` that allows for a loose bound.
It states that `a` relates to `b` in *at most* `n` steps.
-/
def RelatesWithinSteps (r : α → α → Prop) (a b : α) (n : ℕ) : Prop :=
  ∃ m ≤ n, RelatesInSteps r a b m

/-- `RelatesInSteps` implies `RelatesWithinSteps` with the same bound. -/
lemma RelatesWithinSteps.of_RelatesInSteps {a b : α} {n : ℕ} (h : RelatesInSteps r a b n) :
    RelatesWithinSteps r a b n :=
  ⟨n, Nat.le_refl n, h⟩

lemma RelatesWithinSteps.refl (a : α) : RelatesWithinSteps r a a 0 :=
  RelatesWithinSteps.of_RelatesInSteps (RelatesInSteps.refl a)

lemma RelatesWithinSteps.single {a b : α} (h : r a b) : RelatesWithinSteps r a b 1 :=
  RelatesWithinSteps.of_RelatesInSteps (RelatesInSteps.single h)

lemma RelatesWithinSteps.zero {a b : α} (h : RelatesWithinSteps r a b 0) : a = b := by
  obtain ⟨m, hm, hevals⟩ := h
  have : m = 0 := Nat.le_zero.mp hm
  subst this
  exact RelatesInSteps.zero hevals

@[simp]
lemma RelatesWithinSteps.zero_iff {a b : α} : RelatesWithinSteps r a b 0 ↔ a = b := by
  constructor
  · exact RelatesWithinSteps.zero
  · intro h
    subst h
    exact RelatesWithinSteps.refl a

/-- Transitivity of `RelatesWithinSteps` in the sum of the step bounds. -/
@[trans]
lemma RelatesWithinSteps.trans {a b c : α} {n₁ n₂ : ℕ}
    (h₁ : RelatesWithinSteps r a b n₁) (h₂ : RelatesWithinSteps r b c n₂) :
    RelatesWithinSteps r a c (n₁ + n₂) := by
  obtain ⟨m₁, hm₁, hevals₁⟩ := h₁
  obtain ⟨m₂, hm₂, hevals₂⟩ := h₂
  use m₁ + m₂
  constructor
  · lia
  · exact RelatesInSteps.trans hevals₁ hevals₂

lemma RelatesWithinSteps.of_le {a b : α} {n₁ n₂ : ℕ}
    (h : RelatesWithinSteps r a b n₁) (hn : n₁ ≤ n₂) :
    RelatesWithinSteps r a b n₂ := by
  obtain ⟨m, hm, hevals⟩ := h
  exact ⟨m, Nat.le_trans hm hn, hevals⟩

/-- If `h : α → ℕ` increases by at most 1 on each step of `r`,
then the value of `h` at the output is at most `h` at the input plus the step bound. -/
lemma RelatesWithinSteps.apply_le_apply_add {a b : α} (h : α → ℕ)
    (h_step : ∀ a b, r a b → h b ≤ h a + 1)
    (n : ℕ) (hevals : RelatesWithinSteps r a b n) :
    h b ≤ h a + n := by
  obtain ⟨m, hm, hevals_m⟩ := hevals
  have := RelatesInSteps.apply_le_apply_add h h_step m hevals_m
  lia

/--
If `g` is a homomorphism from `r` to `r'` (i.e., it preserves the reduction relation),
then `RelatesWithinSteps` is preserved under `g`.
-/
lemma RelatesWithinSteps.map {α α' : Type*} {r : α → α → Prop} {r' : α' → α' → Prop}
    (g : α → α') (hg : ∀ a b, r a b → r' (g a) (g b))
    {a b : α} {n : ℕ} (h : RelatesWithinSteps r a b n) :
    RelatesWithinSteps r' (g a) (g b) n := by
  obtain ⟨m, hm, hevals⟩ := h
  exact ⟨m, hm, RelatesInSteps.map g hg hevals⟩

end Steps

end Relation
