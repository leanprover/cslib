/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Languages.Language
import Cslib.Foundations.Data.OmegaSequence.Flatten
import Mathlib.Computability.Language
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic

/-!
# ωLanguage

This file contains the definition and operations on formal ω-languages, which
are sets of infinite sequences over an alphabet `α` (namely, objects of type
`ωSequence α`).

## Main definitions and notations

In general we will use `p` and `q` to denote ω-languages and `l` and `m` to
denote languages (namely, sets of finite sequences of type `List α`).

* Set operations (union, intersection, complementation), constants (empty and
  universe sets), and the subset relation are denoted using lattice-theoretic
  notations (`p ∪ q`, `p ∩ q`, `pᶜ`, `⊥`, `⊤`, and `≤`) and terminologies in
  definition and theorem names ("meet", "join", "compl", "bot", "top", "le").
* `l * p`: ω-language of `x ++ω y` where `x ∈ l` and `y ∈ p`; referred to as
  "hmul" in definition and theorem names.
* `l^ω`: ω-language of infinite sequences each of which is the concatenation of
  infinitely many (nonemoty) members of `l`; referred to as "omegaPow" in
  definition and theorem names.
  + Note: Since `l^ω` is defined using `ωSequence.flatten`, any theorem about it
    needs the additional assumption `[Inhabited α]`.
* `l↗ω`: ω-language of infinite sequences each of which has infinitely many
  distinct prefixes in `l`; referred to as "omegaLim" in definition and theorem names.
* `p.map f`: transform an ω-language `p` over `α` into an ω-language over `β`
  by mapping through `f : α → β`; referred to as "map" in definition and theorem names.

## Main theorems

* Many algebraic properties of the above operations.
* omegaPow_seq_prop: an alternative characterization of `l^ω`.
* omegaPow_coind: a "coinductive" rule for proving `p` is a subset of `l^ω`.
* hmul_omegaPow_eq_omegaPow: `l * l^ω = l^ω`.
* kstar_omegaPow_eq_omegaPow: `(l∗)^ω = l^ω`.
* kstar_hmul_omegaPow_eq_omegaPow: `l∗ * l^ω = l^ω`.

## TODO

* Prove more theorems about omegaLim and map.
-/

namespace Cslib

open Set Filter ωSequence
open scoped Computability

universe v

variable {α β γ : Type _}

/-- An ω-language is a set of strings over an alphabet. -/
def ωLanguage (α) :=
  Set (ωSequence α)

namespace ωLanguage

instance instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (ωLanguage α) :=
  Set.instCompleteAtomicBooleanAlgebra

instance : Membership (ωSequence α) (ωLanguage α) := ⟨Set.Mem⟩
instance : Singleton (ωSequence α) (ωLanguage α) := ⟨Set.singleton⟩
instance : Insert (ωSequence α) (ωLanguage α) := ⟨Set.insert⟩
instance : HasSubset (ωLanguage α) := ⟨(· ≤ ·)⟩

variable {l m : Language α} {p q : ωLanguage α} {a b x : List α} {s t : ωSequence α}

instance : Inhabited (ωLanguage α) := ⟨(∅ : Set _)⟩

theorem le_def (p q : ωLanguage α) :
    p ≤ q ↔ (p : Set (ωSequence α)) ⊆ (q : Set (ωSequence α)) :=
  Iff.rfl

theorem bot_def : (⊥ : ωLanguage α) = (∅ : Set (ωSequence α)) :=
  rfl

theorem top_def : (⊤ : ωLanguage α) = (univ : Set (ωSequence α)) :=
  rfl

theorem join_def (p q : ωLanguage α) : p ⊔ q = (p ∪ q : Set (ωSequence α)) :=
  rfl

theorem meet_def (p q : ωLanguage α) : p ⊓ q = (p ∩ q : Set (ωSequence α)) :=
  rfl

theorem compl_def (p : ωLanguage α) : pᶜ = (pᶜ : Set (ωSequence α)) :=
  rfl

theorem iSup_def {ι : Sort v} {p : ι → ωLanguage α} :
    ⨆ i, p i = ⋃ i, p i :=
  rfl

theorem iInf_def {ι : Sort v} {p : ι → ωLanguage α} :
    ⨅ i, p i = ⋂ i, p i :=
  rfl

/-- The concatenation of a language l and an ω-language `p` is the ω-language made of
infinite sequences `x ++ω y` where `x ∈ l` and `y ∈ p`. -/
instance : HMul (Language α) (ωLanguage α) (ωLanguage α) :=
  ⟨image2 (· ++ω ·)⟩

theorem hmul_def (l : Language α) (p : ωLanguage α) : l * p = image2 (· ++ω ·) l p :=
  rfl

/-- Concatenation of infinitely many copies of a languages, resulting in an ω-language.
A.k.a. ω-power.
-/
def omegaPow [Inhabited α] (l : Language α) : ωLanguage α :=
  { s | ∃ xs : ωSequence (List α), xs.flatten = s ∧ ∀ k, xs k ∈ l \ 1 }

/-- Use the postfix notation ^ω` for `omegaPow`. -/
@[notation_class]
class OmegaPow (α : Type*) (β : outParam (Type*)) where
  omegaPow : α → β

postfix:1024 "^ω" => OmegaPow.omegaPow

instance [Inhabited α] : OmegaPow (Language α) (ωLanguage α) :=
  { omegaPow := omegaPow }

theorem omegaPow_def [Inhabited α] (l : Language α) :
    l^ω = { s | ∃ xs : ωSequence (List α), xs.flatten = s ∧ ∀ k, xs k ∈ l \ 1 }
  := rfl

/- The ω-limit of a language `l` is the ω-language of infinite sequences each of which
contains infinitely many distinct prefixes in `l`.
-/
def omegaLim (l : Language α) : ωLanguage α :=
  { s | ∃ᶠ m in atTop, s.extract 0 m ∈ l }

/-- Use the postfix notation ↗ω` for `omegaLim`. -/
@[notation_class]
class OmegaLim (α : Type*) (β : outParam (Type*)) where
  omegaLim : α → β

postfix:1024 "↗ω" => OmegaLim.omegaLim

instance instOmegaLim : OmegaLim (Language α) (ωLanguage α) :=
  { omegaLim := omegaLim }

theorem omegaLim_def (l : Language α) :
    l↗ω = { s | ∃ᶠ m in atTop, s.extract 0 m ∈ l } :=
  rfl

/-- transform an ω-language `p` over `α` into an ω-language over `β`
by mapping through `f : α → β`. -/
def map (f : α → β) : ωLanguage α → ωLanguage β := image (ωSequence.map f)

theorem map_def (f : α → β) (p : ωLanguage α) :
    p.map f = image (ωSequence.map f) p :=
  rfl

@[ext]
theorem ext (h : ∀ (s : ωSequence α), s ∈ p ↔ s ∈ q) : p = q :=
  Set.ext h

@[simp]
theorem mem_top (s : ωSequence α) : s ∈ (⊤ : ωLanguage α) := by
  trivial

@[simp]
theorem notMem_bot (s : ωSequence α) : s ∉ (⊥ : ωLanguage α) :=
  id

@[simp, scoped grind =]
theorem mem_join (p q : ωLanguage α) (s : ωSequence α) : s ∈ p ⊔ q ↔ s ∈ p ∨ s ∈ q :=
  Iff.rfl

@[simp, scoped grind =]
theorem mem_meet (p q : ωLanguage α) (s : ωSequence α) : s ∈ p ⊓ q ↔ s ∈ p ∧ s ∈ q :=
  Iff.rfl

@[simp, scoped grind =]
theorem mem_compl (p : ωLanguage α) (s : ωSequence α) : s ∈ pᶜ ↔ ¬ s ∈ p :=
  Iff.rfl

@[simp]
theorem mem_iSup {ι : Sort v} {p : ι → ωLanguage α} {s : ωSequence α} :
    (s ∈ ⨆ i, p i) ↔ ∃ i, s ∈ p i :=
  mem_iUnion

@[simp]
theorem mem_iInf {ι : Sort v} {p : ι → ωLanguage α} {s : ωSequence α} :
    (s ∈ ⨅ i, p i) ↔ ∀ i, s ∈ p i :=
  mem_iInter

@[simp, scoped grind =]
theorem mem_hmul : s ∈ l * p ↔ ∃ x ∈ l, ∃ t ∈ p, x ++ω t = s :=
  mem_image2

theorem append_mem_hmul : x ∈ l → s ∈ p → x ++ω s ∈ l * p :=
  mem_image2_of_mem

@[simp, scoped grind =]
theorem mem_omegaPow [Inhabited α] :
    s ∈ l^ω ↔ ∃ xs : ωSequence (List α), xs.flatten = s ∧ ∀ k, xs k ∈ l \ 1 :=
  Iff.rfl

theorem flatten_mem_omegaPow [Inhabited α] {xs : ωSequence (List α)}
    (h_xs : ∀ k, xs k ∈ l \ 1) : xs.flatten ∈ l^ω :=
  ⟨xs, rfl, h_xs⟩

theorem mul_hmul : (l * m) * p = l * (m * p) :=
  image2_assoc append_append_ωSequence

@[simp, scoped grind =]
theorem zero_hmul : (0 : Language α) * p = ⊥ :=
  image2_empty_left

@[simp, scoped grind =]
theorem hmul_bot : l * (⊥ : ωLanguage α) = ⊥ :=
  image2_empty_right

@[simp, scoped grind =]
theorem one_hmul : (1 : Language α) * p = p := by
  simp [hmul_def, Language.one_def]

theorem hmul_join : l * (p ⊔ q) = l * p ⊔ l * q :=
  image2_union_right

theorem add_hmul : (l + m) * p = l * p ⊔ m * p :=
  image2_union_left

theorem iSup_hmul {ι : Sort v} (l : ι → Language α) (p : ωLanguage α) :
    (⨆ i, l i) * p = ⨆ i, l i * p :=
  image2_iUnion_left _ _ _

theorem hmul_iSup {ι : Sort v} (p : ι → ωLanguage α) (l : Language α) :
    (l * ⨆ i, p i) = ⨆ i, l * p i :=
  image2_iUnion_right _ _ _

theorem le_hmul_congr {l1 l2 : Language α} {p1 p2 : ωLanguage α} :
    l1 ≤ l2 → p1 ≤ p2 → l1 * p1 ≤ l2 * p2 := by
  intro h_l h_p s h_s
  simp only [hmul_def, mem_image2] at h_s ⊢
  tauto

theorem le_omegaPow_congr [Inhabited α] {l1 l2 : Language α} :
    l1 ≤ l2 → l1^ω ≤ l2^ω := by
  rintro h s ⟨xs, rfl, h_xs⟩
  refine ⟨xs, rfl, ?_⟩
  intro k ; specialize h_xs k
  simp only [Language.mem_sdiff_one, ne_eq] at h_xs ⊢
  tauto

@[simp, scoped grind =]
theorem omegaPow_of_sdiff_one [Inhabited α] :
    (l \ 1)^ω = l^ω := by
  ext s ; simp

@[simp]
theorem zero_omegaPow [Inhabited α] :
    (0 : Language α)^ω = ⊥ := by
  ext s ; simp

@[simp]
theorem one_omegaPow [Inhabited α] :
    (1 : Language α)^ω = ⊥ := by
  rw [← omegaPow_of_sdiff_one, Language.one_sdiff_one, zero_omegaPow]

@[simp, scoped grind =]
theorem omegaPow_of_trivial [Inhabited α]
    (h : l.Trivial) : l^ω = ⊥ := by
  obtain (rfl | rfl) := Language.trivial_eq_zero_or_one h
  · exact zero_omegaPow
  · exact one_omegaPow

theorem omegaPow_eq_empty [Inhabited α]
    (h : l^ω = ⊥) : l.Trivial := by
  by_contra h_contra
  obtain ⟨x, h_x⟩ := nonempty_iff_ne_empty.mpr h_contra
  suffices h' : (const x).flatten ∈ l^ω by simp [h] at h'
  refine ⟨const x, rfl, ?_⟩ ; simpa

/-- An alternative characterization of `l * p`. -/
theorem hmul_seq_prop :
    l * p = { s | ∃ k, s.take k ∈ l ∧ s.drop k ∈ p } := by
  ext s ; constructor
  · rintro ⟨x, h_x, t, h_t, rfl⟩
    refine ⟨x.length, ?_, ?_⟩
    · simpa [take_append_of_le_length]
    · simpa [drop_append_ωSequence]
  · rintro ⟨k, h1, h2⟩
    refine ⟨s.take k, h1, s.drop k, h2, by simp⟩

/-- An alternative characterization of `l^ω`. -/
theorem omegaPow_seq_prop [Inhabited α] :
    l^ω = { s | ∃ f : ℕ → ℕ, StrictMono f ∧ f 0 = 0 ∧ ∀ m, s.extract (f m) (f (m + 1)) ∈ l } := by
  ext s ; constructor
  · rintro ⟨xs, rfl, h_xs⟩
    simp [forall_and, List.ne_nil_iff_length_pos] at h_xs
    refine ⟨xs.cumLen, by grind [cumLen_strictMono], by simp [cumLen_zero], ?_⟩
    grind
  · rintro ⟨f, hm, h0, he⟩
    refine ⟨(fun m ↦ s.extract (f m) (f (m + 1))), ?_, ?_⟩
    · apply strictMono_flatten hm h0
    · intro m
      suffices h : s.extract (f m) (f (m + 1)) ∈ l \ 1 by exact h
      simp only [he, Language.mem_sdiff_one, ne_eq, extract_eq_nil_iff, ge_iff_le, not_le, true_and]
      apply hm ; omega

open scoped Classical in
private noncomputable def iter_helper (p : ℕ → Prop) (f : (n : ℕ) → p n → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    let m := iter_helper p f n
    if h : p m then f m h else 0

theorem omegaPow_coind' [Inhabited α]
    (h_nn : [] ∉ l) (h_le : p ≤ l * p) : p ≤ l^ω := by
  intro s h_s
  rw [omegaPow_seq_prop]
  have h_nxt : ∀ m, s.drop m ∈ p → ∃ n > m, s.extract m n ∈ l ∧ s.drop n ∈ p := by
    intro m h_m
    obtain ⟨k, h1, h2⟩ := hmul_seq_prop ▸ h_le h_m
    refine ⟨m + k, ?_, ?_, ?_⟩
    · have : k = (take k (drop m s)).length := by grind
      have : 0 < k := by grind
      omega
    · simpa [extract_eq_drop_take]
    · simpa [← drop_drop]
  choose nxt_n nxt_p using h_nxt
  let f := iter_helper (fun n ↦ s.drop n ∈ p) nxt_n
  have h_f (n : ℕ) :
      f n < f (n + 1) ∧ s.extract (f n) (f (n + 1)) ∈ l ∧ s.drop (f (n + 1)) ∈ p := by
    induction n
    case zero => simp [f, iter_helper, h_s, nxt_p 0]
    case succ n h_ind =>
      have h1 : s.drop (f (n + 1)) ∈ p := by grind
      have h2 : f (n + 1 + 1) = nxt_n (f (n + 1)) h1 := by
        unfold f at h1 ⊢
        rw [iter_helper]
        simp [h1]
      grind
  refine ⟨f, ?_, by simp [f, iter_helper], by grind⟩
  apply strictMono_nat_of_lt_succ
  grind

/-- A "coinductive" rule for proving `p` is a subset of `l^ω`. -/
theorem omegaPow_coind [Inhabited α]
    (h_le : p ≤ (l \ 1) * p) : p ≤ l^ω := by
  rw [← omegaPow_of_sdiff_one]
  refine omegaPow_coind' ?_ h_le
  simp

theorem omegaPow_le_hmul_omegaPow' [Inhabited α] (l : Language α) :
    l^ω ≤ (l \ 1) * l^ω := by
  rintro s ⟨xs, rfl, h_xs⟩
  simp only [Language.mem_sdiff_one, ne_eq, forall_and, List.ne_nil_iff_length_pos] at h_xs
  refine ⟨xs.head, ?_, xs.tail.flatten, ⟨xs.tail, rfl, ?_⟩, by grind⟩
  · rw [Language.mem_sdiff_one]
    grind
  · simp only [ωSequence.get_tail, Language.mem_sdiff_one, ne_eq, List.ne_nil_iff_length_pos]
    grind

theorem omegaPow_le_hmul_omegaPow [Inhabited α] (l : Language α) :
    l^ω ≤ l * l^ω := by
  have h1 := omegaPow_le_hmul_omegaPow' l
  refine le_trans h1 ?_
  refine le_hmul_congr ?_ ?_
  · apply sdiff_le
  · apply le_refl

theorem hmul_omegaPow_le_omegaPow [Inhabited α] (l : Language α) :
    l * l^ω ≤ l^ω := by
  suffices h : l * l^ω ≤ (l \ 1) * (l * l^ω) by exact omegaPow_coind h
  rw [← mul_hmul, Language.sdiff_one_mul, mul_hmul]
  refine le_hmul_congr ?_ ?_
  · apply le_refl
  · apply omegaPow_le_hmul_omegaPow'

@[simp, scoped grind =]
theorem hmul_omegaPow_eq_omegaPow [Inhabited α] (l : Language α) :
    l * l^ω = l^ω := by
  apply le_antisymm
  · apply hmul_omegaPow_le_omegaPow
  · apply omegaPow_le_hmul_omegaPow

theorem omegaPow_le_kstar_omegaPow [Inhabited α] (l : Language α) :
    l^ω ≤ (l∗)^ω := by
  apply le_omegaPow_congr
  simp

theorem kstar_omegaPow_le_omegaPow [Inhabited α] (l : Language α) :
    (l∗)^ω ≤ l^ω := by
  suffices h : (l∗)^ω ≤ (l \ 1) * (l∗)^ω by exact omegaPow_coind h
  calc
    _ ≤ (l∗ \ 1) * (l∗)^ω := by apply omegaPow_le_hmul_omegaPow'
    _ = (l \ 1) * l∗ * (l∗)^ω := by simp
    _ = (l \ 1) * (l∗ * (l∗)^ω) := by rw [mul_hmul]
    _ = _ := by simp

@[simp, scoped grind =]
theorem kstar_omegaPow_eq_omegaPow [Inhabited α] (l : Language α) :
    (l∗)^ω = l^ω := by
  apply le_antisymm
  · apply kstar_omegaPow_le_omegaPow
  · apply omegaPow_le_kstar_omegaPow

@[simp, scoped grind =]
theorem kstar_hmul_omegaPow_eq_omegaPow [Inhabited α] (l : Language α) :
    l∗ * l^ω = l^ω := by
  calc
    _ = l∗ * (l∗)^ω := by simp
    _ = (l∗)^ω := by rw [hmul_omegaPow_eq_omegaPow]
    _ = _ := by simp

@[simp, scoped grind =]
theorem map_id (p : ωLanguage α) : map id p = p :=
  by simp [map]

@[scoped grind =]
theorem map_map (g : β → γ) (f : α → β) (p : ωLanguage α) : map g (map f p) = map (g ∘ f) p := by
  simp [map, image_image]

end ωLanguage

end Cslib
