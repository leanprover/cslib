/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.Language
public import Cslib.Foundations.Data.OmegaSequence.Flatten
public import Cslib.Foundations.Data.OmegaSequence.Topology
public import Mathlib.Computability.Language
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Filter.AtTopBot.Defs

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
  definition and theorem names ("inf", "sup", "compl", "bot", "top", "le").
* `p.closure`: the topological closure of `p`, where `ωLanguage α` inherits the
  product topology of `TopologicalSpace (ωSequence α)`
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

* Many algebraic and lattice-theoretic properties of the above operations.
* `omegaPow_seq_prop`: an alternative characterization of `l^ω`.
* `omegaPow_coind`: a "coinductive" rule for proving `p` is a subset of `l^ω`.
* `hmul_omegaPow_eq_omegaPow`: `l * l^ω = l^ω`.
* `kstar_omegaPow_eq_omegaPow`: `(l∗)^ω = l^ω`.
* `kstar_hmul_omegaPow_eq_omegaPow`: `l∗ * l^ω = l^ω`.
* `omegaLim_add`, `omegaLim_iSup_of_finite`, `omegaLim_sub_one`: union and empty-word properties
  of `l↗ω`.
* `hmul_omegaLim_le`, `omegaLim_mul_of_finite`, `omegaPow_le_omegaLim_kstar`: relationships between
  `l↗ω`, concatenation, and `l^ω`.
* `map_hmul`, `map_omegaPow`, `map_omegaLim_le`, `map_omegaLim_of_injective`: interaction of
  `p.map f` with concatenation, ω-power, and ω-limit.
-/

@[expose] public section

variable {α β γ : Type*}

-- This section is to be removed after mathlib#36934 is merged into mathlib.
section Mathlib_36934

/-- The set of lists in a language. -/
def Language.toSet (l : Language α) : Set (List α) := l

end Mathlib_36934

namespace Cslib

open Set Filter ωSequence
open scoped Computability

/-- An ω-language is a set of ω-sequences over an alphabet. -/
@[ext]
structure ωLanguage (α : Type u) where
  /-- Construct an ω-language from a set of ω-sequences. -/
  ofSet ::
  /-- The set of ω-sequences in an ω-language. -/
  toSet : Set (ωSequence α)
deriving Inhabited

instance : Coe (Set (ωSequence α)) (ωLanguage α) where
  coe f := ⟨f⟩

namespace ωLanguage

@[simp]
lemma ofSet_toSet (l : ωLanguage α) : ofSet l.toSet = l := rfl

lemma toSet_ofSet (s : Set (ωSequence α)) : (ofSet s).toSet = s := rfl

/-- The equivalence between `ωLanguage α` and `Set (ωSequence α)`. -/
def equiv : ωLanguage α ≃ Set (ωSequence α) where
  toFun := toSet
  invFun := ofSet

instance : CompleteAtomicBooleanAlgebra (ωLanguage α) :=
  equiv.completeAtomicBooleanAlgebra

/-- `⊥` is the only possible ω-language over an empty type. -/
theorem eq_bot_ofIsEmpty [IsEmpty α] (p : ωLanguage α) : p = ⊥ := by
  ext xs
  exfalso
  exact IsEmpty.false xs

set_option linter.tacticAnalysis.verifyGrindOnly false in
instance : SetLike (ωLanguage α) (ωSequence α) where
  coe := ωLanguage.toSet
  coe_injective := by grind only [Function.Injective, ωLanguage]

instance : HasSubset (ωLanguage α) := ⟨(· ≤ ·)⟩

variable {l m : Language α} {p q : ωLanguage α} {a b x : List α} {s t : ωSequence α}

lemma le_def (p q : ωLanguage α) : p ≤ q ↔ p.toSet ⊆ q.toSet := Iff.rfl

lemma top_def : (⊤ : ωLanguage α) = ⟨univ⟩ := rfl

lemma bot_def : (⊥ : ωLanguage α) = ⟨∅⟩ := rfl

lemma sup_def (p q : ωLanguage α) : p ⊔ q = ⟨p.toSet ∪ q.toSet⟩ := rfl

lemma inf_def (p q : ωLanguage α) : p ⊓ q = ⟨p.toSet ∩ q.toSet⟩ := rfl

lemma compl_def (p : ωLanguage α) : pᶜ = ⟨p.toSetᶜ⟩ := rfl

lemma sSup_def (s : Set (ωLanguage α)) : sSup s = ⟨⋃ p ∈ s, p.toSet⟩ := rfl

lemma sInf_def (s : Set (ωLanguage α)) : sInf s = ⟨⋂ p ∈ s, p.toSet⟩ := rfl

lemma iSup_def {ι : Sort v} {p : ι → ωLanguage α} : ⨆ i, p i = ⟨⋃ i, (p i).toSet⟩ := by
  ext
  simp [iSup, sSup_def]

lemma iInf_def {ι : Sort v} {p : ι → ωLanguage α} : ⨅ i, p i = ⟨⋂ i, (p i).toSet⟩ := by
  ext
  simp [iInf, sInf_def]

/-- The topological closure of an ω-language. -/
def closure (p : ωLanguage α) : ωLanguage α :=
  _root_.closure p.toSet

/-- The concatenation of a language l and an ω-language `p` is the ω-language made of
infinite sequences `x ++ω y` where `x ∈ l` and `y ∈ p`. -/
instance : HMul (Language α) (ωLanguage α) (ωLanguage α) where
  hMul l p := ⟨image2 (· ++ω ·) l.toSet p.toSet⟩

theorem hmul_def (l : Language α) (p : ωLanguage α) : l * p = image2 (· ++ω ·) l.toSet p.toSet :=
  rfl

/-- Concatenation of infinitely many copies of a languages, resulting in an ω-language.
A.k.a. ω-power.
-/
def omegaPow [Inhabited α] (l : Language α) : ωLanguage α :=
  { s | ∃ xs : ωSequence (List α), xs.flatten = s ∧ ∀ k, xs k ∈ l - 1 }

/-- Notation class for `omegaPow`. -/
@[notation_class]
class OmegaPow (α : Type*) (β : outParam (Type*)) where
  /-- The `omegaPow` operation. -/
  omegaPow : α → β

/-- Use the postfix notation ^ω` for `omegaPow`. -/
postfix:1024 "^ω" => OmegaPow.omegaPow

instance [Inhabited α] : OmegaPow (Language α) (ωLanguage α) :=
  ⟨omegaPow⟩

theorem omegaPow_def [Inhabited α] (l : Language α) :
    l^ω = { s | ∃ xs : ωSequence (List α), xs.flatten = s ∧ ∀ k, xs k ∈ l - 1 }
  := rfl

/-- The ω-limit of a language `l` is the ω-language of infinite sequences each of which
contains infinitely many distinct prefixes in `l`. -/
def omegaLim (l : Language α) : ωLanguage α :=
  { s : ωSequence α | ∃ᶠ m in atTop, s.extract 0 m ∈ l }

/-- Notation class for `omegaLim`. -/
@[notation_class]
class OmegaLim (α : Type*) (β : outParam (Type*)) where
  /-- The `omegaLim` operation. -/
  omegaLim : α → β

/-- Use the postfix notation ↗ω` for `omegaLim`. -/
postfix:1024 "↗ω" => OmegaLim.omegaLim

instance instOmegaLim : OmegaLim (Language α) (ωLanguage α) :=
  ⟨omegaLim⟩

theorem omegaLim_def (l : Language α) :
    l↗ω = { s : ωSequence α | ∃ᶠ m in atTop, s.extract 0 m ∈ l } :=
  rfl

/-- transform an ω-language `p` over `α` into an ω-language over `β`
by mapping through `f : α → β`. -/
def map (f : α → β) : ωLanguage α → ωLanguage β :=
  fun p ↦ image (ωSequence.map f) p.toSet

theorem map_def (f : α → β) (p : ωLanguage α) :
    p.map f = image (ωSequence.map f) p.toSet :=
  rfl

@[scoped grind =]
theorem mem_def (p : ωLanguage α) (s : ωSequence α) : s ∈ p ↔ s ∈ p.toSet :=
  Iff.rfl

theorem mem_ext (h : ∀ (s : ωSequence α), s ∈ p ↔ s ∈ q) : p = q := by
  apply ωLanguage.ext
  exact Set.ext h

@[simp]
theorem mem_top (s : ωSequence α) : s ∈ (⊤ : ωLanguage α) := by
  trivial

@[simp]
theorem notMem_bot (s : ωSequence α) : s ∉ (⊥ : ωLanguage α) :=
  id

@[simp, scoped grind =]
theorem mem_sup (p q : ωLanguage α) (s : ωSequence α) : s ∈ p ⊔ q ↔ s ∈ p ∨ s ∈ q :=
  Iff.rfl

@[simp, scoped grind =]
theorem mem_inf (p q : ωLanguage α) (s : ωSequence α) : s ∈ p ⊓ q ↔ s ∈ p ∧ s ∈ q :=
  Iff.rfl

@[simp, scoped grind =]
theorem mem_compl (p : ωLanguage α) (s : ωSequence α) : s ∈ pᶜ ↔ ¬ s ∈ p :=
  Iff.rfl

@[simp]
theorem mem_sSup (ps : Set (ωLanguage α)) {s : ωSequence α} :
    s ∈ sSup ps ↔ ∃ p ∈ ps, s ∈ p := by
  simp [sSup_def, mem_def]

@[simp]
theorem mem_sInf (ps : Set (ωLanguage α)) {s : ωSequence α} :
    s ∈ sInf ps ↔ ∀ p ∈ ps, s ∈ p := by
  simp [sInf_def, mem_def]

@[simp]
theorem mem_iSup {ι : Sort v} {p : ι → ωLanguage α} {s : ωSequence α} :
    (s ∈ ⨆ i, p i) ↔ ∃ i, s ∈ p i := by
  simp only [iSup_def]
  exact mem_iUnion

@[simp]
theorem mem_iInf {ι : Sort v} {p : ι → ωLanguage α} {s : ωSequence α} :
    (s ∈ ⨅ i, p i) ↔ ∀ i, s ∈ p i := by
  simp only [iInf_def]
  exact mem_iInter

@[simp, scoped grind =]
theorem mem_hmul : s ∈ l * p ↔ ∃ x ∈ l, ∃ t ∈ p, x ++ω t = s :=
  mem_image2

theorem append_mem_hmul : x ∈ l → s ∈ p → x ++ω s ∈ l * p :=
  mem_image2_of_mem

@[simp, scoped grind =]
theorem mem_omegaPow [Inhabited α] :
    s ∈ l^ω ↔ ∃ xs : ωSequence (List α), xs.flatten = s ∧ ∀ k, xs k ∈ l - 1 :=
  Iff.rfl

theorem flatten_mem_omegaPow [Inhabited α] {xs : ωSequence (List α)}
    (h_xs : ∀ k, xs k ∈ l - 1) : xs.flatten ∈ l^ω :=
  ⟨xs, rfl, h_xs⟩

@[simp, scoped grind =]
theorem mem_omegaLim :
    s ∈ l↗ω ↔ ∃ᶠ m in atTop, s.extract 0 m ∈ l :=
  Iff.rfl

theorem mul_hmul : (l * m) * p = l * (m * p) := by
  ext : 1
  exact image2_assoc append_append_ωSequence

@[simp, scoped grind =]
theorem zero_hmul : (0 : Language α) * p = ⊥ := by
  ext : 1
  exact image2_empty_left

@[simp, scoped grind =]
theorem hmul_bot : l * (⊥ : ωLanguage α) = ⊥ := by
  ext : 1
  exact image2_empty_right

@[simp, scoped grind =]
theorem one_hmul : (1 : Language α) * p = p := by
  simp [hmul_def]
  simp [Language.one_def, Language.toSet]

theorem hmul_sup : l * (p ⊔ q) = l * p ⊔ l * q := by
  ext : 1
  exact image2_union_right

theorem add_hmul : (l + m) * p = l * p ⊔ m * p := by
  ext : 1
  exact image2_union_left

theorem iSup_hmul {ι : Sort v} (l : ι → Language α) (p : ωLanguage α) :
    (⨆ i, l i) * p = ⨆ i, l i * p := by
  ext : 1
  simp only [hmul_def, iSup_def]
  apply image2_iUnion_left

theorem hmul_iSup {ι : Sort v} (p : ι → ωLanguage α) (l : Language α) :
    (l * ⨆ i, p i) = ⨆ i, l * p i := by
  ext : 1
  simp only [hmul_def, iSup_def]
  apply image2_iUnion_right

theorem le_hmul_congr {l1 l2 : Language α} {p1 p2 : ωLanguage α} (hl : l1 ≤ l2) (hp : p1 ≤ p2) :
    l1 * p1 ≤ l2 * p2 := by
  simp only [le_def]
  intros _
  simp only [hmul_def, mem_image2]
  tauto

theorem le_omegaPow_congr [Inhabited α] {l1 l2 : Language α} (h : l1 ≤ l2) : l1^ω ≤ l2^ω := by
  rintro s ⟨xs, rfl, h_xs⟩
  refine ⟨xs, rfl, ?_⟩
  intro k; specialize h_xs k
  simp only [Language.mem_sub_one, ne_eq] at h_xs ⊢
  tauto

@[simp, scoped grind =]
theorem omegaPow_of_sub_one [Inhabited α] : (l - 1)^ω = l^ω := by
  ext
  simp [omegaPow_def]

@[simp, nolint simpNF]
theorem zero_omegaPow [Inhabited α] : (0 : Language α)^ω = ⊥ := by
  ext
  simp [omegaPow_def, bot_def]

@[simp, nolint simpNF]
theorem one_omegaPow [Inhabited α] : (1 : Language α)^ω = ⊥ := by
  rw [← omegaPow_of_sub_one, tsub_self, zero_omegaPow]

@[simp, scoped grind =]
theorem omegaPow_of_le_one [Inhabited α] (h : l ≤ 1) : l^ω = ⊥ := by
  cases (Language.le_one_iff_eq.mp h) <;> simp_all

#adaptation_note
/-- A grind regression found moving to nightly-2026-03-31 (from lean#13166? seems different) -/
theorem omegaPow_eq_empty [Inhabited α] (h : l^ω = ⊥) : l ≤ 1 := by
  intro x h_x
  by_contra h_contra
  suffices h' : (const x).flatten ∈ l^ω by
    simp [h, mem_def, bot_def] at h'
  use const x, rfl
  exact fun _ => ⟨h_x, h_contra⟩

/-- An alternative characterization of `l * p`. -/
theorem hmul_seq_prop : l * p = { s : ωSequence α | ∃ k, s.take k ∈ l ∧ s.drop k ∈ p } := by
  ext s; constructor
  · rintro ⟨x, h_x, t, h_t, rfl⟩
    refine ⟨x.length, ?_, ?_⟩
    · simpa [take_append_of_le_length]
    · simpa [drop_append_ωSequence]
  · rintro ⟨k, h1, h2⟩
    exact ⟨s.take k, h1, s.drop k, h2, by simp⟩

/-- An alternative characterization of `l^ω`. -/
theorem omegaPow_seq_prop [Inhabited α] :
    l^ω = { s : ωSequence α |
      ∃ f : ℕ → ℕ, StrictMono f ∧ f 0 = 0 ∧ ∀ m, s.extract (f m) (f (m + 1)) ∈ l } := by
  ext s; constructor
  · rintro ⟨xs, rfl, h_xs⟩
    simp [forall_and, List.ne_nil_iff_length_pos] at h_xs
    refine ⟨xs.cumLen, by grind [cumLen_strictMono], by simp [cumLen_zero], ?_⟩
    grind
  · rintro ⟨f, hm, h0, he⟩
    refine ⟨(fun m ↦ s.extract (f m) (f (m + 1))), ?_, ?_⟩
    · apply strictMono_flatten hm h0
    · intro m
      change s.extract (f m) (f (m + 1)) ∈ l - 1
      simp only [he, Language.mem_sub_one, ne_eq, extract_eq_nil_iff, not_le, true_and]
      apply hm; omega

open scoped Classical in
private noncomputable def iter_helper (p : ℕ → Prop) (f : (n : ℕ) → p n → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    let m := iter_helper p f n
    if h : p m then f m h else 0

theorem omegaPow_coind' [Inhabited α] (h_nn : [] ∉ l) (h_le : p ≤ l * p) : p ≤ l^ω := by
  simp only [le_def]
  intro s h_s
  have h_nxt m (hm : s.drop m ∈ p) : ∃ n > m, s.extract m n ∈ l ∧ s.drop n ∈ p := by
    obtain ⟨k, _⟩ := hmul_seq_prop ▸ h_le hm
    grind [extract_eq_drop_take]
  choose nxt_n nxt_p using h_nxt
  let f := iter_helper (fun n ↦ s.drop n ∈ p) nxt_n
  have h_f (n) : f n < f (n + 1) ∧ s.extract (f n) (f (n + 1)) ∈ l ∧ s.drop (f (n + 1)) ∈ p := by
    induction n <;> grind [iter_helper]
  rw [omegaPow_seq_prop]
  use f
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-09-29 (changes from lean#15378) -/
  exact ⟨strictMono_nat_of_lt_succ fun n ↦ (h_f n).1, rfl, fun m ↦ (h_f m).2.1⟩

/-- A "coinductive" rule for proving `p` is a subset of `l^ω`. -/
theorem omegaPow_coind [Inhabited α] (h_le : p ≤ (l - 1) * p) : p ≤ l^ω := by
  rw [← omegaPow_of_sub_one]
  refine omegaPow_coind' ?_ h_le
  simp

#adaptation_note
/-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
theorem omegaPow_le_hmul_omegaPow' [Inhabited α] (l : Language α) :
    l^ω ≤ (l - 1) * l^ω := by
  rintro s ⟨xs, rfl, h_xs⟩
  refine ⟨xs.head, h_xs 0, xs.tail.flatten, ⟨xs.tail, rfl, ?_⟩, ?_⟩
  · grind
  · apply cons_flatten
    intro k
    apply List.length_pos_iff.mpr
    exact h_xs k |>.right

theorem omegaPow_le_hmul_omegaPow [Inhabited α] (l : Language α) : l^ω ≤ l * l^ω := by
  have h1 := omegaPow_le_hmul_omegaPow' l
  refine le_trans h1 ?_
  refine le_hmul_congr ?_ ?_
  · apply sdiff_le
  · apply le_refl

theorem hmul_omegaPow_le_omegaPow [Inhabited α] (l : Language α) : l * l^ω ≤ l^ω := by
  suffices h : l * l^ω ≤ (l - 1) * (l * l^ω) by exact omegaPow_coind h
  rw [← mul_hmul, Language.sub_one_mul, ← Language.mul_sub_one, mul_hmul]
  refine le_hmul_congr ?_ ?_
  · apply le_refl
  · apply omegaPow_le_hmul_omegaPow'

@[simp, scoped grind =]
theorem hmul_omegaPow_eq_omegaPow [Inhabited α] (l : Language α) : l * l^ω = l^ω := by
  apply le_antisymm
  · apply hmul_omegaPow_le_omegaPow
  · apply omegaPow_le_hmul_omegaPow

theorem omegaPow_le_kstar_omegaPow [Inhabited α] (l : Language α) : l^ω ≤ (l∗)^ω := by
  simp [le_omegaPow_congr]

theorem kstar_omegaPow_le_omegaPow [Inhabited α] (l : Language α) : (l∗)^ω ≤ l^ω := by
  suffices h : (l∗)^ω ≤ (l - 1) * (l∗)^ω by exact omegaPow_coind h
  calc
    _ ≤ (l∗ - 1) * (l∗)^ω := omegaPow_le_hmul_omegaPow' _
    _ = (l - 1) * l∗ * (l∗)^ω := by simp [Language.kstar_sub_one]
    _ = (l - 1) * (l∗ * (l∗)^ω) := mul_hmul
    _ = _ := by simp

@[simp, scoped grind =]
theorem kstar_omegaPow_eq_omegaPow [Inhabited α] (l : Language α) : (l∗)^ω = l^ω := by
  apply le_antisymm
  · apply kstar_omegaPow_le_omegaPow
  · apply omegaPow_le_kstar_omegaPow

@[simp, scoped grind =]
theorem kstar_hmul_omegaPow_eq_omegaPow [Inhabited α] (l : Language α) : l∗ * l^ω = l^ω := by
  calc
    _ = l∗ * (l∗)^ω := by simp
    _ = (l∗)^ω := by rw [hmul_omegaPow_eq_omegaPow]
    _ = _ := by simp

@[simp]
theorem omegaLim_zero : (0 : Language α)↗ω = ⊥ := by
  ext
  simp [omegaLim_def, bot_def]

/-- The ω-limit of `⊥` is empty. -/
@[simp]
theorem omegaLim_bot : (⊥ : Language α)↗ω = ⊥ :=
  omegaLim_zero

/-- The ω-limit of `1` (the language containing only the empty word) is empty. -/
@[simp, scoped grind =]
theorem omegaLim_one : (1 : Language α)↗ω = ⊥ := by
  apply mem_ext
  intro s
  simp only [mem_omegaLim, Language.mem_one, extract_eq_nil_iff, Nat.le_zero, notMem_bot,
    iff_false, not_frequently, eventually_atTop]
  exact ⟨1, fun m hm ↦ by omega⟩

/-- `omegaLim` is monotonic. -/
theorem omegaLim_mono {l₁ l₂ : Language α} (h : l₁ ≤ l₂) : l₁↗ω ≤ l₂↗ω :=
  fun _ hs ↦ hs.mono fun _ hm ↦ h hm

/-- If `l ≤ 1`, then the ω-limit of `l` is empty. -/
theorem omegaLim_eq_bot_of_le_one (h : l ≤ 1) : l↗ω = ⊥ :=
  le_bot_iff.mp ((omegaLim_mono h).trans_eq omegaLim_one)

/-- Removing the empty word from a language does not change its ω-limit. -/
@[simp, scoped grind =]
theorem omegaLim_sub_one (l : Language α) : (l - 1)↗ω = l↗ω := by
  apply mem_ext
  intro s
  simp only [mem_omegaLim]
  refine frequently_congr (eventually_atTop.mpr ⟨1, fun m hm ↦ ?_⟩)
  simp only [Language.mem_sub_one, ne_eq, extract_eq_nil_iff, Nat.le_zero, and_iff_left_iff_imp]
  omega

/-- `omegaLim` distributes over language addition (union). -/
@[simp, scoped grind =]
theorem omegaLim_add (l m : Language α) : (l + m)↗ω = l↗ω ⊔ m↗ω := by
  apply mem_ext
  intro s
  simp only [mem_omegaLim, Language.mem_add, mem_sup, frequently_or_distrib]

/-- `omegaLim` distributes over binary supremum. -/
@[simp]
theorem omegaLim_sup (l m : Language α) : (l ⊔ m)↗ω = l↗ω ⊔ m↗ω :=
  omegaLim_add l m

/-- The ω-limit of an intersection is contained in the intersection of the ω-limits. -/
theorem omegaLim_inf_le (l m : Language α) : (l ⊓ m)↗ω ≤ l↗ω ⊓ m↗ω :=
  le_inf (omegaLim_mono inf_le_left) (omegaLim_mono inf_le_right)

/-- The ω-limit of an indexed infimum is contained in the indexed infimum of the ω-limits. -/
theorem omegaLim_iInf_le {ι : Sort*} (l : ι → Language α) : (⨅ i, l i)↗ω ≤ ⨅ i, (l i)↗ω :=
  le_iInf fun i ↦ omegaLim_mono (iInf_le l i)

/-- The indexed supremum of ω-limits is contained in the ω-limit of the indexed supremum. -/
theorem iSup_omegaLim_le {ι : Sort*} (l : ι → Language α) : (⨆ i, (l i)↗ω) ≤ (⨆ i, l i)↗ω :=
  iSup_le fun i ↦ omegaLim_mono (le_iSup l i)

/-- `omegaLim` distributes over finite indexed suprema. -/
theorem omegaLim_iSup_of_finite {ι : Sort*} [Finite ι] (l : ι → Language α) :
    (⨆ i, l i)↗ω = ⨆ i, (l i)↗ω := by
  apply mem_ext
  intro s
  simp only [mem_omegaLim, Language.mem_iSup, mem_iSup, frequently_exists]

/-- Concatenating `l` with the ω-limit of `m` is contained in the ω-limit of `l * m`. -/
theorem hmul_omegaLim_le (l m : Language α) : l * m↗ω ≤ (l * m)↗ω := by
  rintro _ ⟨x, hx, t, ht, rfl⟩
  change t ∈ m↗ω at ht
  change x ++ω t ∈ (l * m)↗ω
  rw [mem_omegaLim, frequently_atTop] at ht ⊢
  intro N
  obtain ⟨k, _, hkm⟩ := ht N
  refine ⟨x.length + k, by omega, ?_⟩
  rw [extract_append_zero_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact Language.append_mem_mul hx hkm

/-- When `l` is finite, `(l * m)↗ω = l * m↗ω`. -/
theorem omegaLim_mul_of_finite {l m : Language α} (hl : l.toSet.Finite) :
    (l * m)↗ω = l * m↗ω := by
  have : Finite l.toSet := hl
  refine le_antisymm ?_ (hmul_omegaLim_le l m)
  intro s hs
  change s ∈ (l * m)↗ω at hs
  change s ∈ l * m↗ω
  have hs' : ∃ᶠ n in atTop, ∃ x : l.toSet, ∃ y ∈ m, x.1 ++ y = s.extract 0 n := by
    rw [mem_omegaLim] at hs
    refine hs.mono fun n hn ↦ ?_
    obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hn
    exact ⟨⟨x, hx⟩, y, hy, hxy⟩
  obtain ⟨⟨x, hx⟩, hx_freq⟩ := frequently_exists.mp hs'
  obtain ⟨n₀, hn₀, y₀, _, hxy₀⟩ := (frequently_atTop.mp hx_freq) x.length
  have htake : s.take x.length = x := by
    have h := congr_arg (List.take x.length) hxy₀
    simp only [List.take_left, extract_eq_take, take_take, min_eq_right hn₀] at h
    exact h.symm
  rw [hmul_seq_prop]
  refine ⟨x.length, htake.symm ▸ hx, ?_⟩
  rw [mem_omegaLim, frequently_atTop]
  intro N
  obtain ⟨n, hn, y, hy, hxy⟩ := (frequently_atTop.mp hx_freq) (x.length + N)
  refine ⟨n - x.length, by omega, ?_⟩
  have hdrop := congr_arg (List.drop x.length) hxy
  rw [List.drop_left, drop_extract (by simp only [Nat.sub_zero]; omega), Nat.zero_add] at hdrop
  rw [extract_drop, Nat.add_zero, Nat.add_sub_of_le (by omega), ← hdrop]
  exact hy

/-- The ω-power of a language `l` is contained in the ω-limit of its Kleene star `l∗`. -/
theorem omegaPow_le_omegaLim_kstar [Inhabited α] (l : Language α) : l^ω ≤ (l∗)↗ω := by
  intro s hs
  change s ∈ l^ω at hs
  change s ∈ (l∗)↗ω
  rw [omegaPow_seq_prop] at hs
  obtain ⟨f, hm, h0, hf⟩ := hs
  have hstar : ∀ k, s.extract 0 (f k) ∈ l∗ := by
    intro k
    induction k with
    | zero =>
      simp only [h0, extract_eq_nil]
      exact Language.nil_mem_kstar l
    | succ k ih =>
      rw [← append_extract_extract (Nat.zero_le _) (hm.monotone (Nat.le_succ k))]
      exact (kstar_mul_le_kstar : l∗ * l ≤ l∗) (Language.append_mem_mul ih (hf k))
  rw [mem_omegaLim, frequently_atTop]
  exact fun N ↦ ⟨f N, hm.id_le N, hstar N⟩

@[simp, scoped grind =]
theorem map_id (p : ωLanguage α) : map id p = p := by
  unfold map
  change { toSet := id '' p.toSet } = p
  simp

@[scoped grind =]
theorem map_map (g : β → γ) (f : α → β) (p : ωLanguage α) : map g (map f p) = map (g ∘ f) p := by
  simp [map, image_image]

private lemma map_extract (f : α → β) (s : ωSequence α) (m n : ℕ) :
    (s.map f).extract m n = (s.extract m n).map f := by
  simp only [extract_eq_drop_take, drop_map, map_take]

private lemma map_flatten [Inhabited α] [Inhabited β] (f : α → β) {xs : ωSequence (List α)}
    (hpos : ∀ k, 0 < (xs k).length) :
    xs.flatten.map f = (xs.map (List.map f)).flatten := by
  let ys := xs.map (List.map f)
  have hc : ys.cumLen = xs.cumLen := by
    ext k
    induction k with
    | zero => rfl
    | succ k ih => simp [ys, cumLen_succ, ih]
  have hys_pos : ∀ k, 0 < (ys k).length := fun k ↦ by simpa [ys] using hpos k
  ext i
  have hm := cumLen_strictMono hpos
  have hl := Nat.segment_lower_bound hm cumLen_zero i
  have hu := Nat.segment_upper_bound hm cumLen_zero i
  set n := Nat.segment xs.cumLen i
  have hk : i - xs.cumLen n < (xs n).length := by rw [cumLen_succ] at hu; omega
  have hi : i = xs.cumLen n + (i - xs.cumLen n) := by omega
  rw [hi, get_map, xs.flatten_get_add hk hpos]
  have hi' : xs.cumLen n + (i - xs.cumLen n) = ys.cumLen n + (i - xs.cumLen n) := by rw [hc]
  rw [hi', ys.flatten_get_add (by simpa [ys] using hk) hys_pos]
  simp [ys]

/-- An ω-sequence `t` belongs to `p.map f` iff `t = s.map f` for some `s ∈ p`. -/
@[simp, scoped grind =]
theorem mem_map {f : α → β} {p : ωLanguage α} {t : ωSequence β} :
    t ∈ p.map f ↔ ∃ s ∈ p, s.map f = t :=
  Iff.rfl

/-- Mapping a member of `p` through `f` produces a member of `p.map f`. -/
theorem map_mem_map {f : α → β} {p : ωLanguage α} {s : ωSequence α} (h : s ∈ p) :
    s.map f ∈ p.map f :=
  ⟨s, h, rfl⟩

/-- `ωLanguage.map f` is injective when `f` is injective. -/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (map f) := by
  have hf_seq : Function.Injective (ωSequence.map f) :=
    fun _ _ h ↦ ωSequence.ext fun n ↦ hf (congr_arg (· n) h)
  intro _ _ h
  ext : 1
  exact hf_seq.image_injective (congr_arg toSet h)

/-- Mapping the empty ω-language yields the empty ω-language. -/
@[simp, scoped grind =]
theorem map_bot (f : α → β) : (⊥ : ωLanguage α).map f = ⊥ := by
  ext : 1
  exact image_empty _

/-- `p.map f` is empty iff `p` is empty. -/
theorem map_eq_bot_iff {f : α → β} {p : ωLanguage α} : p.map f = ⊥ ↔ p = ⊥ := by
  simp only [ωLanguage.ext_iff, map_def, bot_def, image_eq_empty]

/-- Mapping `⊤` through a surjective function yields `⊤`. -/
theorem map_top_of_surjective {f : α → β} (hf : Function.Surjective f) :
    (⊤ : ωLanguage α).map f = ⊤ :=
  eq_top_iff.mpr fun t _ ↦
    ⟨t.map (Function.surjInv hf), mem_top _,
      ωSequence.ext fun n ↦ Function.surjInv_eq hf (t n)⟩

/-- `ωLanguage.map` is monotonic. -/
theorem map_mono {f : α → β} {p q : ωLanguage α} (h : p ≤ q) : p.map f ≤ q.map f :=
  image_mono h

/-- `ωLanguage.map` distributes over binary supremum. -/
@[simp]
theorem map_sup (f : α → β) (p q : ωLanguage α) : (p ⊔ q).map f = p.map f ⊔ q.map f := by
  ext : 1
  exact image_union _ _ _

/-- `ωLanguage.map` distributes over indexed supremum. -/
theorem map_iSup {ι : Sort*} (f : α → β) (p : ι → ωLanguage α) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f := by
  ext : 1
  simp only [map_def, iSup_def, image_iUnion]

/-- `ωLanguage.map` distributes over supremum of a set of ω-languages. -/
theorem map_sSup (f : α → β) (ps : Set (ωLanguage α)) :
    (sSup ps).map f = ⨆ p ∈ ps, p.map f := by
  ext : 1
  simp only [map_def, sSup_def, iSup_def, image_iUnion]

/-- Mapping an intersection is contained in the intersection of the mapped ω-languages. -/
theorem map_inf_le (f : α → β) (p q : ωLanguage α) : (p ⊓ q).map f ≤ p.map f ⊓ q.map f :=
  le_inf (map_mono inf_le_left) (map_mono inf_le_right)

/-- Mapping an indexed infimum is contained in the indexed infimum of the mapped ω-languages. -/
theorem map_iInf_le {ι : Sort*} (f : α → β) (p : ι → ωLanguage α) :
    (⨅ i, p i).map f ≤ ⨅ i, (p i).map f :=
  le_iInf fun i ↦ map_mono (iInf_le p i)

/-- When `f` is injective, `ωLanguage.map f` distributes over binary infimum. -/
theorem map_inf_of_injective {f : α → β} (hf : Function.Injective f) (p q : ωLanguage α) :
    (p ⊓ q).map f = p.map f ⊓ q.map f := by
  have hf_seq : Function.Injective (ωSequence.map f) :=
    fun _ _ h ↦ ωSequence.ext fun n ↦ hf (congr_arg (· n) h)
  ext : 1
  exact image_inter hf_seq

/-- When `f` is bijective, `ωLanguage.map f` commutes with complementation. -/
theorem map_compl_of_bijective {f : α → β} (hf : Function.Bijective f) (p : ωLanguage α) :
    pᶜ.map f = (p.map f)ᶜ := by
  have hf_seq : Function.Bijective (ωSequence.map f) :=
    ⟨fun _ _ h ↦ ωSequence.ext fun n ↦ hf.1 (congr_arg (· n) h),
      fun t ↦ ⟨t.map (Function.surjInv hf.2),
        ωSequence.ext fun n ↦ Function.surjInv_eq hf.2 (t n)⟩⟩
  ext : 1
  exact image_compl_eq hf_seq

/-- `ωLanguage.map` distributes over concatenation with a language. -/
theorem map_hmul (f : α → β) (l : Language α) (p : ωLanguage α) :
    (l * p).map f = l.map f * p.map f := by
  ext : 1
  exact image_image2_distrib (map_append_ωSequence f)

/-- `ωLanguage.map` commutes with ω-power. -/
theorem map_omegaPow [Inhabited α] [Inhabited β] (f : α → β) (l : Language α) :
    (l^ω).map f = (l.map f)^ω := by
  apply mem_ext
  intro t
  constructor
  · rintro ⟨_, ⟨xs, rfl, hxs⟩, rfl⟩
    have hpos : ∀ k, 0 < (xs k).length :=
      fun k ↦ List.length_pos_iff.mpr ((Language.mem_sub_one _).mp (hxs k)).2
    refine ⟨xs.map (List.map f), (map_flatten f hpos).symm, fun k ↦ ?_⟩
    obtain ⟨hx_mem, hx_ne⟩ := (Language.mem_sub_one _).mp (hxs k)
    exact (Language.mem_sub_one _).mpr ⟨⟨xs k, hx_mem, rfl⟩, by simpa using hx_ne⟩
  · rintro ⟨ys, rfl, hys⟩
    have hex : ∀ k, ∃ x, x ∈ l - 1 ∧ x.map f = ys k := by
      intro k
      obtain ⟨⟨x, hx_mem, hx_eq⟩, hy_ne⟩ := (Language.mem_sub_one _).mp (hys k)
      exact ⟨x, (Language.mem_sub_one _).mpr ⟨hx_mem, fun h ↦ hy_ne (by simp [← hx_eq, h])⟩, hx_eq⟩
    choose xs hxs_mem hxs_eq using hex
    let xs' : ωSequence (List α) := ⟨xs⟩
    have hpos : ∀ k, 0 < (xs' k).length :=
      fun k ↦ List.length_pos_iff.mpr ((Language.mem_sub_one _).mp (hxs_mem k)).2
    have hys_eq : ys = xs'.map (List.map f) := ωSequence.ext fun k ↦ (hxs_eq k).symm
    rw [hys_eq, ← map_flatten f hpos]
    exact ⟨xs'.flatten, ⟨xs', rfl, hxs_mem⟩, rfl⟩

/-- Mapping the ω-limit of `l` is contained in the ω-limit of `l.map f`. -/
theorem map_omegaLim_le (f : α → β) (l : Language α) : (l↗ω).map f ≤ (l.map f)↗ω := by
  rintro _ ⟨s, hs, rfl⟩
  exact hs.mono fun m hm ↦ ⟨s.extract 0 m, hm, (map_extract f s 0 m).symm⟩

/-- When `f` is injective, `ωLanguage.map f` commutes with `omegaLim`. -/
theorem map_omegaLim_of_injective {f : α → β} (hf : Function.Injective f) (l : Language α) :
    (l↗ω).map f = (l.map f)↗ω := by
  refine le_antisymm (map_omegaLim_le f l) ?_
  intro t ht
  have h_range : ∀ n, ∃ a, f a = t n := by
    intro n
    obtain ⟨m, hm, x, _, hx⟩ := (frequently_atTop.mp ht) (n + 1)
    have hlen : n < x.length := by
      have := congr_arg List.length hx
      simp only [List.length_map, length_extract, Nat.sub_zero] at this
      omega
    refine ⟨x[n], ?_⟩
    have hget := congr_arg (fun y : List β ↦ y[n]?) hx
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen, Option.map_some,
      extract_eq_take, getElem?_take (by omega : n < m)] at hget
    exact Option.some.inj hget
  choose s hs using h_range
  let s' : ωSequence α := ⟨s⟩
  have hmap : s'.map f = t := ωSequence.ext hs
  refine ⟨s', ?_, hmap⟩
  rw [← hmap] at ht
  refine ht.mono fun m ⟨x, hx_mem, hx_eq⟩ ↦ ?_
  rw [map_extract] at hx_eq
  rwa [← List.map_injective_iff.mpr hf hx_eq]

end ωLanguage

end Cslib
