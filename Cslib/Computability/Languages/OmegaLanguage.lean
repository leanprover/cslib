/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/
import Cslib.Foundations.Data.OmegaSequence.Init
import Mathlib.Computability.Language
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic

/-!
# ωLanguage

This file contains the definition and operations on formal ω-languages, which
are sets of infinite sequences over an alphabet `α`, namely, objects of type
`ωSequence α`.

## Notations

In general we will use `p` and `q` to denote ω-languages and `l` and `m` to
denote languages (namely, sets of finite sequences of type `List α`).

* `p ∪ q`, `p ∩ q`, `pᶜ`, `∅`: the usual set operations.
* `l * p`: ω-language of `x ++ω y` where `x ∈ l` and `y ∈ p`.
* `l ^ω`: ω-language of infinite sequences each of which is the concatenation of
  infinitely many (non-nil) members of `l`.
* `l ↗ω`: ω-language of infinite sequences each of which has infinitely many
  prefixes in `l`.

## Main definitions

* `ωLanguage α`: a set of infinite sequences over the alphabet `α`
* `p.map f`: transform an ω-language `p` over `α` into an ω-language over `β`
  by translating through `f : α → β`

## Main theorems

-/

namespace Cslib

open List Set Filter Computability

universe v

variable {α β γ : Type*}

/-- An ω-language is a set of strings over an alphabet. -/
def ωLanguage (α) :=
  Set (ωSequence α)

namespace ωLanguage

instance : Membership (ωSequence α) (ωLanguage α) := ⟨Set.Mem⟩
instance : Singleton (ωSequence α) (ωLanguage α) := ⟨Set.singleton⟩
instance : Insert (ωSequence α) (ωLanguage α) := ⟨Set.insert⟩
instance instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (ωLanguage α) :=
  Set.instCompleteAtomicBooleanAlgebra

variable {l m : Language α} {p q : ωLanguage α} {a b x : List α} {s t : ωSequence α}

instance : Inhabited (ωLanguage α) := ⟨(∅ : Set _)⟩

/-- ω-language ∅ has no elements. -/
instance : EmptyCollection (ωLanguage α) :=
  ⟨(∅ : Set _)⟩

theorem empty_def : (∅ : ωLanguage α) = (∅ : Set (ωSequence α)) :=
  rfl

/-- The union of two ω-languages. -/
instance : Union (ωLanguage α) :=
  ⟨((· ∪ ·) : Set (ωSequence α) → Set (ωSequence α) → Set (ωSequence α))⟩

theorem union_def (p q : ωLanguage α) : p ∪ q = (p ∪ q : Set (ωSequence α)) :=
  rfl

/-- The intersection of two ω-languages. -/
instance : Inter (ωLanguage α) :=
  ⟨((· ∩ ·) : Set (ωSequence α) → Set (ωSequence α) → Set (ωSequence α))⟩

theorem inter_def (p q : ωLanguage α) : p ∩ q = (p ∩ q : Set (ωSequence α)) :=
  rfl

theorem compl_def (p : ωLanguage α) : pᶜ = (pᶜ : Set (ωSequence α)) :=
  rfl

/-- The product of a language l and an ω-language `p` is the ω-language made of
infinite sequences `x ++ω y` where `x ∈ l` and `y ∈ p`. -/
instance : HMul (Language α) (ωLanguage α) (ωLanguage α) :=
  ⟨image2 (· ++ω ·)⟩

theorem hmul_def (l : Language α) (p : ωLanguage α) : l * p = image2 (· ++ω ·) l p :=
  rfl

/-- Concatenation of infinitely many copies of a languages, resulting in an ω-language.
A.k.a. ω-power.
-/
def omegaPower (l : Language α) : ωLanguage α :=
  { s | ∃ φ : ℕ → ℕ, StrictMono φ ∧ φ 0 = 0 ∧ ∀ m, s.extract (φ m) (φ (m + 1)) ∈ l }

/-- Use the postfix notation ^ω` for `omegaPower`. -/
@[notation_class]
class OmegaPower (α : Type*) (β : outParam (Type*)) where
  omegaPower : α → β

postfix:1024 "^ω" => OmegaPower.omegaPower

instance : OmegaPower (Language α) (ωLanguage α) :=
  { omegaPower := omegaPower }

theorem omegaPower_def (l : Language α) :
    l^ω = { s | ∃ φ : ℕ → ℕ, StrictMono φ ∧ φ 0 = 0 ∧ ∀ m, s.extract (φ m) (φ (m + 1)) ∈ l }
  := rfl

/- The ω-limit of a language `l` is the ω-language of infinite sequences each of which
contains infinitely many prefixes in `l`.
-/
def omegaLimit (l : Language α) : ωLanguage α :=
  { s | ∃ᶠ m in atTop, s.extract 0 m ∈ l }

/-- Use the postfix notation ↗ω` for `omegaLimit`. -/
@[notation_class]
class OmegaLimit (α : Type*) (β : outParam (Type*)) where
  omegaLimit : α → β

postfix:1024 "↗ω" => OmegaLimit.omegaLimit

instance instOmegaLimit : OmegaLimit (Language α) (ωLanguage α) :=
  { omegaLimit := omegaLimit }

theorem omegaLimit_def (l : Language α) :
    l↗ω = { s | ∃ᶠ m in atTop, s.extract 0 m ∈ l } :=
  rfl

def map (f : α → β) : ωLanguage α → ωLanguage β := image (ωSequence.map f)

theorem map_def (f : α → β) (p : ωLanguage α) :
    p.map f = image (ωSequence.map f) p :=
  rfl

@[ext]
theorem ext (h : ∀ (s : ωSequence α), s ∈ p ↔ s ∈ q) : p = q :=
  Set.ext h

@[simp]
theorem notMem_empty (s : ωSequence α) : s ∉ (∅ : ωLanguage α) :=
  id

@[simp]
theorem mem_union (p q : ωLanguage α) (s : ωSequence α) : s ∈ p ∪ q ↔ s ∈ p ∨ s ∈ q :=
  Iff.rfl

@[simp]
theorem mem_inter (p q : ωLanguage α) (s : ωSequence α) : s ∈ p ∩ q ↔ s ∈ p ∧ s ∈ q :=
  Iff.rfl

@[simp]
theorem mem_compl (p : ωLanguage α) (s : ωSequence α) : s ∈ pᶜ ↔ ¬ s ∈ p :=
  Iff.rfl

theorem mem_hmul : s ∈ l * p ↔ ∃ x ∈ l, ∃ t ∈ p, x ++ω t = s :=
  mem_image2

theorem append_mem_hmul : x ∈ l → s ∈ p → x ++ω s ∈ l * p :=
  mem_image2_of_mem

@[simp]
theorem map_id (p : ωLanguage α) : map id p = p :=
  by simp [map]

@[simp]
theorem map_map (g : β → γ) (f : α → β) (p : ωLanguage α) : map g (map f p) = map (g ∘ f) p := by
  simp [map, image_image]

end ωLanguage

end Cslib
