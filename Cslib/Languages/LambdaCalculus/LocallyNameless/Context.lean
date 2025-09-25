/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Foundations.Syntax.HasWellFormed
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Sigma

/-! # λ-calculus

Contexts as pairs of free variables and types.

-/

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α]

-- TODO: These are pieces of API that cannot be directly automated by adding `grind` attributes to
-- `Mathlib.Data.List.Sigma`. We should consider upstreaming them to Mathlib.
namespace List

variable {β : α → Type v} {Γ Δ : List (Sigma β)}

omit [DecidableEq α] in
/-- Keys distribute with appending. -/
theorem keys_append : (Δ ++ Γ).keys = Δ.keys ++ Γ.keys := by
  induction Δ <;> simp_all

/-- Sublists without duplicate keys preserve lookups. -/
theorem sublist_dlookup (l₁ l₂ : List (Sigma β)) (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys)
    (s : l₁ <+ l₂) (mem : b ∈ l₁.dlookup a) : b ∈ l₂.dlookup a := by
  induction s generalizing a b
  case slnil => exact mem
  case cons p' _ ih =>
    obtain ⟨a', b'⟩ := p'
    have := ih nd₁ (by grind [nodupKeys_cons]) mem |> of_mem_dlookup |> mem_keys_of_mem
    have : a ≠ a' := by grind [nodupKeys_cons]
    simp_all
  case cons₂ p' _ ih =>
    obtain ⟨a', b'⟩ := p'
    by_cases h : a = a'
    · subst h
      rw [List.dlookup_cons_eq] at *
      exact mem
    · simp_all

/-- List permutation preserves keys. -/
theorem perm_keys (h : Γ.Perm Δ) : x ∈ Γ.keys ↔ x ∈ Δ.keys := by
  induction h <;> grind [keys_cons]

/-- A key not appearing in an appending of list must not appear in either list. -/
theorem nmem_append_keys (l₁ l₂ : List (Sigma β)) :
    a ∉ (l₁ ++ l₂).keys ↔ a ∉ l₁.keys ∧ a ∉ l₂.keys := by
  constructor <;> (
    intro h
    induction l₂
    case nil => simp_all
    case cons hd tl ih =>
      have perm : (l₁ ++ hd :: tl).Perm (hd :: (l₁ ++ tl)) := by simp
      grind [keys_cons, => perm_keys]
  )

/-- An element between two appended lists without duplicate keys appears in neither list. -/
@[grind →]
theorem nodupKeys_of_nodupKeys_middle (l₁ l₂ : List (Sigma β)) (h : (l₁ ++ s :: l₂).NodupKeys) : 
    s.fst ∉ l₁.keys ∧ s.fst ∉ l₂.keys:= by
  have : (s :: (l₁ ++ l₂)).NodupKeys := by grind [perm_middle, perm_nodupKeys]
  grind [→ notMem_keys_of_nodupKeys_cons, nmem_append_keys]

end List

namespace LambdaCalculus.LocallyNameless

/-- A typing context is a list of free variables and corresponding types. -/
abbrev Context (α : Type u) (β : Type v) := List ((_ : α) × β)

namespace Context

open List

-- we would like grind to see through certain notations
attribute [scoped grind =] Option.mem_def
attribute [scoped grind _=_] List.append_eq
attribute [scoped grind =] List.Nodup
attribute [scoped grind =] List.NodupKeys
attribute [scoped grind _=_] List.singleton_append

-- a few grinds on Option:
attribute [scoped grind =] Option.or_eq_some_iff
attribute [scoped grind =] Option.or_eq_none_iff

-- we would like grind to treat list and finset membership the same
attribute [scoped grind _=_] List.mem_toFinset

-- otherwise, we mostly reuse existing API in `Mathlib.Data.List.Sigma`
attribute [scoped grind =] List.keys_cons
attribute [scoped grind =] List.dlookup_cons_eq
attribute [scoped grind =] List.dlookup_cons_ne
attribute [scoped grind =] List.dlookup_nil
attribute [scoped grind _=_] List.dlookup_isSome
attribute [scoped grind →] List.perm_nodupKeys

/-- The domain of a context is the finite set of free variables it uses. -/
@[simp, grind =]
def dom (Γ : Context α β) : Finset α := Γ.keys.toFinset

instance : HasWellFormed (Context α β) :=
  ⟨NodupKeys⟩

omit [DecidableEq α] in
@[scoped grind _=_]
theorem haswellformed_def (Γ : Context α β) : Γ✓ = Γ.NodupKeys := by rfl

variable {Γ Δ : Context α β}

omit [DecidableEq α] in
/-- Context well-formedness is preserved on removing an element. -/
@[scoped grind →]
theorem wf_strengthen (ok : (Δ ++ ⟨x, σ⟩ :: Γ)✓) : (Δ ++ Γ)✓ := by
  exact List.NodupKeys.sublist (by simp) ok

/-- A mapping of values within a context. -/
@[simp, scoped grind]
def map_val (f : β → β) (Γ : Context α β) : Context α β := 
  Γ.map (fun ⟨var,ty⟩ => ⟨var,f ty⟩)

omit [DecidableEq α] in
/-- A mapping of values preserves keys. -/
@[scoped grind]
lemma map_val_keys (f) : Γ.keys = (Γ.map_val f).keys := by
  induction Γ  <;> simp_all

omit [DecidableEq α] in
/-- A mapping of values preserves non-duplication of keys. -/
theorem map_val_ok (f : β → β) : Γ✓ ↔ (Γ.map_val f)✓ := by
  grind

/-- A mapping of values maps lookups. -/
lemma map_val_mem (mem : σ ∈ Γ.dlookup x) (f) : f σ ∈ (Γ.map_val f).dlookup x := by
  induction Γ <;> grind

/-- A mapping of values preserves non-lookups. -/
lemma map_val_nmem (nmem : Γ.dlookup x = none) (f) : (Γ.map_val f).dlookup x = none := by
  grind [List.dlookup_eq_none]

/-- A mapping of part of an appending of lists preseves non-duplicate keys. -/
lemma map_val_append_left (f) (ok : (Γ ++ Δ)✓) : (Γ.map_val f ++ Δ)✓ := by
  induction Δ
  case nil => grind
  case cons hd tl ih =>
    have perm : hd :: (map_val f Γ ++ tl) ~ map_val f Γ ++ hd :: tl := Perm.symm perm_middle
    have perm' : hd :: (Γ ++ tl) ~ Γ ++ hd :: tl := Perm.symm perm_middle
    have ok' : (hd :: (Γ ++ tl))✓ := by grind
    grind [List.nodupKeys_cons, nmem_append_keys]

end LambdaCalculus.LocallyNameless.Context
