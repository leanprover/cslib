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

variable {α : Type u} {β : Type v}

-- TODO: These are pieces of API that cannot be directly automated by adding `grind` attributes to
-- `Mathlib.Data.List.Sigma`. We should consider upstreaming them to Mathlib.
namespace List

variable {β : α → Type v} {l₁ l₂ : List (Sigma β)}

/-- Keys distribute with appending. -/
theorem keys_append : (l₁ ++ l₂).keys = l₁.keys ++ l₂.keys := by
  simp [keys]

variable [DecidableEq α] in
/-- Sublists without duplicate keys preserve lookups. -/
theorem sublist_dlookup (nd₂ : l₂.NodupKeys) (s : l₁ <+ l₂) (mem : b ∈ l₁.dlookup a) : 
    b ∈ l₂.dlookup a := by
  grind [Option.mem_def, → perm_nodupKeys, dlookup_append, => perm_dlookup,
    → Sublist.exists_perm_append]

@[grind =]
lemma nodupKeys_middle : (l₁ ++ s :: l₂).NodupKeys ↔ (s :: (l₁ ++ l₂)).NodupKeys := by
  simp_all [NodupKeys, keys, nodup_middle]

end List

namespace LambdaCalculus.LocallyNameless

variable [DecidableEq α]

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
  grind [keys_append]

/-- A mapping of values within a context. -/
@[simp, scoped grind]
def map_val (f : β → β) (Γ : Context α β) : Context α β := 
  Γ.map (fun ⟨var,ty⟩ => ⟨var,f ty⟩)

omit [DecidableEq α] in
/-- A mapping of values preserves keys. -/
@[scoped grind]
lemma map_val_keys (f) : Γ.keys = (Γ.map_val f).keys := by
  induction Γ <;> grind

/-- A mapping of values maps lookups. -/
lemma map_val_mem (mem : σ ∈ Γ.dlookup x) (f) : f σ ∈ (Γ.map_val f).dlookup x := by
  induction Γ <;> grind

end LambdaCalculus.LocallyNameless.Context
