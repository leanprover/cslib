/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Syntax.HasWellFormed
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.List.Sigma


/-! # λ-calculus

Contexts as pairs of free variables and types.

-/

@[expose] public section

namespace Cslib

universe u v

variable {α : Type u} {β : Type v}

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
attribute [scoped grind _=_] List.singleton_append

-- a few grinds on Option:
attribute [scoped grind =] Option.or_eq_some_iff
attribute [scoped grind =] Option.or_eq_none_iff

-- we would like grind to treat list and finset membership the same
attribute [scoped grind _=_] List.mem_toFinset

-- otherwise, we mostly reuse existing API in `Mathlib.Data.List.Sigma`
attribute [scoped grind =] List.nodupKeys_middle
attribute [scoped grind →] List.perm_nodupKeys

/-- The domain of a context is the finite set of free variables it uses. -/
@[simp, grind =]
def dom (Γ : Context α β) : Finset α := Γ.keys.toFinset

instance : HasWellFormed (Context α β) :=
  ⟨NodupKeys⟩

omit [DecidableEq α] in
@[scoped grind _=_]
theorem haswellformed_def (Γ : Context α β) : Γ✓ = Γ.NodupKeys := by rfl

/-- A mapping of values within a context. -/
@[simp, scoped grind]
def mapVal (f : β → β) (Γ : Context α β) : Context α β :=
  Γ.map (fun ⟨var, ty⟩ => ⟨var, f ty⟩)

variable {Γ : Context α β} (f : β → β)

omit [DecidableEq α] in
/-- `mapVal` can be written as `List.map (Sigma.map id _)`. -/
lemma mapVal_def : Γ.mapVal f = Γ.map (Sigma.map id fun _ => f) := rfl

omit [DecidableEq α] in
/-- A mapping of values preserves keys. -/
@[scoped grind =]
lemma mapVal_keys : (Γ.mapVal f).keys = Γ.keys := by
  rw [mapVal_def, map₂_keys]

/-- Lookup commutes with a mapping of values. -/
@[scoped grind =]
lemma mapVal_dlookup (x : α) : (Γ.mapVal f).dlookup x = (Γ.dlookup x).map f := by
  rw [mapVal_def, dlookup_map₂]

/-- A mapping of values maps lookups. -/
lemma mapVal_mem {x : α} {σ : β} (mem : σ ∈ Γ.dlookup x) : f σ ∈ (Γ.mapVal f).dlookup x := by
  grind

omit [DecidableEq α] in
/-- A mapping of values preserves well-formedness. -/
lemma mapVal_wf (Γ_wf : Γ✓) : (Γ.mapVal f)✓ := by
  rw [haswellformed_def, mapVal_def]
  exact NodupKeys.map₂ _ Γ Γ_wf

end LambdaCalculus.LocallyNameless.Context

end Cslib
