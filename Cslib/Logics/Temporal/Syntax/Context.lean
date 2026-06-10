/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Syntax.Formula

/-!
# Context - Formula Lists for Proof Contexts

This module defines the Context type used to represent assumptions in derivations.

## Main Definitions

- `Context`: Type alias for `List (Formula Atom)`
- `Context.map`: Apply a transformation to all formulas in a context
- `Context.isEmpty`: Check if a context is empty
- `Context.singleton`: Create a context with a single formula

## Main Results

- Contexts inherit all list operations (membership, subset, append, etc.)
- Map operation preserves structural properties (length, composition)
- Map operation is equivalent to `List.map` for formulas

## Implementation Notes

- Context is simply `List (Formula Atom)`, leveraging Lean's built-in list operations
- Parameterized over a generic `Atom` type for composability
- The `map` operation is essential for temporal K inference rules
-/

@[expose] public section

namespace Cslib.Logic.Temporal

/--
Context type representing a list of formula assumptions.

Used in the derivability relation `Γ ⊢ φ` where `Γ` is a context of assumptions.
-/
abbrev Context (Atom : Type u) := List (Formula Atom)

namespace Context

variable {Atom : Type u}

/--
Apply a transformation to all formulas in a context.

This is used in inference rules like:
- Temporal K: If `Γ.map allFuture ⊢ φ` then `Γ ⊢ allFuture φ`
-/
def map (f : Formula Atom → Formula Atom) : Context Atom → Context Atom := List.map f

/-- Check if a context is empty. -/
def isEmpty : Context Atom → Bool
  | [] => true
  | _ :: _ => false

/-- Create a context containing a single formula. -/
def singleton (φ : Formula Atom) : Context Atom := [φ]

/-- Mapping a function over a context preserves length. -/
theorem map_length (f : Formula Atom → Formula Atom) (Γ : Context Atom) :
    (map f Γ).length = Γ.length := by
  simp [map]

/-- Mapping functions compose: `map f (map g Γ) = map (f ∘ g) Γ`. -/
theorem map_comp (f g : Formula Atom → Formula Atom) (Γ : Context Atom) :
    map f (map g Γ) = map (f ∘ g) Γ := by
  simp [map, List.map_map]

/-- Mapping the identity function leaves the context unchanged. -/
theorem map_id (Γ : Context Atom) : map id Γ = Γ := by
  simp [map]

/-- Mapping over an empty context yields an empty context. -/
theorem map_nil (f : Formula Atom → Formula Atom) : map f [] = [] := by
  rfl

/-- Mapping distributes over cons. -/
theorem map_cons (f : Formula Atom → Formula Atom) (φ : Formula Atom) (Γ : Context Atom) :
    map f (φ :: Γ) = f φ :: map f Γ := by
  rfl

/-- Mapping distributes over append. -/
theorem map_append (f : Formula Atom → Formula Atom) (Γ Δ : Context Atom) :
    map f (Γ ++ Δ) = map f Γ ++ map f Δ := by
  simp [map]

/-- Membership in mapped context comes from mapping a member. -/
theorem mem_map_iff {f : Formula Atom → Formula Atom} {Γ : Context Atom}
    {φ : Formula Atom} :
    φ ∈ map f Γ ↔ ∃ ψ ∈ Γ, f ψ = φ := by
  simp [map]

/-- If `ψ ∈ Γ`, then `f ψ ∈ map f Γ`. -/
theorem mem_map_of_mem {f : Formula Atom → Formula Atom} {Γ : Context Atom}
    {ψ : Formula Atom} (h : ψ ∈ Γ) : f ψ ∈ map f Γ := by
  rw [mem_map_iff]
  exact ⟨ψ, h, rfl⟩

/-- Empty context has no members. -/
theorem not_mem_nil (φ : Formula Atom) : φ ∉ ([] : Context Atom) := by
  simp

/-- Singleton context contains exactly one formula. -/
theorem mem_singleton_iff {φ ψ : Formula Atom} :
    φ ∈ singleton ψ ↔ φ = ψ := by
  simp [singleton]

/-- isEmpty is true iff the context equals []. -/
theorem isEmpty_iff_eq_nil (Γ : Context Atom) : isEmpty Γ = true ↔ Γ = [] := by
  cases Γ with
  | nil => simp [isEmpty]
  | cons _ _ => simp [isEmpty]

/-- A non-empty context has at least one element. -/
theorem exists_mem_of_ne_nil {Γ : Context Atom} (h : Γ ≠ []) :
    ∃ φ, φ ∈ Γ := by
  cases Γ with
  | nil => contradiction
  | cons φ _ => exact ⟨φ, List.mem_cons_self ..⟩

end Context

end Cslib.Logic.Temporal
