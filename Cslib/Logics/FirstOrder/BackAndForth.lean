/-
Copyright (c) 2026 Inacio F. Vasquez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Inacio F. Vasquez
-/

module

public import Cslib.Init
public import Mathlib.ModelTheory.Semantics

/-!
# First-order back-and-forth preservation

A back-and-forth relation preserving atomic formulas and supporting
extensions in both directions preserves all first-order formulas.

This is an unrestricted back-and-forth preservation theorem.
It does not construct a finite-round EF-game winning strategy.
-/

@[expose] public section

namespace Cslib.ModelTheory

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Structure

/-- A relation between valuations, preserving atoms and both quantified moves. -/
structure FormulaBackAndForth
    (L : FirstOrder.Language) (M N : Type*)
    [L.Structure M] [L.Structure N] (α : Type*) where
  Related : ∀ k : Nat, (α → M) → (Fin k → M) →
    (α → N) → (Fin k → N) → Prop
  preserves_equal :
    ∀ {k : Nat} {v : α → M} {xs : Fin k → M}
      {w : α → N} {ys : Fin k → N},
      Related k v xs w ys →
      ∀ t₁ t₂ : L.Term (α ⊕ Fin k),
        (t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)) ↔
          (t₁.realize (Sum.elim w ys) = t₂.realize (Sum.elim w ys))
  preserves_relation :
    ∀ {k ar : Nat} {v : α → M} {xs : Fin k → M}
      {w : α → N} {ys : Fin k → N},
      Related k v xs w ys →
      ∀ (r : L.Relations ar) (ts : Fin ar → L.Term (α ⊕ Fin k)),
        (RelMap r (fun i => (ts i).realize (Sum.elim v xs))) ↔
          (RelMap r (fun i => (ts i).realize (Sum.elim w ys)))
  forward :
    ∀ {k : Nat} {v : α → M} {xs : Fin k → M}
      {w : α → N} {ys : Fin k → N},
      Related k v xs w ys → ∀ x : M,
      ∃ y : N, Related (k + 1) v (Fin.snoc xs x) w (Fin.snoc ys y)
  backward :
    ∀ {k : Nat} {v : α → M} {xs : Fin k → M}
      {w : α → N} {ys : Fin k → N},
      Related k v xs w ys → ∀ y : N,
      ∃ x : M, Related (k + 1) v (Fin.snoc xs x) w (Fin.snoc ys y)

/-- All-arities back-and-forth preserves every first-order formula. -/
theorem FormulaBackAndForth.preserves_formula
    {L : FirstOrder.Language} {M N : Type*}
    [L.Structure M] [L.Structure N] {α : Type*}
    (F : FormulaBackAndForth L M N α) :
    ∀ {k : Nat} (φ : L.BoundedFormula α k)
      (v : α → M) (xs : Fin k → M)
      (w : α → N) (ys : Fin k → N),
      F.Related k v xs w ys →
        (φ.Realize v xs ↔ φ.Realize w ys) := by
  intro k φ
  induction φ with
  | falsum =>
      intro v xs w ys _
      exact Iff.rfl
  | equal t₁ t₂ =>
      intro v xs w ys h
      exact F.preserves_equal h t₁ t₂
  | rel r ts =>
      intro v xs w ys h
      exact F.preserves_relation h r ts
  | imp φ ψ ihφ ihψ =>
      intro v xs w ys h
      change (φ.Realize v xs → ψ.Realize v xs) ↔
        (φ.Realize w ys → ψ.Realize w ys)
      constructor
      · intro hp hφ
        exact (ihψ v xs w ys h).mp
          (hp ((ihφ v xs w ys h).mpr hφ))
      · intro hp hφ
        exact (ihψ v xs w ys h).mpr
          (hp ((ihφ v xs w ys h).mp hφ))
  | all φ ih =>
      intro v xs w ys h
      change (∀ x : M, φ.Realize v (Fin.snoc xs x)) ↔
        (∀ y : N, φ.Realize w (Fin.snoc ys y))
      constructor
      · intro hall y
        obtain ⟨x, hxy⟩ := F.backward h y
        exact (ih v (Fin.snoc xs x) w (Fin.snoc ys y) hxy).mp (hall x)
      · intro hall x
        obtain ⟨y, hxy⟩ := F.forward h x
        exact (ih v (Fin.snoc xs x) w (Fin.snoc ys y) hxy).mpr (hall y)


end ModelTheory
end Cslib
