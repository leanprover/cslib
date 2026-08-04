/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FastInstance

/-!
# Query Types for Comparison-Based Sorting in Lists

In this file we define two query types: `SortOpsInsertHead`, which is suitable for
insertion sort, and `SortOps`, which only supports comparisons. We define a model
`sortModel` for `SortOpsInsertHead` which uses a custom cost structure `SortOpsCost`, and
a model `sortModelNat` for `SortOps` which defines a `ℕ` based cost structure.
--
## Definitions

- `SortOpsInsertHead`: A query type for comparison based sorting in lists which includes
   queries for comparison and head-insertion into Lists. This is a suitable query type for
   ordered insertion and insertion sort.
- `SortOps`: A query type for comparison based sorting that only includes a comparison
   query. This is more suitable for comparison based sorts for which it is only desirable
   to count comparisons.

-/
@[expose] public section

namespace Cslib.Algorithms

open Prog

/--
A query type for comparison sorting on lists, with comparison and head-insertion queries.
-/
inductive SortOpsInsertHead (α : Type) : Type → Type  where
  /-- `cmpLE x y` is intended to return `true` if `x ≤ y` and `false` otherwise.
  The specific order relation depends on the model provided for this type. -/
  | cmpLE (x : α) (y : α) : SortOpsInsertHead α Bool
  /-- `insertHead l x` is intended to return `x :: l`. -/
  | insertHead (x : α) (l : List α) : SortOpsInsertHead α (List α)

open SortOpsInsertHead

section SortOpsCostModel

/--
A cost type for counting the operations of `SortOps` with separate fields for
counting calls to `cmpLE` and `insertHead`
-/
@[ext, grind]
structure SortOpsCost where
  /-- `compares` counts the number of calls to `cmpLE` -/
  compares : ℕ
  /-- `inserts` counts the number of calls to `insertHead` -/
  inserts : ℕ

/-- Equivalence between SortOpsCost and a product type. -/
def SortOpsCost.equivProd : SortOpsCost ≃ (ℕ × ℕ) where
  toFun sortOps := (sortOps.compares, sortOps.inserts)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace SortOpsCost

@[simps, grind]
instance : Zero SortOpsCost := ⟨0, 0⟩

@[simps]
instance : LE SortOpsCost where
  le soc₁ soc₂ := soc₁.compares ≤ soc₂.compares ∧ soc₁.inserts ≤ soc₂.inserts

instance : LT SortOpsCost where
  lt soc₁ soc₂ := soc₁ ≤ soc₂ ∧ ¬soc₂ ≤ soc₁

@[grind]
instance : PartialOrder SortOpsCost :=
  fast_instance% SortOpsCost.equivProd.injective.partialOrder _ .rfl .rfl

@[simps]
instance : Add SortOpsCost where
  add soc₁ soc₂ := ⟨soc₁.compares + soc₂.compares, soc₁.inserts + soc₂.inserts⟩

@[simps]
instance : SMul ℕ SortOpsCost where
  smul n soc := ⟨n • soc.compares, n • soc.inserts⟩

instance : AddCommMonoid SortOpsCost :=
  fast_instance%
    SortOpsCost.equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

end SortOpsCost

/--
A model of `SortOpsInsertHead` that uses `SortOpsCost` as the cost type for operations.

While this accepts any decidable relation `le`, most sorting algorithms are only well-behaved in the
presence of `[Std.Total le] [IsTrans _ le]`.
-/
@[simps, grind]
def sortModel {α : Type} (le : α → α → Bool) :
    Model (SortOpsInsertHead α) SortOpsCost where
  evalQuery
    | .cmpLE x y => le x y
    | .insertHead x l => x :: l
  cost
    | .cmpLE _ _ => ⟨1,0⟩
    | .insertHead _ _ => ⟨0,1⟩

@[simp]
lemma sortModel_evalQuery_cmpLE {α : Type} (le : α → α → Bool) (x y : α) :
    (sortModel le).evalQuery (cmpLE x y) = le x y := rfl

@[simp]
lemma sortModel_evalQuery_insertHead {α : Type} (le : α → α → Bool) (x : α) (l : List α) :
    (sortModel le).evalQuery (insertHead x l) = x :: l := rfl

@[simp]
lemma sortModel_cost_cmpLE {α : Type} (le : α → α → Bool) (x y : α) :
    (sortModel le).cost (cmpLE x y) = ⟨1, 0⟩ := rfl

@[simp]
lemma sortModel_cost_insertHead {α : Type} (le : α → α → Bool) (x : α) (l : List α) :
    (sortModel le).cost (insertHead x l) = ⟨0, 1⟩ := rfl

end SortOpsCostModel

section NatModel

/--
A query type for comparison sorting on lists with only the comparison operation.
This is used in mergeSort.
-/
inductive SortOps.{u} (α : Type u) : Type → Type _ where
  /-- `cmpLE x y` is intended to return `true` if `x ≤ y` and `false` otherwise.
  The specific order relation depends on the model provided for this type. -/
  | cmpLE (x : α) (y : α) : SortOps α Bool

/--
A model of `SortOps` that uses `ℕ` as the type for the cost of operations. In this model,
both comparisons and insertions are counted in a single `ℕ` parameter.

While this accepts any decidable relation `le`, most sorting algorithms are only well-behaved in the
presence of `[Std.Total le] [IsTrans _ le]`.
-/
@[simps]
def sortModelNat {α : Type*}
    (le : α → α → Bool) : Model (SortOps α) ℕ where
  evalQuery
    | .cmpLE x y => le x y
  cost _ := 1

@[simp]
lemma sortModelNat_evalQuery_cmpLE {α : Type*} (le : α → α → Bool) (x y : α) :
    (sortModelNat le).evalQuery (SortOps.cmpLE x y) = le x y := rfl

end NatModel

end Algorithms

end Cslib
