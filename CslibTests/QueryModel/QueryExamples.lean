/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.QueryModel
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# Additional examples of Query Types

This file contains two query types
- `ListOpsWithFind`
- `ArrayOpsWithFind`
which respectively provide query types for List and Array operations
equipped with a searching algorithm, and different models for them.
They are meant to be additional examples to guide authors of query types
-/
namespace Cslib

namespace Algorithms

section Examples

/--
ListOpsWithFind provides an example of list query type equipped with a `find` query.
The complexity of this query depends on the search algorithm used. This means
we can define two separate models for modelling situations where linear search
or binary search is used.
-/
inductive ListOpsWithFind (α : Type u) : Type u → Type _ where
  | get (l : List α) (i : Fin l.length) : ListOpsWithFind α α
  | find (l : List α) (elem : α) : ListOpsWithFind α (ULift ℕ)
  | write (l : List α) (i : Fin l.length) (x : α) : ListOpsWithFind α (List α)

/-- The typical means of evaluating a `ListOps`. -/
@[simp]
def ListOpsWithFind.eval [BEq α] : ListOpsWithFind α ι → ι
  | .write l i x => l.set i x
  | .find l elem => l.findIdx (· == elem)
  | .get l i => l[i]

/--
A model of `ListOpsWithFind` that assumes that `find` is implemented by a
linear search like `Θ(n)` algorithm.
-/
@[simps]
def ListOpsWithFind.linSearchWorstCase [DecidableEq α] : Model (ListOpsWithFind α) ℕ where
  evalQuery := ListOpsWithFind.eval
  cost
    | .write l _ _ => l.length
    | .find l _ =>  l.length
    | .get l _ => l.length

/--
A model of `ListOpsWithFind` that assumes that `find` is implemented by a
binary-search like `Θ(log n)` algorithm.
-/
@[simps]
def ListOps.binSearchWorstCase [BEq α] : Model (ListOpsWithFind α) ℕ where
  evalQuery := ListOpsWithFind.eval
  cost
    | .find l _ => 1 + Nat.log 2 (l.length)
    | .write l _ _ => l.length
    | .get l _ => l.length

/--
ArrayOpsWithFind is the `Array` version of `ListOpsWithFind`. It comes with
`get` and `write` queries, and additionally a `find` query which corresponds
to a search algorithm.
-/
inductive ArrayOpsWithFind (α : Type u) : Type u → Type _ where
  | get (l : Array α) (i : Fin l.size) : ArrayOpsWithFind α α
  | find (l : Array α) (x : α) : ArrayOpsWithFind α (ULift ℕ)
  | write (l : Array α) (i : Fin l.size) (x : α) : ArrayOpsWithFind α (Array α)

/-- The typical means of evaluating a `ListOps`. -/
@[simp]
def ArrayOpsWithFind.eval [BEq α] : ArrayOpsWithFind α ι → ι
  | .write l i x => l.set i x
  | .find l elem => l.findIdx (· == elem)
  | .get l i => l[i]

/--
A model of `ArrayOpsWithFind` that assumes that `find` is implemented by a
binary-search like `Θ(log n)` algorithm.
-/
@[simps]
def ArrayOpsWithFind.binSearchWorstCase [BEq α] : Model (ArrayOpsWithFind α) ℕ where
  evalQuery := ArrayOpsWithFind.eval
  cost
    | .find l _ => 1 + Nat.log 2 (l.size)
    | .write _ _ _ => 1
    | .get _ _ => 1

end Examples

end Algorithms

end Cslib
