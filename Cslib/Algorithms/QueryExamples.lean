/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.Algorithms.QueryModel


@[expose] public section

namespace Cslib

namespace Algorithms

section Examples

inductive ListOps (α : Type) : Type → Type  where
  | get (l : List α) (i : Fin l.length) : ListOps α α
  | find (l : List α) (elem : α) : ListOps α ℕ
  | write (l : List α) (i : Fin l.length) (x : α) : ListOps α (List α)


def List_LinSearch_WorstCase [DecidableEq α] : Model (ListOps α) ℕ where
  evalQuery
    | .write l i x => l.set i x
    | .find l elem =>  l.findIdx (· = elem)
    | .get l i => l[i]
  cost
    | .write l i x => l.length
    | .find l elem =>  l.length
    | .get l i => l.length



def List_BinSearch_WorstCase [BEq α] : Model (ListOps α) ℕ where
  evalQuery
    | .write l i x => l.set i x
    | .get l i => l[i]
    | .find l elem => l.findIdx (· == elem)

  cost
    | .find l _ => 1 + Nat.log 2 (l.length)
    | .write l i x => l.length
    | .get l x => l.length

inductive ArrayOps (α : Type) : Type → Type  where
  | get : (l : Array α) → (i : Fin l.size) → ArrayOps α α
  | find :  (l : Array α) → α → ArrayOps α ℕ
  | write : (l : Array α) → (i : Fin l.size) →  (x : α) → ArrayOps α (Array α)


def Array_BinSearch_WorstCase [BEq α] : Model (ArrayOps α) ℕ where
  evalQuery
    | .write l i x => l.set i x
    | .get l i => l[i]
    | .find l elem => l.findIdx (· == elem)

  cost
    | .find l _ => 1 + Nat.log 2 (l.size)
    | .write l i x => 1
    | .get l x => 1



end Examples

end Algorithms

end Cslib
