/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

/-!
# Additional examples of Progs with Query Types

This file contains two query types and associated `Prog`s
- `Arith` with `ex1`
- `VectorSortOps` with `simpleExample`
- `VecSearch` with `linearSearch`
They are meant to be additional examples to guide authors to write
query types and programs on top of them
-/
namespace Cslib

namespace Algorithms

namespace Prog

section ProgExamples

inductive Arith (α : Type u) : Type u → Type _ where
  | add (x y : α) : Arith α α
  | mul (x y : α) : Arith α α
  | neg (x : α) : Arith α α
  | zero : Arith α α
  | one : Arith α α

def Arith.natCost [Ring α] : Model (Arith α) ℕ where
  evalQuery
    | .add x y => x + y
    | .mul x y => x * y
    | .neg x => -x
    | .zero => 0
    | .one => 1
  cost _ := 1

open Arith in
def ex1 : Prog (Arith α) α := do
  let mut x : α ← @zero α
  let mut y ← @one α
  let z ← (add x y)
  let w ← @neg α (← add z y)
  add w z

/-- The array version of the sort operations. -/
inductive VecSortOps.{u} (α : Type u) : Type u → Type _ where
  | swap (a : Vector α n) (i j : Fin n) : VecSortOps α (Vector α n)
  -- Note that we have to ULift the result to fit this in the same universe as the other types.
  -- We can avoid this only by forcing everything to be in `Type 0`.
  | cmp (a : Vector α n) (i j : Fin n) : VecSortOps α (ULift Bool)
  | write (a : Vector α n) (i : Fin n) (x : α) : VecSortOps α (Vector α n)
  | read (a : Vector α n) (i : Fin n) : VecSortOps α α
  | push (a : Vector α n) (elem : α) : VecSortOps α (Vector α (n + 1))

/-- The typical means of evaluating a `VecSortOps`. -/
@[simp]
def VecSortOps.eval [BEq α] : VecSortOps α β → β
  | .write v i x => v.set i x
  | .cmp l i j => .up <| l[i] == l[j]
  | .read l i => l[i]
  | .swap l i j => l.swap i j
  | .push a elem => a.push elem

@[simps]
def VecSortOps.worstCase [DecidableEq α] : Model (VecSortOps α) ℕ where
  evalQuery := VecSortOps.eval
  cost
    | .write _ _ _ => 1
    | .read _ _ => 1
    | .cmp _ _ _ => 1
    | .swap _ _ _ => 1
    | .push _ _ => 2 -- amortized over array insertion and resizing by doubling

@[simps]
def VecSortOps.cmpSwap [DecidableEq α] : Model (VecSortOps α) ℕ where
  evalQuery := VecSortOps.eval
  cost
    | .cmp _ _ _ => 1
    | .swap _ _ _ => 1
    | _ => 0

open VecSortOps in
def simpleExample (v : Vector ℤ n) (i k : Fin n) :
    Prog (VecSortOps ℤ) (Vector ℤ (n + 1)) :=  do
  let b : Vector ℤ n ← write v i 10
  let mut c : Vector ℤ n ← swap b i k
  let elem ← read c i
  push c elem

inductive VecSearch (α : Type u) : Type → Type _ where
  | compare (a : Vector α n) (i : ℕ) (val : α) : VecSearch α Bool

@[simps]
def VecSearch.nat [DecidableEq α] : Model (VecSearch α) ℕ where
  evalQuery
    | .compare l i x => l[i]? == some x
  cost
    | .compare _ _ _ => 1

open VecSearch in
def linearSearchAux (v : Vector α n)
    (x : α) (acc : Bool) (index : ℕ) : Prog (VecSearch α) Bool := do
  if h : index ≥ n then
    return acc
  else
    let cmp_res : Bool ← compare v index x
    if cmp_res then
      return true
    else
      linearSearchAux v x false (index + 1)

open VecSearch in
def linearSearch (v : Vector α n) (x : α) : Prog (VecSearch α) Bool:=
  linearSearchAux v x false 0

end ProgExamples

end Prog

end Algorithms

end Cslib
