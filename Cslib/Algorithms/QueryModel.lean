/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Mathlib
public import Cslib.Foundations.Control.Monad.Free.Effects
public import Cslib.Foundations.Control.Monad.Free.Fold
public import Batteries

@[expose] public section

/-
# Query model

This file defines a simple query language modeled as a free monad over a
parametric type of  query operations.

We equip this language with a cost model (`TimeM`) that counts how many primitive queries
are performed. An example algorithm (merge sort) is implemented in
`Cslib.Algorithms.MergeSort.QueryBased`.

## Main definitions

- `QueryF`, `Prog` : query language and programs
- `evalQuery`, `evalProg` : concrete execution semantics

## Tags

query model, free monad, time complexity, merge sort
-/

namespace Cslib

namespace Algorithms

structure Model (QType : Type u → Type u) (Cost : Type) [Add Cost] [Zero Cost] where
  evalQuery : QType ι → ι
  cost : QType ι → Cost

namespace Model

def interpretTimeM
  (M : Model Q ℕ) (q : Q ι) : TimeM ι where
  ret := M.evalQuery q
  time := M.cost q

-- inductive QueryF : Type → Type where
--   /-- Read the value stored at index `i`. -/
--   | read  : Nat → QueryF Nat
--   /-- Write value `v` at index `i`. -/
--   | write : Nat → Nat → QueryF PUnit
--   /-- Compare the values at indices `i` and `j`. -/
--   | cmp   : Nat → Nat → QueryF Bool

section Examples

inductive ListOps (α : Type) : Type → Type  where
  | get : (l : List α) → (i : Fin l.length) → ListOps α α
  | find :  (l : List α) → α → ListOps α ℕ
  | write : (l : List α) → (i : Fin l.length) →  (x : α) → ListOps α (List α)


def List_LinSearch_WorstCase [DecidableEq α] : Model (ListOps α) ℕ where
  evalQuery q :=
    match q with
    | .write l i x => l.set i x
    | .find l elem =>  l.findIdx (· = elem)
    | .get l i => l[i]
  cost q :=
    match q with
    | .write l i x => l.length
    | .find l elem =>  l.length
    | .get l i => l.length



def List_BinSearch_WorstCase [BEq α] : Model (ListOps α) ℕ where
  evalQuery q :=
    match q with
    | .write l i x => l.set i x
    | .get l i => l[i]
    | .find l elem => l.findIdx (· == elem)

  cost q :=
    match q with
    | .find l _ => 1 + Nat.log 2 (l.length)
    | .write l i x => l.length
    | .get l x => l.length

inductive ArrayOps (α : Type) : Type → Type  where
  | get : (l : Array α) → (i : Fin l.size) → ArrayOps α α
  | find :  (l : Array α) → α → ArrayOps α ℕ
  | write : (l : Array α) → (i : Fin l.size) →  (x : α) → ArrayOps α (Array α)

def Array_BinSearch_WorstCase [BEq α] : Model (ArrayOps α) ℕ where
  evalQuery q :=
    match q with
    | .write l i x => l.set i x
    | .get l i => l[i]
    | .find l elem => l.findIdx (· == elem)

  cost q :=
    match q with
    | .find l _ => 1 + Nat.log 2 (l.size)
    | .write l i x => 1
    | .get l x => 1



end Examples
end Model

-- ALternative def where pure has to be a query
-- /-- Programs built as the free ~~monad~~ arrow? over `QueryF`. -/
-- inductive Prog (Q : Type u → Type u) : Type u → Type (u + 1)  where
--   | pure (q : Q α) : Prog Q α
--   | seq (p₁ : Prog Q ι) (cont : ι → Prog Q α) : Prog Q α

abbrev Prog Q α := FreeM Q α

instance {Q α} : Coe (Q α) (FreeM Q α) where
  coe := FreeM.lift
namespace Prog


def eval [Add Cost] [Zero Cost]
  (P : Prog Q α) (M : Model Q Cost) : α :=
  match P with
  | .pure x => x
  | .liftBind op cont  =>
      let qval := M.evalQuery op
      eval (cont qval) M

def time [Add Cost] [Zero Cost] (P : Prog Q α) (M : Model Q Cost) : Cost :=
  match P with
  | .pure _ => 0
  | .liftBind op cont =>
      let t₁ := M.cost op
      let qval := M.evalQuery op
      t₁ + (time (cont qval) M)

section TimeM

-- The below is a proof of concept and pointless
def interpretQueryIntoTime (M : Model Q ℕ) (q : Q α) : TimeM α where
  ret := M.evalQuery q
  time := M.cost q
def interpretProgIntoTime (P : Prog Q α) (M : Model Q ℕ) : TimeM α where
  ret := eval P M
  time := time P M

def liftProgIntoTime (M : Model Q ℕ) (P : Prog Q α) : TimeM α :=
  P.liftM (interpretQueryIntoTime M)


-- This lemma is a sanity check. This is the only place `TimeM` is used.
lemma timing_is_identical : ∀ (P : Prog Q α) (M : Model Q ℕ),
  time P M = (liftProgIntoTime M P).time := by
  intro P pm
  induction P with
  | pure a =>
      simp [time,liftProgIntoTime]
  | liftBind op cont ih =>
      expose_names
      simp_all [time, liftProgIntoTime, interpretQueryIntoTime]

end TimeM

section ProgExamples

inductive Arith (α : Type) : Type → Type where
  | add (x y : α) : Arith α α
  | mul (x y : α) : Arith α α
  | neg (x : α) : Arith α α
  | zero : Arith α α
  | one : Arith α α

def RatArithQuery_NatCost : Model (Arith ℚ) ℕ where
  evalQuery q :=
    match q with
    | .add x y => x + y
    | .mul x y => x * y
    | .neg x =>  -x
    | .zero => (0 : ℚ)
    | .one => (1 : ℚ)
  cost _ := 1

structure AddMulCosts where
  addCount : ℕ
  mulCount : ℕ

instance : Zero (AddMulCosts) where
  zero := ⟨0,0⟩

instance : Add (AddMulCosts) where
    add x y :=
      let ⟨x_addcount, x_mulcount⟩ := x
      let ⟨y_addcount, y_mulcount⟩ := y
      ⟨x_addcount + y_addcount, x_mulcount + y_mulcount⟩

def RatArithQuery_AddMulCost : Model (Arith ℚ) AddMulCosts where
  evalQuery q :=
    match q with
    | .add x y => x + y
    | .mul x y => x * y
    | .neg x =>  -x
    | .zero => (0 : ℚ)
    | .one => (1 : ℚ)
  cost q :=
    match q with
    | .add _ _ => ⟨1,0⟩
    | .mul _ _ => ⟨0,1⟩
    | _ => 0

open Arith in
def ex1 : Prog (Arith ℚ) ℚ := do
  let mut x : ℚ ← @zero ℚ
  let mut y ← @one ℚ
  let z ← (add (x + y + y) y)
  let w ← @neg ℚ (←(add z y))
  add w z


--#eval ex1.eval RatArithQuery_NatCost
--#eval ex1.time RatArithQuery_NatCost
--#eval ex1.time RatArithQuery_AddMulCost

section ArraySort
/--
The array version of the sort operations
-/
inductive VecSortOps (α : Type) : Type → Type  where
  | swap : (a : Vector α n) → (i j : Fin n) → VecSortOps α (Vector α n)
  | cmp :  (a : Vector α n) → (i j : Fin n) → VecSortOps α Bool
  | write : (a : Vector α n) → (i : Fin n) → (x : α) → VecSortOps α (Vector α n)
  | read : (a : Vector α n) → (i : Fin n) → VecSortOps α α
  | push : (a : Vector α n) → (elem : α) → VecSortOps α (Vector α (n + 1))

def VecSort_WorstCase [DecidableEq α] : Model (VecSortOps α) ℕ where
  evalQuery q :=
    match q with
    | .write v i x => v.set i x
    | .cmp l i j =>  l[i] == l[j]
    | .read l i => l[i]
    | .swap l i j => l.swap i j
    | .push a elem => a.push elem

  cost q :=
    match q with
    | .write l i x => 1
    | .read l i =>  1
    | .cmp l i j => 1
    | .swap l i j => 1
    | .push a elem => 2 -- amortized over array insertion and resizing by doubling

def VecSort_CmpSwap [DecidableEq α] : Model (VecSortOps α) ℕ where
  evalQuery q :=
    match q with
    | .write v i x => v.set i x
    | .cmp l i j =>  l[i] == l[j]
    | .read l i => l[i]
    | .swap l i j => l.swap i j
    | .push a elem => a.push elem

  cost q :=
    match q with
    | .cmp l i j => 1
    | .swap l i j => 1
    | _ => 0


open VecSortOps in
def simpleExample (v : Vector ℤ n) (i k : Fin n)
  : Prog (VecSortOps ℤ) (Vector ℤ (n + 1)) :=  do
  let b : Vector ℤ n ← write v i 10
  let mut c : Vector ℤ n ← swap b i k
  let elem ← read c i
  push c elem

--#eval (simpleExample #v[1,2,3,4,5] 5 2).eval VecSort_WorstCase
--#eval (simpleExample #v[1,2,3,4,5] 5 2).time VecSort_WorstCase
--#eval (simpleExample #v[1,2,3,4,5] 5 2).time VecSort_CmpSwap

end ArraySort


end ProgExamples

end Prog

end Algorithms

end Cslib
