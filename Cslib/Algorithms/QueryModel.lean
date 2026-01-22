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

class Model (QType : Type u → Type u) where
  evalQuery : QType ι → ι
  cost : QType ι → ℕ

namespace Model

def interpretTimeM
  [M : Model Q] (q : Q ι) : TimeM ι where
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


def List_LinSearch_WorstCase [DecidableEq α] : Model (ListOps α) where
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



def List_BinSearch_WorstCase [BEq α] : Model (ListOps α) where
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

def Array_BinSearch_WorstCase [BEq α] : Model (ArrayOps α) where
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
namespace Prog

def eval (P : Prog Q α) (M : Model Q) : α :=
  match P with
  | .pure x => x
  | .liftBind op cont  =>
      let qval := M.evalQuery op
      eval (cont qval) M

def time (P : Prog Q α) (M : Model Q) : Nat :=
  match P with
  | .pure _ => 0
  | .liftBind op cont =>
      let t₁ := M.cost op
      let qval := M.evalQuery op
      t₁ + (time (cont qval) M)

def interpretQueryIntoTime (M : Model Q) (q : Q α) : TimeM α where
  ret := M.evalQuery q
  time := M.cost q
def interpretProgIntoTime (P : Prog Q α) (M : Model Q) : TimeM α where
  ret := eval P M
  time := time P M

def liftProgIntoTime (M : Model Q) (P : Prog Q α) : TimeM α :=
  P.liftM (interpretQueryIntoTime M)


-- This lemma is a sanity check. This is the only place `TimeM` is used.
lemma timing_is_identical : ∀ (P : Prog Q α) (M : Model Q),
  time P M = (liftProgIntoTime M P).time := by
  intro P pm
  induction P with
  | pure a =>
      simp [time,liftProgIntoTime]
  | liftBind op cont ih =>
      expose_names
      simp_all [time, liftProgIntoTime, interpretQueryIntoTime]

section ProgExamples

inductive Arith (α : Type) : Type → Type where
  | add (x y : α) : Arith α α
  | mul (x y : α) : Arith α α
  | neg (x : α) : Arith α α
  | zero : Arith α α
  | one : Arith α α

def RatArithQuery : Model (Arith ℚ) where
  evalQuery q :=
    match q with
    | .add x y => x + y
    | .mul x y => x * y
    | .neg x =>  -x
    | .zero => (0 : ℚ)
    | .one => (1 : ℚ)
  cost _ := 1

def add (x y : ℚ) : Prog (Arith ℚ) ℚ := FreeM.lift <| Arith.add x y
def mul (x y : ℚ) : Prog (Arith ℚ) ℚ := FreeM.lift <| Arith.mul x y
def neg (x : ℚ) : Prog (Arith ℚ) ℚ := FreeM.lift <| Arith.neg x
def zero : Prog (Arith ℚ) ℚ := FreeM.lift Arith.zero
def one : Prog (Arith ℚ) ℚ := FreeM.lift Arith.one

def ex1 : Prog (Arith ℚ) ℚ := do
  let mut x ← zero
  let mut y ← one
  let z ← add x y
  let w ← add z y
  add w z

#eval ex1.eval RatArithQuery

#eval ex1.time RatArithQuery

end ProgExamples

end Prog

end Algorithms

end Cslib
