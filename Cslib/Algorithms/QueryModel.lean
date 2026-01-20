/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Mathlib
public import Cslib.Foundations.Control.Monad.Free.Effects
public import Cslib.Foundations.Control.Monad.Free.Fold
public import Cslib.Foundations.Control.Monad.Time

/-
# Query model

This file defines a simple query language modeled as a free monad over a
parametric type of  query operations.

We equip this language with a cost model (`TimeM`) that counts how many primitive queries
are performed. An example algorithm (merge sort) is implemented in
`Cslib.Algorithms.MergeSort.QueryBased`.

## Main definitions

- `QueryF`, `Prog` : query language and programs
- `timeOfQuery`, `timeInterp`, `timeProg` : cost model for programs
- `evalQuery`, `evalProg` : concrete execution semantics

## Tags

query model, free monad, time complexity, merge sort
-/

namespace Cslib

namespace Algorithms

structure Model (QType : Type u → Type u) (ι o : Type u) where
  evalQuery : QType ι → ι → o
  cost : QType ι → ι → ℕ

namespace Model

def interpretTimeM
  (M : Model Q α β) (q : Q α) (inp : α) : TimeM β where
  ret := M.evalQuery q inp
  time := M.cost q inp


section Examples

inductive Search (α : Type*)  where
  | find (elem : α) (list : List α)

def LinSearch_WorstCase [DecidableEq α] : Model Search α ℕ  where
  evalQuery q :=
    match q with
    | .find elem list => List.findIdx (· = elem) list -- sorry we need a more general type
  cost q :=
    match q with
    | .find _ list => list.length



def BinSearch_WorstCase [BEq α] : Model Search α ℕ where
  evalQuery q :=
    match q with
    | .find elem list => List.findIdx (· == elem) list
  cost q :=
    match q with
    | .find _ l => 1 + Nat.log 2 l.length

inductive Arith α where
  | add (x y : α)
  | mul (x y : α)
  | neg (x : α)
  | zero
  | one

noncomputable def RealArithQuery : Model Arith ℝ ℝ where
  evalQuery q _ :=
    match q with
    | .add x y => x + y
    | .mul x y => x * y
    | .neg x =>  -x
    | .zero => (0 : ℝ)
    | .one => (1 : ℝ)
  cost _ := 1

end Examples

/-- Programs built as the free ~~monad~~ arrow? over `QueryF`. -/
inductive Prog (Q : Type u → Type v) : Type u → Type (max u v + 1) where
  | pure (q : Q α) : Prog Q α
  | seq (p₁ : Prog Q α) (cont : α → Prog Q β) : Prog Q β

namespace Prog

-- This is a problem. Only works for a uniform family of models
def eval (P : Prog Q α β) (modelFamily : ∀ i o, Model Q i o) : α :=
  match P with
  | .pure x => x
  | @FreeM.liftBind Q α ι q continuation =>
      let qval := evalQuery (modelFamily ι) q
      eval (continuation qval) modelFamily




end Prog

end Model

end Algorithms

end Cslib
