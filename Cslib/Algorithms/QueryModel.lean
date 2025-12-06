/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Cslib.Foundations.Control.Monad.Free.Effects
import Cslib.Foundations.Control.Monad.Free.Fold
import Cslib.Foundations.Control.Monad.Time

/-
# Query model

This file defines a simple query language modeled as a free monad over primitive query operations.

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

/-- Primitive queries on natural-number registers. -/
inductive QueryF : Type → Type where
  /-- Read the value stored at index `i`. -/
  | read  : Nat → QueryF Nat
  /-- Write value `v` at index `i`. -/
  | write : Nat → Nat → QueryF PUnit
  /-- Compare the values at indices `i` and `j`. -/
  | cmp   : Nat → Nat → QueryF Bool

/-- Programs built as the free monad over `QueryF`. -/
abbrev Prog (α : Type) := FreeM QueryF α

namespace Prog

/-- Lift a comparison on values into the free monad. -/
def cmpVal (x y : Nat) : Prog Bool :=
  FreeM.lift (QueryF.cmp x y)

/-- Conditional branching on a boolean program. -/
def cond {α} (b : Prog Bool) (t e : Prog α) : Prog α :=
  b.bind (fun b' => if b' then t else e)

/-- A counting loop from `0` to `n - 1`, sequencing the body. -/
def forLoop (n : Nat) (body : Nat → Prog PUnit) : Prog PUnit :=
  go n
where
  /-- Auxiliary recursive worker for `forLoop`. -/
  go : Nat → Prog PUnit
    | 0       => pure ()
    | i + 1   =>
      body i >>= fun _ => go i

end Prog

/-- Constant time cost assigned to each primitive query. -/
def timeOfQuery : {ι : Type} → QueryF ι → Nat
  | _, .read _       => 1
  | _, .write _ _    => 1
  | _, .cmp _ _      => 1

/-- Interpret primitive queries into the time-counting monad `TimeM`. -/
def timeInterp : {ι : Type} → QueryF ι → TimeM ι
  | _, .read i      => TimeM.tick 0 (timeOfQuery (.read i))
  | _, .write i v   => TimeM.tick PUnit.unit (timeOfQuery (.write i v))
  | _, .cmp i j     => TimeM.tick false (timeOfQuery (.cmp i j))

/-- Total time cost of running a program under the interpreter `timeInterp`. -/
def timeProg {α : Type} (p : Prog α) : Nat :=
  (p.liftM timeInterp).time

/-- Lift a comparison into the query language at the top level. -/
def cmpVal (x y : Nat) : Prog Bool :=
  FreeM.lift (QueryF.cmp x y)

/-- Concrete semantics for primitive queries, used to run programs. -/
def evalQuery : {ι : Type} → QueryF ι → ι
  | _, .read _      => 0
  | _, .write _ _   => PUnit.unit
  | _, .cmp x y     => x ≤ y

/-- Evaluate a query program to a pure value using `evalQuery`. -/
def evalProg {α : Type} (p : Prog α) : α :=
  FreeM.foldFreeM id
    (fun {ι} (op : QueryF ι) (k : ι → α) =>
      k (evalQuery op))
    p

end Algorithms

end Cslib
