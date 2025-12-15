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



/-- Programs built as the free monad over `QueryF`. -/
abbrev Prog (QType : Type u → Type u) (α : Type v) := FreeM QType α


instance {QType : Type u → Type u} : Monad (Prog QType) := inferInstance




namespace Prog



/-- Conditional branching on a boolean program. -/
def cond {QType} {α} (b : Prog QType Bool) (t e : Prog QType α) : Prog QType α :=
  b.bind (fun b' => if b' then t else e)

/-- A counting loop from `0` to `n - 1`, sequencing the body. -/
def forLoop {QType} (n : Nat) (body : Nat → Prog QType PUnit) : Prog QType PUnit :=
  go n
where
  /-- Auxiliary recursive worker for `forLoop`. -/
  go : Nat → Prog QType PUnit
    | 0       => pure ()
    | i + 1   =>
      body i >>= fun _ => go i

end Prog

class Query (Q : Type u → Type u) where
  timeOfQuery : {ι : Type u} → Q ι → Nat
  evalQuery : {ι : Type u} → Q ι → ι

open Query
-- /-- Constant time cost assigned to each primitive query. -/
-- def timeOfQuery : {ι : Type} → QueryF ι → Nat
--   | _, .read _       => 1
--   | _, .write _ _    => 1
--   | _, .cmp _ _      => 1

/--
Interpret primitive queries into the time-counting monad `TimeM`.
-/
def timeInterp [Query QF] [Inhabited ι] (q : QF ι) : TimeM ι :=
  TimeM.tick default (timeOfQuery q)

-- /-- Interpret primitive queries into the time-counting monad `TimeM`. -/
-- def timeInterp : {ι : Type} → QueryF ι → TimeM ι
--   | _, .read i      => TimeM.tick 0 (timeOfQuery (.read i))
--   | _, .write i v   => TimeM.tick PUnit.unit (timeOfQuery (.write i v))
--   | _, .cmp i j     => TimeM.tick false (timeOfQuery (.cmp i j))


instance {α : Type u} {Q : Type u → Type u} [Query Q] : MonadLiftT (Prog Q) TimeM where
  monadLift (p : Prog Q α) : TimeM α :=
    timeInterp

/-- Total time cost of running a program under the interpreter `timeInterp`. -/
def timeProg [Query QF] {α : Type u}  (p : Prog QF α) : Nat :=
  (p.liftM timeInterp).time



/-- Evaluate a query program to a pure value using `evalQuery`. -/
def evalProg [Query QF] {α : Type} (p : Prog QF α) : α :=
  FreeM.foldFreeM id
    (fun {ι} (op : QF ι) (k : ι → α) =>
      k (evalQuery op))
    p

end Algorithms

end Cslib
