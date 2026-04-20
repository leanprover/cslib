/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas, Eric Wieser
-/

module

public import Cslib.Foundations.Control.Monad.Free
public import Cslib.AlgorithmsTheory.Lean.TimeM

@[expose] public section

/-
# Query model

This file defines a simple query language modeled as a free monad over a
parametric type of query operations.

## Main definitions

- `Model Q c`: A model type for a query type `Q : Type u → Type u` and cost type `c`
- `Prog Q α`: The type of programs of query type `Q` and return type `α`.
  This is a free monad under the hood
- `Prog.eval`, `Prog.time`: concrete execution semantics of a `Prog Q α` for a given model of `Q`

## How to set up an algorithm

This model is a lightweight framework for specifying and verifying both the correctness
and complexity of algorithms in lean. To specify an algorithm, one must:
1. Define an inductive type of queries. This type must at least one index parameter
   which determines the output type of the query. Additionally, it helps to have a parameter `α`
   on which the index type depends. This way, any instance parameters of `α` can be used easily
   for the output types. The signatures of `Model.evalQuery` and `Model.cost` are fixed.
   So you can't supply instances for the index type there.
2. Define a record of the  `Model Q C` structure that specifies the evaluation and time (cost) of
   each query
3. Write your algorithm as a monadic program in `Prog Q α`. With sufficient type anotations
   each query `q : Q` is automatically lifted into `Prog Q α`.

## Tags
query model, free monad, time complexity, Prog
-/

namespace Cslib

namespace Algorithms

/--
A model type for a query type `QType` and cost type `Cost`. It consists of
two fields, which respectively define the evaluation and cost of a query.
-/
structure Model (QType : Type u → Type v) (Cost : Type w) where
  /-- Evaluates a query `q : Q ι` to return a result of type `ι`. -/
  evalQuery : QType ι → ι
  /-- Counts the operational cost of a query `q : Q ι` to return a result of type `Cost`.
  The cost could represent any desired complexity measure,
  including but not limited to time complexity. -/
  cost : QType ι → Cost


open Cslib.Algorithms.Lean in
/-- lift `Model.cost` to `TimeM Cost ι` -/
abbrev Model.timeQuery
    (M : Model Q Cost) (x : Q ι) : TimeM Cost ι :=
  TimeM.mk (M.evalQuery x) (M.cost x)

/--
A program is defined as a Free Monad over a Query type `Q` which operates on a base type `α`
which can determine the input and output types of a query.
-/
abbrev Prog Q α := FreeM Q α

/--
The evaluation function of a program `P : Prog Q α` given a model `M : Model Q α` of `Q`
-/
def Prog.eval
    (P : Prog Q α) (M : Model Q Cost) : α :=
  Id.run <| P.liftM fun x => pure (M.evalQuery x)

@[simp, grind =]
theorem Prog.eval_pure (a : α) (M : Model Q Cost) :
    Prog.eval (FreeM.pure a) M = a :=
  rfl

@[simp, grind =]
theorem Prog.eval_bind
    (x : Prog Q α) (f : α → Prog Q β) (M : Model Q Cost) :
    Prog.eval (FreeM.bind x f) M = Prog.eval (f (x.eval M)) M := by
  simp [Prog.eval]

@[simp, grind =]
theorem Prog.eval_liftBind
    (x : Q α) (f : α → Prog Q β) (M : Model Q Cost) :
    Prog.eval (FreeM.liftBind x f) M = Prog.eval (f <| M.evalQuery x) M := by
  simp [Prog.eval]

/--
The cost function of a program `P : Prog Q α` given a model `M : Model Q α` of `Q`.
The most common use case of this function is to compute time-complexity, hence the name.

In practice this is only well-behaved in the presence of `AddCommMonoid Cost`.
-/
def Prog.time [AddZero Cost]
    (P : Prog Q α) (M : Model Q Cost) : Cost :=
  (P.liftM M.timeQuery).time

@[simp, grind =]
lemma Prog.time_pure [AddZero Cost] (a : α) (M : Model Q Cost) :
    Prog.time (FreeM.pure a) M = 0 := by
  simp [time]

@[simp, grind =]
theorem Prog.time_liftBind [AddZero Cost]
    (x : Q α) (f : α → Prog Q β) (M : Model Q Cost) :
    Prog.time (FreeM.liftBind x f) M = M.cost x + Prog.time (f <| M.evalQuery x) M := by
  simp [Prog.time]

@[simp, grind =]
lemma Prog.time_bind [AddCommMonoid Cost] (M : Model Q Cost)
    (op : Prog Q ι) (cont : ι → Prog Q α) :
    Prog.time (op.bind cont) M =
      Prog.time op M + Prog.time (cont (Prog.eval op M)) M := by
  simp only [eval, time]
  induction op with
  | pure a =>
    simp
  | liftBind op cont' ih =>
    specialize ih (M.evalQuery op)
    simp_all [add_assoc]

section Reduction

/-- A reduction structure from query type `Q₁` to query type `Q₂`. -/
structure Reduction (Q₁ Q₂ : Type u → Type u) where
  /-- `reduce (q : Q₁ α)` is a program `P : Prog Q₂ α` that is intended to
  implement `q` in the query type `Q₂` -/
  reduce : Q₁ α → Prog Q₂ α

/--
`Prog.reduceProg` takes a reduction structure from a query `Q₁` to `Q₂` and extends its
`reduce` function to programs on the query type `Q₁`.
-/
abbrev Prog.reduceProg (P : Prog Q₁ α) (red : Reduction Q₁ Q₂) : Prog Q₂ α :=
  P.liftM red.reduce

end Reduction

end Cslib.Algorithms
