/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
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
parametric type of query operations.

## Main definitions

- `PureCosts`  : A typeclass that every model needs to log or cost pure monadic operations
- `Model Q` : A model type for a query type `Q : Type u → Type u`
- `Prog Q α` : The type of programs of query type `Q` and return type `α`. This is a free monad
      under the hood
- `eval`, `time` : concrete execution semantics of a `Prog Q α` for a given model of `Q`


## Important notes

This model is a lightweight framework for specifying and verifying both the correctness
and complexity of algorithms in lean. To specify an algorithm, one must:
1. Define an inductive type of queries which carries. This type must have one parameter `α` and
  one index type. The parameter type `α` is the return type of an
  which is the type supplied to the query and an index which denotes the output type of each query

2. C
## Tags

query model, free monad, time complexity, Prog
-/

namespace Cslib

namespace Algorithms

class PureCosts (α : Type u) where
  pureCost : α

scoped instance : PureCosts ℕ where
  pureCost := 1

structure Model (QType : Type u → Type u) (Cost : Type) [Add Cost] [Zero Cost]
  [PureCosts Cost] where
  evalQuery : QType ι → ι
  cost : QType ι → Cost

abbrev Prog Q α := FreeM Q α

instance {Q α} : Coe (Q α) (FreeM Q α) where
  coe := FreeM.lift
namespace Prog


def eval [Add Cost] [Zero Cost] [PureCosts Cost]
  (P : Prog Q α) (M : Model Q Cost) : α :=
  match P with
  | .pure x => x
  | .liftBind op cont  =>
      let qval := M.evalQuery op
      eval (cont qval) M

def time [Add Cost] [Zero Cost] [PureCosts Cost]
  (P : Prog Q α) (M : Model Q Cost) : Cost :=
  match P with
  | .pure _ => PureCosts.pureCost
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


-- The below lemma only holds if the cost of pure operations is zero. This
-- is however a footgun

-- -- This lemma is a sanity check. This is the only place `TimeM` is used.
-- lemma timing_is_identical : ∀ (P : Prog Q α) (M : Model Q ℕ),
--   time P M = (liftProgIntoTime M P).time := by
--   intro P pm
--   induction P with
--   | pure a =>
--       simp [time,liftProgIntoTime]
--   | liftBind op cont ih =>
--       expose_names
--       simp_all [time, liftProgIntoTime, interpretQueryIntoTime]

end TimeM



section Reduction

structure Reduction (Q Q' : Type u → Type u) where
  reduce : Q' α → Prog Q α




end Reduction



end Prog

end Algorithms

end Cslib
