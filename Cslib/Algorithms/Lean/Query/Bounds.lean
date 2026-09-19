/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Kim Morrison, Shreyas Srinivas
-/
module

public import Cslib.Algorithms.Lean.Query.FreeM
public import Mathlib.Order.Monotone.Defs

/-! # Upper and Lower Bounds for Query Complexity

Definitions of upper and lower bounds on the number of queries a program makes,
quantified over oracles.
-/

public section

namespace Cslib.Query

universe u v w

variable {α : Type w} {Q : Type u → Type v} {β : Type u}

/-- Upper bound: for all oracles, inputs of size ≤ n make at most `bound n` queries. -/
@[expose] def UpperBound (prog : α → FreeM Q β)
    (size : α → Nat) (bound : Nat → Nat) : Prop :=
  ∀ (oracle : {ι : Type u} → Q ι → ι) (n : Nat) (x : α),
    size x ≤ n → (prog x).countQueries oracle ≤ bound n

/-- Lower bound: for every size n, there exists an input of size at most n and an oracle
    making the program perform ≥ `bound n` queries. -/
@[expose] def LowerBound (prog : α → FreeM Q β)
    (size : α → Nat) (bound : Nat → Nat) : Prop :=
  ∀ (n : Nat), ∃ (x : α), size x ≤ n ∧
    ∃ (oracle : {ι : Type u} → Q ι → ι), bound n ≤ (prog x).countQueries oracle

/-- To prove an `UpperBound` with a monotone bound function, it suffices to bound the
    query count of each input by `bound` at its own size. -/
theorem UpperBound.of_pointwise {prog : α → FreeM Q β} {size : α → Nat} {bound : Nat → Nat}
    (hmono : Monotone bound)
    (h : ∀ (oracle : {ι : Type u} → Q ι → ι) (x : α),
      (prog x).countQueries oracle ≤ bound (size x)) :
    UpperBound prog size bound :=
  fun oracle _n x hx => (h oracle x).trans (hmono hx)

/-- A lower bound for a program never exceeds an upper bound for the same program and
    size function. -/
theorem LowerBound.le_upperBound {prog : α → FreeM Q β} {size : α → Nat} {l u : Nat → Nat}
    (hl : LowerBound prog size l) (hu : UpperBound prog size u) (n : Nat) : l n ≤ u n := by
  obtain ⟨x, hx, oracle, hbound⟩ := hl n
  exact hbound.trans (hu oracle n x hx)

end Cslib.Query
