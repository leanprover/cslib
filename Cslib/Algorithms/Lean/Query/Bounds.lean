/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Kim Morrison, Shreyas Srinivas
-/
module

public import Cslib.Algorithms.Lean.Query.Prog

/-! # Upper and Lower Bounds for Query Complexity

Definitions of upper and lower bounds on the number of queries a program makes,
quantified over oracles.
-/

open Cslib.Query

public section

namespace Cslib.Query

/-- Upper bound: for all oracles, inputs of size ≤ n make at most `bound n` queries. -/
@[expose] def UpperBound (prog : α → Prog Q β)
    (size : α → Nat) (bound : Nat → Nat) : Prop :=
  ∀ (oracle : {ι : Type} → Q ι → ι) (n : Nat) (x : α),
    size x ≤ n → (prog x).queriesOn oracle ≤ bound n

/-- Lower bound: for every size n, there exists an input and oracle
    making the program perform ≥ `bound n` queries. -/
@[expose] def LowerBound (prog : α → Prog Q β)
    (size : α → Nat) (bound : Nat → Nat) : Prop :=
  ∀ (n : Nat), ∃ (x : α), size x ≤ n ∧
    ∃ (oracle : {ι : Type} → Q ι → ι), bound n ≤ (prog x).queriesOn oracle

end Cslib.Query

end -- public section
