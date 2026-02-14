/-
Copyright (c) 2026 William (Liam) Schilling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William (Liam) Schilling
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Divisibility.Basic

@[expose] public section

namespace Semigroup

variable {α : Type*} [Semigroup α]

/-- Extract a witness of `a ∣ b`, that is, a result of left-dividing `b` by `a`. -/
noncomputable def divl (a b : α) (h : a ∣ b) : α :=
  Classical.choose h

/-- Multiplying `a` with a left-quotient of `b` by `a` yields `b`. -/
theorem divl_spec (a b : α) (h : a ∣ b) : b = a * divl a b h :=
  Classical.choose_spec h

end Semigroup
