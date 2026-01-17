/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Computability.Language

@[expose] public section

/-!
# Right RightCongruence

This file contains basic definitions about right congruences on finite sequences.

NOTE: Left congruences and two-sided congruences can be similarly defined.
But they are left to future work because they are not needed for now.
-/

namespace Cslib

/-- A right congruence is an equivalence relation on finite sequences (represented by lists)
that is preserved by concatenation on the right.  The equivalence relation is represented
by a setoid to to enable ready access to the quotient construction. -/
class RightCongruence (α : Type*) extends eq : Setoid (List α) where
  /-- If `u` an `v` are congruent, then `u ++ w` and `v ++ w` are also congruent for any `w`. -/
  right_congr {u v} (huv : u ≈ v) (w : List α) : u ++ w ≈ v ++ w

/-- The `≃` notation is supported for right congruences. -/
instance {α : Type*} [RightCongruence α] : HasEquiv (List α) :=
  ⟨RightCongruence.eq⟩

namespace RightCongruence

variable {α : Type*}

/-- The quotient type of a RightCongruence relation. -/
@[scoped grind =]
def QuotType (c : RightCongruence α) := Quotient c.eq

/-- The equivalence class (as a language) corresponding to an element of the quotient type. -/
@[scoped grind =]
def eqvCls [c : RightCongruence α] (s : c.QuotType) : Language α :=
  (Quotient.mk c.eq) ⁻¹' {s}

end RightCongruence

end Cslib
