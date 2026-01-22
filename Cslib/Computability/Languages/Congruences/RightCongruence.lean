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
# Right Congruence

This file contains basic definitions about right congruences on finite sequences.

NOTE: Left congruences and two-sided congruences can be similarly defined.
But they are left to future work because they are not needed for now.
-/

namespace Cslib

/-- A right congruence is an equivalence relation on finite sequences (represented by lists)
that is preserved by concatenation on the right.  The equivalence relation is represented
by a setoid to to enable ready access to the quotient construction. -/
class RightCongruence (α : Type*) extends
  eq : Setoid (List α) , CovariantClass _ _ (fun x y => y ++ x) eq where

namespace RightCongruence

variable {α : Type*}

/-- The quotient type of a RightCongruence relation. -/
abbrev QuotType (α : Type*) [c : RightCongruence α] := Quotient c.eq

/-- The equivalence class (as a language) corresponding to an element of the quotient type. -/
abbrev eqvCls [c : RightCongruence α] (s : QuotType α) : Language α :=
  (Quotient.mk c.eq) ⁻¹' {s}

end RightCongruence

end Cslib
