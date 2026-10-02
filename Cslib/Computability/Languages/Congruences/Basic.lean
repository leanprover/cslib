/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Computability.Language

/-!
# Right Congruence

This file contains basic definitions about left, right, and (two-sided) congruences
on finite sequences.
-/

@[expose] public section

namespace Language

variable {α : Type*}

/-- A right congruence is an equivalence relation on finite sequences (represented by lists)
that is preserved by concatenation on the right.  The equivalence relation is represented
by a setoid to to enable ready access to the quotient construction. -/
class RightCongruence (α : Type*) extends eq : Setoid (List α) where
  right_cov : CovariantClass _ _ (fun x y => y ++ x) eq

namespace RightCongruence

/-- The equivalence class (as a language) corresponding to an element of the quotient type. -/
abbrev eqvCls [c : RightCongruence α] (a : Quotient c.eq) : Language α :=
  (Quotient.mk c.eq) ⁻¹' {a}

end RightCongruence

/-- A left congruence is an equivalence relation on finite sequences (represented by lists)
that is preserved by concatenation on the left.  The equivalence relation is represented
by a setoid to to enable ready access to the quotient construction. -/
class LeftCongruence (α : Type*) extends eq : Setoid (List α) where
  left_cov : CovariantClass _ _ (fun x y => x ++ y) eq

namespace LeftCongruence

/-- The equivalence class (as a language) corresponding to an element of the quotient type. -/
abbrev eqvCls [c : LeftCongruence α] (a : Quotient c.eq) : Language α :=
  (Quotient.mk c.eq) ⁻¹' {a}

end LeftCongruence

/-- A (two-sided) congruence is an equivalence relation on finite sequences (represented by lists)
that is both a left-congruence and a right-congruence. -/
class Congruence (α : Type*) extends LeftCongruence α, RightCongruence α where

namespace Congruence

/-- The equivalence class (as a language) corresponding to an element of the quotient type. -/
abbrev eqvCls [c : Congruence α] (a : Quotient c.eq) : Language α :=
  (Quotient.mk c.eq) ⁻¹' {a}

end Congruence

end Language
