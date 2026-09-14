/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.Congruences.MyhillCongruence

/-! # Syntactic monoid

This file defines the syntactic monoid of a language `l` and shows that
`l` is regular if and only if its syntactic monoid is finite.

## References

[Holcombe1982] Holcombe, W.M.L. (1982). Algebraic automata theory. Section 5.3
-/

@[expose] public section

variable {α : Type}

namespace Language

open Cslib.Language

/-- Converting a (two-sided) congruence `c` on finite words to a congruence relation
on the (multiplicative) free monoid. -/
def Congruence.toCon [c : Congruence α] : Con (FreeMonoid α) where
  r := c.r
  iseqv := c.iseqv
  mul' {w x y z} h_wx h_yz := by
    have h_wyxy : c.eq (w * y) (x * y) := c.right_cov.elim y h_wx
    have h_xyxz : c.eq (x * y) (x * z) := c.left_cov.elim x h_yz
    exact c.iseqv.trans h_wyxy h_xyxz

/-- The syntactic monoid of a language `l` is the quotient of the free monoid
by the Myhill congruence of `l`. -/
abbrev SyntacticMonoid (l : Language α) := l.MyhillCongruence.toCon.Quotient

/-- A language `l` is regular if and only if its syntactic monoid is finite. -/
theorem IsRegular.iff_finite_syntacticMonoid (l : Language α) :
    l.IsRegular ↔ Finite (l.SyntacticMonoid) :=
  IsRegular.iff_finite_myhillQuotient l

end Language
