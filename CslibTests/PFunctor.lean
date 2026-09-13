/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Basic

/-!
# Polynomial Functor Tests

These tests exercise the universe-polymorphic polynomial sum and product, the simp API for
the basic constructions, and the extensionality lemma.
-/

universe uA uB uA₁ uA₂ uB₁ uB₂ v

namespace CslibTests

open PFunctor
open scoped PFunctor

/-- Binary monomial notation preserves independent shape and direction universes. -/
example (A : Type uA) (B : Type uB) : PFunctor.{uA, uB} := A y^ B

/-- Prefix power notation denotes a representable polynomial functor. -/
example (B : Type uB) : (y^ B : PFunctor.{uA, uB}) = purePower B := rfl

/-- Addition notation is available when its result universe is fixed by the expected type. -/
example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} := P + Q

/-- Multiplication notation is likewise available, including for child types in
different universes. -/
example (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} := P * Q

section elaboration

/-! ### When `+` fails to elaborate

The `def` spelling `P.add Q` elaborates in every position. The `+` spelling fails in exactly one
situation: prefix-application position, e.g. as the argument of `PFunctor.W`, when the expected
type only determines the universe levels of the sum up to a `max`. This is the motivating use
case for keeping `PFunctor.add` as a `def` alongside the `HAdd` instance. -/

/-- The `def` spelling elaborates under `PFunctor.W` with a `max`-shaped expected type. -/
example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) : Type (max uA₁ uA₂ uB) :=
  PFunctor.W (P.add Q)

/- The failure is not caused by universe metavariables in `C α`: it also occurs for the sum of
two polynomial functors with fully determined universes. -/
/--
error: Type mismatch
  P + Q
has type
  PFunctor.{max uA₁ uA₂, uB}
of sort
  Type (max (max (uA₁ + 1) (uA₂ + 1)) (uB + 1))
but is expected to have type
  PFunctor.{uA₁, uB}
of sort `Type (max (uA₁ + 1) (uB + 1))`
---
error: failed to solve universe constraint
  max (max uA₁ uA₂) uB =?= max uB uA₁
while trying to unify
  Type (max uA₁ uA₂ uB) : Type ((max uA₁ uA₂ uB) + 1)
with
  Type (max uA₁ uB) : Type ((max uA₁ uB) + 1)
-/
#guard_msgs in
example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) : Type (max uA₁ uA₂ uB) :=
  PFunctor.W (P + Q)

end elaboration

section simp

variable (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (R : PFunctor.{uA₂, uB₂})

example : (P + Q).A = (P.A ⊕ Q.A) := by simp
example : (P.add Q).A = (P.A ⊕ Q.A) := by simp
example (a : P.A) : (P + Q).B (.inl a) = P.B a := by simp
example (a : Q.A) : (P + Q).B (.inr a) = Q.B a := by simp
example (a : P.A) : (P.add Q).B (.inl a) = P.B a := by simp
example (a : Q.A) : (P.add Q).B (.inr a) = Q.B a := by simp
example : (P * R).A = (P.A × R.A) := by simp
example (a : P.A) (b : R.A) : (P * R).B (a, b) = (P.B a ⊕ R.B b) := by simp
example (a : P.A) (b : R.A) : (P.prod R).B (a, b) = (P.B a ⊕ R.B b) := by simp
example (ab : (P * R).A) : (P * R).B ab = (P.B ab.1 ⊕ R.B ab.2) := by simp

/-- The named monomials reduce to the canonical `0`, `1`, and `y`. -/
example : (C PUnit : PFunctor.{uA, uB}) = 1 := by simp
example : (linear PUnit : PFunctor.{uA, uB}) = y := by simp
example : (selfMonomial PUnit : PFunctor.{uA, uA}) = y := by simp
example : (purePower PUnit : PFunctor.{uA, uB}) = y := by simp

end simp

/-- The `ext` tactic picks up the registered extensionality lemma. -/
example (P Q : PFunctor.{uA, uB}) (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) :
    P = Q := by
  ext x
  · exact h
  · exact h' x

end CslibTests
