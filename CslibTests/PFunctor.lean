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

/-- The `def` spelling `P.add (.const α)` elaborates under `PFunctor.W` even when the
expected type only determines the universe levels up to a `max`. This is the motivating
use case for keeping `PFunctor.add` as a `def` alongside the `HAdd` instance. -/
example (P : PFunctor.{uA₁, uB}) (α : Type v) : Type (max uA₁ uB v) :=
  PFunctor.W (P.add (.const α))

/- The `+` spelling of the same type fails: the `binop%` elaborator behind `+` commits the
universe metavariables in the expected type to the first operand's universes before it
considers the heterogeneous `HAdd` instance. -/
/--
error: Type mismatch
  P + const α
has type
  PFunctor.{max uA₁ v, uB}
of sort
  Type (max (max (uA₁ + 1) (uB + 1)) (v + 1))
but is expected to have type
  PFunctor.{uA₁, uB}
of sort `Type (max (uA₁ + 1) (uB + 1))`
---
error: failed to solve universe constraint
  max (max uA₁ uB) v =?= max uB uA₁
while trying to unify
  Type (max uA₁ uB v) : Type ((max uA₁ uB v) + 1)
with
  Type (max uA₁ uB) : Type ((max uA₁ uB) + 1)
-/
#guard_msgs in
example (P : PFunctor.{uA₁, uB}) (α : Type v) : Type (max uA₁ uB v) :=
  PFunctor.W (P + PFunctor.const α)

/-- The simp set rewrites the head type of a sum through the `+` notation. -/
example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    (P + Q).A = (P.A ⊕ Q.A) := by simp

/-- The simp set computes child types of a sum on both shapes. -/
example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : P.A) :
    (P.add Q).B (.inl a) = P.B a := by simp

example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : Q.A) :
    (P.add Q).B (.inr a) = Q.B a := by simp

/-- Nested sum directions normalize during elaboration. -/
example (P Q R : PFunctor.{uA, uB}) (q : Q.A) (consume : Q.B q → Nat)
    (d : ((P + Q) + R).B (.inl (.inr q))) : consume d = consume d := rfl

/-- The simp set computes head and child types of a product. -/
example (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (a : P.A) (b : Q.A) :
    (P * Q).B (a, b) = (P.B a ⊕ Q.B b) := by simp

/-- The named monomials reduce to the canonical `0`, `1`, and `y`. -/
example : (const PUnit : PFunctor.{uA, uB}) = 1 := by simp
example : (linear PUnit : PFunctor.{uA, uB}) = y := by simp
example : (selfMonomial PUnit : PFunctor.{uA, uA}) = y := by simp
example : (purePower PUnit : PFunctor.{uA, uB}) = y := by simp

/-- The `ext` tactic picks up the registered extensionality lemma. -/
example (P Q : PFunctor.{uA, uB}) (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) :
    P = Q := by
  ext
  · exact h
  · exact h' _

end CslibTests
