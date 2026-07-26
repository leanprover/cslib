/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Free

/-!
# Polynomial Functor Universe Tests

These tests exercise the universe-polymorphic polynomial sum and the W-type representation of
`PFunctor.FreeM`.
-/

universe uA₁ uA₂ uB v

namespace CslibTests

open PFunctor

variable {P : PFunctor.{uA₁, uB}} {α : Type v} {β : Type uA₂}

/-- Addition notation remains available when its result universe is fixed by the expected type. -/
example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} := P + Q

private def isPure {P : PFunctor.{uA₁, uB}} {α : Type v} : P.FreeM α → Bool :=
  FreeM.rec (motive := fun _ => Bool) (fun _ => true) (fun _ _ _ => false)

/-- The `cases` tactic picks up the registered case eliminator. -/
example (x : P.FreeM α) : isPure x = true ∨ isPure x = false := by
  cases x with
  | pure a => left; rfl
  | lift_bind a cont => right; rfl

/-- The `induction` tactic picks up the registered induction eliminator. -/
example (x : P.FreeM α) : x.bind FreeM.pure = x := by
  induction x with
  | pure a => rfl
  | lift_bind a cont ih => simp only [FreeM.liftBind_bind, ih]

private def coin : PFunctor.{0, 0} := ⟨Bool, fun b => if b then Bool else Nat⟩

/-- A ground free computation remains small enough to serve as another polynomial's directions. -/
private def scheduler : PFunctor.{0, 0} := ⟨Unit, fun _ => coin.FreeM Bool⟩

example : scheduler.B () = coin.FreeM Bool := rfl

end CslibTests
