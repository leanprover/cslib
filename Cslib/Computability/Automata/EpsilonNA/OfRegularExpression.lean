/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Computability.Automata.EpsilonNA.ThompsonConstruction
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Computability.RegularExpressions

/-! # The ε-NA of a regular expression

Thompson's construction [Thompson1968]: every regular expression is sent to an `εNA` with finitely
many states that accepts exactly its language, by assembling the automata of
`Cslib.Computability.Automata.EpsilonNA.ThompsonConstruction`.

## Main definitions

* `RegularExpression.State r`: the states of the automaton of `r`.
* `RegularExpression.toEpsilonNA r`: the automaton of `r`.

## Main statements

* `RegularExpression.language_toEpsilonNA`: the automaton of `r` accepts exactly `r.matches'`.

## References

* [K. Thompson, *Regular expression search algorithm*][Thompson1968]
-/

@[expose] public section

namespace RegularExpression

open Cslib.Automata Cslib.Automata.εNA Cslib.Automata.Acceptor

variable {α : Type*}

/-- The states of the automaton of a regular expression. -/
def State : RegularExpression α → Type
  | zero => Unit
  | epsilon => Unit
  | char _ => Bool
  | plus P Q => Bool ⊕ (P.State ⊕ Q.State)
  | comp P Q => P.State ⊕ Q.State
  | star P => Unit ⊕ P.State

/-- The automaton of a regular expression has finitely many states. -/
instance instFiniteState : (r : RegularExpression α) → Finite r.State
  | zero => inferInstanceAs (Finite Unit)
  | epsilon => inferInstanceAs (Finite Unit)
  | char _ => inferInstanceAs (Finite Bool)
  | plus P Q =>
    haveI := instFiniteState P
    haveI := instFiniteState Q
    inferInstanceAs (Finite (Bool ⊕ (P.State ⊕ Q.State)))
  | comp P Q =>
    haveI := instFiniteState P
    haveI := instFiniteState Q
    inferInstanceAs (Finite (P.State ⊕ Q.State))
  | star P =>
    haveI := instFiniteState P
    inferInstanceAs (Finite (Unit ⊕ P.State))

/-- Thompson's construction: the `εNA` of a regular expression. -/
def toEpsilonNA : (r : RegularExpression α) → FinAcc r.State α
  | zero => FinAcc.zero
  | epsilon => FinAcc.epsilon
  | char a => FinAcc.char a
  | plus P Q => P.toEpsilonNA.union Q.toEpsilonNA
  | comp P Q => P.toEpsilonNA.concat Q.toEpsilonNA
  | star P => P.toEpsilonNA.star

/-- The automaton of a regular expression accepts exactly its language. -/
@[simp]
theorem language_toEpsilonNA (r : RegularExpression α) :
    language r.toEpsilonNA = r.matches' := by
  induction r with
  | zero => exact FinAcc.language_zero
  | epsilon => exact FinAcc.language_epsilon
  | char a => exact FinAcc.language_char a
  | plus P Q ihP ihQ => exact (FinAcc.language_union _ _).trans (by rw [ihP, ihQ]; rfl)
  | comp P Q ihP ihQ => exact (FinAcc.language_concat _ _).trans (by rw [ihP, ihQ]; rfl)
  | star P ih => exact (FinAcc.language_star _).trans (by rw [ih]; rfl)

end RegularExpression
