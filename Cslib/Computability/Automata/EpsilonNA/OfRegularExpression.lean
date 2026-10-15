/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Thompson
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Data.Fintype.Sum

/-! # The ε-NA of a regular expression

Thompson's construction [Thompson1968]: every regular expression is sent to an `εNA` with finitely
many states that accepts exactly its language, by assembling the automata of
`Cslib.Computability.Automata.EpsilonNA.Thompson`.

## Main definitions

* `RegularExpression.State r`: the states of the automaton of `r`.
* `RegularExpression.toεNA r`: the automaton of `r`.

## Main statements

* `RegularExpression.language_toεNA`: the automaton of `r` accepts exactly `r.matches'`.

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

instance instFintypeState : (r : RegularExpression α) → Fintype r.State
  | zero => inferInstanceAs (Fintype Unit)
  | epsilon => inferInstanceAs (Fintype Unit)
  | char _ => inferInstanceAs (Fintype Bool)
  | plus P Q =>
    letI := instFintypeState P
    letI := instFintypeState Q
    inferInstanceAs (Fintype (Bool ⊕ (P.State ⊕ Q.State)))
  | comp P Q =>
    letI := instFintypeState P
    letI := instFintypeState Q
    inferInstanceAs (Fintype (P.State ⊕ Q.State))
  | star P =>
    letI := instFintypeState P
    inferInstanceAs (Fintype (Unit ⊕ P.State))

instance instDecidableEqState : (r : RegularExpression α) → DecidableEq r.State
  | zero => inferInstanceAs (DecidableEq Unit)
  | epsilon => inferInstanceAs (DecidableEq Unit)
  | char _ => inferInstanceAs (DecidableEq Bool)
  | plus P Q =>
    letI := instDecidableEqState P
    letI := instDecidableEqState Q
    inferInstanceAs (DecidableEq (Bool ⊕ (P.State ⊕ Q.State)))
  | comp P Q =>
    letI := instDecidableEqState P
    letI := instDecidableEqState Q
    inferInstanceAs (DecidableEq (P.State ⊕ Q.State))
  | star P =>
    letI := instDecidableEqState P
    inferInstanceAs (DecidableEq (Unit ⊕ P.State))

/-- Thompson's construction: the `εNA` of a regular expression. -/
def toεNA : (r : RegularExpression α) → FinAcc r.State α
  | zero => FinAcc.zero
  | epsilon => FinAcc.epsilon
  | char a => FinAcc.char a
  | plus P Q => P.toεNA.union Q.toεNA
  | comp P Q => P.toεNA.concat Q.toεNA
  | star P => P.toεNA.star

/-- The automaton of a regular expression accepts exactly its language. -/
@[simp]
theorem language_toεNA (r : RegularExpression α) : language r.toεNA = r.matches' := by
  induction r with
  | zero => exact FinAcc.language_zero
  | epsilon => exact FinAcc.language_epsilon
  | char a => exact FinAcc.language_char a
  | plus P Q ihP ihQ => exact (FinAcc.language_union _ _).trans (by rw [ihP, ihQ]; rfl)
  | comp P Q ihP ihQ => exact (FinAcc.language_concat _ _).trans (by rw [ihP, ihQ]; rfl)
  | star P ih => exact (FinAcc.language_star _).trans (by rw [ih]; rfl)

end RegularExpression
