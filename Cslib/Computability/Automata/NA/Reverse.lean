/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Semantics.LTS.Reverse

/-!
# Reversal of nondeterministic automata

This file defines `Cslib.Automata.NA.FinAcc.reverse`, which reverses every transition of a
nondeterministic automaton and swaps its start and accept states. Its underlying transition system
is `Cslib.LTS.reverse`, so the transition results are inherited from
`Cslib/Foundations/Semantics/LTS/Reverse.lean`.

The main result is `FinAcc.reverse_language_eq`: the language accepted by `na.reverse` is the
`Language.reverse` of the language accepted by `na`. It follows from `FinAcc.accepts_reverse`,
the statement that `na.reverse` accepts `xs` iff `na` accepts `xs.reverse`.
-/


@[expose] public section

namespace Cslib.Automata.NA

open Acceptor Language

variable {State Symbol : Type*}

namespace FinAcc

/-- `na.reverse` reverses every transition of `na` and swaps its start and accept states,
so that it accepts exactly the reversals of the words accepted by `na`. -/
def reverse (na : FinAcc State Symbol) : FinAcc State Symbol where
  toLTS := na.toLTS.reverse
  start := na.accept
  accept := na.start

/-- Reversing an automaton twice gives back the original automaton. -/
@[simp]
theorem reverse_reverse (na : FinAcc State Symbol) : na.reverse.reverse = na := rfl

/-- Reversal of an automaton is an involution. -/
theorem reverse_involutive : Function.Involutive (reverse (State := State) (Symbol := Symbol)) :=
  reverse_reverse

/-- The start states of `na.reverse` are the accept states of `na`. -/
@[simp, grind =]
theorem reverse_start (na : FinAcc State Symbol) : na.reverse.start = na.accept := rfl

/-- The accept states of `na.reverse` are the start states of `na`. -/
@[simp, grind =]
theorem reverse_accept (na : FinAcc State Symbol) : na.reverse.accept = na.start := rfl

/-- The multistep transitions of `na.reverse` are exactly the reversed multistep transitions
of `na`. -/
@[simp]
theorem reverse_mTr (na : FinAcc State Symbol) {xs : List Symbol} {s s' : State} :
    na.reverse.MTr s' xs s ↔ na.MTr s xs.reverse s' := LTS.reverse_mTr

/-- `na.reverse` accepts a word iff `na` accepts its reversal. -/
@[simp]
theorem accepts_reverse {na : FinAcc State Symbol} {xs : List Symbol} :
    Accepts na.reverse xs ↔ Accepts na xs.reverse := by
  grind [Accepts, reverse_mTr]

/-- `na.reverse` accepts exactly the reversals of the words accepted by `na`. -/
@[simp]
theorem reverse_language_eq (na : FinAcc State Symbol) :
    language na.reverse = (language na).reverse := by
  ext; simp

end FinAcc

end Cslib.Automata.NA
