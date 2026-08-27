/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Semantics.LTS.MapHom

/-!
# Preimage construction on nondeterministic automata
-/


@[expose] public section

namespace Cslib.Automata.NA.FinAcc

open Acceptor Language _root_.Language

variable {State Symbol Symbol' : Type*} (f : Hom Symbol' Symbol)

/--
Given a language homomorphism `f` from `Symbol'` to `Symbol` and an NA `na` on `Symbol`,
`na.preimage f` is an NA on `Symbol` with the same state space, start states, and
accept states, but with a different transition relation: the step that `na.preimage f` takes
on input `x` is the composition of the steps taken by `na` on inputs `f [x]`. -/
def preimage (na : FinAcc State Symbol) : FinAcc State Symbol' where
  toLTS := na.toLTS.mapHom f
  start := na.start
  accept := na.accept

@[simp, grind =]
theorem preimage_start (na : FinAcc State Symbol) : (na.preimage f).start = na.start := rfl

@[simp, grind =]
theorem preimage_accept (na : FinAcc State Symbol) : (na.preimage f).accept = na.accept := rfl

@[simp, grind =]
theorem preimage_mTr (na : FinAcc State Symbol) {xs' : List Symbol'} {s t : State} :
    (na.preimage f).MTr s xs' t ↔ na.MTr s (f xs') t :=
  LTS.mapHom_mTr

/-- `na.preimage f` accepts a word `xs'` iff `na` accepts the word `f xs'`. -/
@[simp]
theorem accepts_preimage {na : FinAcc State Symbol} {xs' : List Symbol'} :
    Accepts (na.preimage f) xs' ↔ Accepts na (f xs') := by
  simp [Accepts]

/-- `na.preimage f` accepts the preimage under `f` of the language accepted by `na`. -/
@[simp]
theorem preimage_language_eq (na : FinAcc State Symbol) :
    language (na.preimage f) = (language na).preimage f := by
  ext
  simp

end Cslib.Automata.NA.FinAcc
