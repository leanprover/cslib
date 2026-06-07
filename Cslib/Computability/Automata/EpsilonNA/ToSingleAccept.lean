/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic

/-! # Translation of εNA into εNA with a single accept state. -/

@[expose] public section

namespace Cslib.Automata.εNA.FinAcc

variable {State Symbol : Type*}

/-- Any `εNA.FinAcc` can be converted into an `εNA.FinAcc` with a single accept state `none`.
The original states are wrapped in `some`, and all original accept states have ε-transitions to
`none`. -/
@[scoped grind]
def toSingleAccept (a : εNA.FinAcc State Symbol) : εNA.FinAcc (Option State) Symbol where
  start := some '' a.start
  accept := {none}
  Tr
    | some s, x, some s' => a.Tr s x s'
    | some s, none, none => s ∈ a.accept
    | _, _, _ => False

open scoped LTS LTS.MTr LTS.STr LTS.SMTr

theorem toSingleAccept_tr_tr {a : εNA.FinAcc State Symbol} :
    a.toSingleAccept.Tr (some s) x (some s') ↔ a.Tr s x s' := by
  simp [toSingleAccept]

theorem toSingleAccept_tr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.Tr os x (some s')) : os.isSome := by
  cases os with
  | none => simp only [toSingleAccept] at h
  | some _ => simp



open Acceptor in
theorem toSingleAccept_language_eq {a : εNA.FinAcc State Symbol} :
    language a.toSingleAccept = language a := by sorry

end Cslib.Automata.εNA.FinAcc
