/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Foundations.Semantics.LTS.LiftOption

/-! # Translation of Nondeterministic Automata into Nondeterministic Automata with ε-transitions

An `NA` is an `εNA` without ε-transitions.
-/

@[expose] public section

namespace Cslib.Automata.NA

variable {State Symbol : Type*}

/-- `NA` is a special case of `εNA`, through `LTS.liftOption`: the transitions on `some x` are
those of the `NA` on `x`, and there are no ε-transitions. -/
def toEpsilonNA (a : NA State Symbol) : εNA State Symbol where
  toLTS := a.toLTS.liftOption
  start := a.start

namespace FinAcc

/-- `NA.FinAcc` is a special case of `εNA.FinAcc`. -/
def toEpsilonNAFinAcc (a : NA.FinAcc State Symbol) : εNA.FinAcc State Symbol :=
  { a.toEpsilonNA with accept := a.accept }

private theorem reduceOption_map_some (xs : List Symbol) : (xs.map some).reduceOption = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

open Acceptor in
/-- The `εNA.FinAcc` constructed from an `NA.FinAcc` has the same language. -/
@[simp]
theorem toEpsilonNAFinAcc_language_eq {a : NA.FinAcc State Symbol} :
    language a.toEpsilonNAFinAcc = language a := by
  ext xs
  rw [εNA.FinAcc.mem_language_iff, mem_language]
  constructor
  · rintro ⟨s, hs, t, ht, μs, rfl, h⟩
    obtain ⟨ys, rfl, hrun⟩ := LTS.liftOption_mTr_iff.mp h
    rw [reduceOption_map_some]
    exact ⟨s, hs, t, ht, hrun⟩
  · rintro ⟨s, hs, t, ht, h⟩
    exact ⟨s, hs, t, ht, xs.map some, reduceOption_map_some xs,
      LTS.liftOption_mTr_iff.mpr ⟨xs, rfl, h⟩⟩

end FinAcc

end Cslib.Automata.NA
