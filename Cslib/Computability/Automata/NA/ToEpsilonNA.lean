/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Foundations.Semantics.LTS.MapHom

/-! # Translation of Nondeterministic Automata into Nondeterministic Automata with ε-transitions

An `NA` is an `εNA` whose ε-transitions are self-loops.
-/

@[expose] public section

namespace Cslib.Automata.NA

variable {State Symbol : Type*}

/-- `NA` is a special case of `εNA`, through `LTS.mapHom` and `Language.Hom.reduceOption`: the
transitions on `some x` are the runs of the `NA` on `[x]`, and the ε-transitions are self-loops. -/
def toEpsilonNA (a : NA State Symbol) : εNA State Symbol where
  toLTS := a.toLTS.mapHom Language.Hom.reduceOption
  start := a.start

namespace FinAcc

/-- `NA.FinAcc` is a special case of `εNA.FinAcc`. -/
def toEpsilonNAFinAcc (a : NA.FinAcc State Symbol) : εNA.FinAcc State Symbol :=
  { a.toEpsilonNA with accept := a.accept }

open Acceptor in
/-- The `εNA.FinAcc` constructed from an `NA.FinAcc` has the same language. -/
@[simp]
theorem toEpsilonNAFinAcc_language_eq {a : NA.FinAcc State Symbol} :
    language a.toEpsilonNAFinAcc = language a := by
  ext xs
  rw [εNA.FinAcc.mem_language_iff, mem_language]
  constructor
  · rintro ⟨s, hs, t, ht, μs, rfl, h⟩
    exact ⟨s, hs, t, ht, LTS.mapHom_mTr.mp h⟩
  · rintro ⟨s, hs, t, ht, h⟩
    use s, hs, t, ht, xs.map some
    split_ands
    · simp [List.reduceOption]
    · apply LTS.mapHom_mTr.mpr
      simpa [Language.Hom.reduceOption_apply, List.reduceOption]

end FinAcc

end Cslib.Automata.NA
