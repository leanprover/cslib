/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic

/-! # Translation of Nondeterministic Automata into Nondeterministic Automata with ε-transitions

An `NA` is an `εNA` without ε-transitions.
-/

@[expose] public section

namespace Cslib.Automata.NA

variable {State Symbol : Type*}

/-- `NA` is a special case of `εNA`: the transitions on `some x` are those of the `NA` on `x`, and
there are no ε-transitions. -/
def toEpsilonNA (a : NA State Symbol) : εNA State Symbol where
  Tr s μ s' := match μ with
    | some x => a.Tr s x s'
    | none => False
  start := a.start

/-- The runs of `toEpsilonNA` are the runs of the `NA`, read through `some`. -/
theorem toEpsilonNA_mTr_iff {a : NA State Symbol} {s t : State} {μs : List (Option Symbol)} :
    a.toEpsilonNA.MTr s μs t ↔ ∃ xs, μs = xs.map some ∧ a.MTr s xs t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl, .refl⟩
    | @stepL _ μ _ _ _ htr _ ih =>
      obtain ⟨xs, rfl, hrun⟩ := ih
      cases μ with
      | none => exact htr.elim
      | some x => exact ⟨x :: xs, rfl, .stepL htr hrun⟩
  · rintro ⟨xs, rfl, h⟩
    induction h with
    | refl => exact .refl
    | stepL htr _ ih => exact .stepL htr ih

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
    obtain ⟨ys, rfl, hrun⟩ := toEpsilonNA_mTr_iff.mp h
    rw [reduceOption_map_some]
    exact ⟨s, hs, t, ht, hrun⟩
  · rintro ⟨s, hs, t, ht, h⟩
    exact ⟨s, hs, t, ht, xs.map some, reduceOption_map_some xs,
      toEpsilonNA_mTr_iff.mpr ⟨xs, rfl, h⟩⟩

end FinAcc

end Cslib.Automata.NA
