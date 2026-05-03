/-
Copyright (c) 2026 Henning Dieterichs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Dieterichs
-/

module

public import Cslib.Computability.CellularAutomata.Defs
public import Mathlib.Computability.Language

@[expose] public section

/-! # Cellular Automata: Language Acceptance

This file defines language-accepting cellular automata and acceptance schemes.

An `LCellAutomaton α Q` is a cellular automaton that reads an input word over `α` (with `none`
as a border symbol) and produces a `Bool` output.

An `AcceptanceScheme` describes how the output is read: given the input length `n`, it specifies
the time step `t n` and position `p n` at which to read the accept/reject decision.

## Main definitions

* `LCellAutomaton` — language-accepting cellular automaton.
* `wordToConfig` — convert a finite word to a configuration with border symbols.
* `AcceptanceScheme` — when and where to read acceptance.
* `AcceptanceScheme.rt` — real-time acceptance (time `n - 1`, position `0`).
* `AcceptanceScheme.rtRight` — real-time rightmost acceptance.
* `AcceptanceScheme.lt` — linear-time acceptance.
* `LCellAutomaton.accepts` — whether a CA accepts a word under a given scheme.
* `LCellAutomaton.lang` — the language recognized by a CA under a given scheme.

## References

* [A. R. Smith III, *Real-Time Language Recognition by One-Dimensional Cellular Automata*][Smith1972]
* [M. Kutrib, *Cellular Automata and Language Theory*][Kutrib2009]
-/

namespace Cslib.CellularAutomata

/-- A language-accepting cellular automaton: input is `Option α` (with `none` as border),
output is `Bool` (accept/reject). -/
abbrev LCellAutomaton (α Q : Type*) := CellAutomaton (Option α) Bool Q

namespace LCellAutomaton

variable {α Q : Type*} (C : LCellAutomaton α Q)

/-- The border state (embedding of `none`). -/
def border : Q := C.embed none

/-- The internal state corresponding to an input symbol. -/
def inner (a : α) : Q := C.embed (some a)

end LCellAutomaton

/-- Convert a finite word to a configuration with border symbols. Positions
`0` through `w.length - 1` contain the corresponding word symbols; all other
positions are `none`. -/
def wordToConfig {α : Type*} (w : List α) : Config (Option α) :=
  fun p => if h : p ≥ 0 ∧ p < w.length then some w[p.toNat] else none

/-- An acceptance scheme describes how a CA reads its output:
given input length `n`, read at time `t n` and position `p n`. -/
structure AcceptanceScheme where
  /-- The time step at which to read the output, as a function of input length. -/
  t : ℕ → ℕ
  /-- The position at which to read the output, as a function of input length. -/
  p : ℕ → Int

namespace AcceptanceScheme

/-- Real-time, position 0: read at time `n - 1`, position `0`. -/
def rt : AcceptanceScheme where
  t := fun n => n - 1
  p := fun _ => 0

/-- Real-time, rightmost position: read at time `n - 1`, position `n`. -/
def rtRight : AcceptanceScheme where
  t := fun n => n - 1
  p := fun n => n

/-- Linear-time with constant `c`, position 0. -/
def lt (c : ℕ) : AcceptanceScheme where
  t := fun n => c * n
  p := fun _ => 0

end AcceptanceScheme

namespace LCellAutomaton

variable {α Q : Type*}

/-- Whether `C` accepts word `w` under acceptance scheme `s`. -/
def accepts (C : LCellAutomaton α Q) (s : AcceptanceScheme) (w : List α) : Bool :=
  C.comp (C.embedConfig (wordToConfig w)) (s.t w.length) (s.p w.length)

/-- The language recognized by `C` under acceptance scheme `s`. -/
def lang (C : LCellAutomaton α Q) (s : AcceptanceScheme) : Language α :=
  { w | C.accepts s w }

end LCellAutomaton

end Cslib.CellularAutomata
