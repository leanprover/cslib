/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Automata.Transducers.Transducer

open Cslib.Automata

private instance : Transducer Unit Nat Nat where
  Translates _ xs ys := xs = ys

-- Opening the transducer notation must leave ordinary list indexing available.
example (xs : List Nat) (h : 0 < xs.length) : xs[0] - 1 = xs[0] - 1 := rfl

-- Translation has relation precedence, so conjunction remains outside its operands.
example (xs ys : List Nat) : (xs [()]↦ ys ∧ True) ↔ xs = ys ∧ True := Iff.rfl
