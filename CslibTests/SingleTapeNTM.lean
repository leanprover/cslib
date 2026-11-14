/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.Turing.SingleTape.NonDeterministic

namespace CslibTests.SingleTapeNTM

open Cslib.Automata Cslib.Computability.Turing.SingleTape Cslib.Turing

-- Blank and nonblank reads must remain distinct.
example : (TrLabel.read (none : Option Bool)).applyToTape (some BiTape.nil) =
    some BiTape.nil := rfl

example : (TrLabel.read (some true)).applyToTape (some (BiTape.mk₁ [])) = none := rfl

example : (TrLabel.read (none : Option Bool)).applyToTape (some (BiTape.mk₁ [true])) =
    none := rfl

example : (TrLabel.read (some true)).applyToTape (some (BiTape.mk₁ [true])) =
    some (BiTape.mk₁ [true]) := rfl

-- Erasing a singleton must yield the empty output tape.
private def eraser : SingleTapeNTM Bool Bool where
  Tr q μ q' := q = false ∧ μ = .write none ∧ q' = true
  start := {false}
  accept := {true}
  accept_halting := by
    rintro s hs ⟨μ, q, h, _, _⟩
    simp_all

example (x : Bool) : Transducer.Translates eraser [x] [] := by
  refine ⟨false, rfl, Cfg.mk₁ true [], rfl, ?_, rfl⟩
  apply Relation.ReflTransGen.single
  exact ⟨.write none, ⟨rfl, rfl, rfl⟩, rfl⟩

end CslibTests.SingleTapeNTM
