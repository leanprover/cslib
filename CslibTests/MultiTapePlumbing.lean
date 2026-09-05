/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.RewindInput
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Comp

/-! Executable regressions and interface checks for generic TM plumbing. -/

namespace CslibTests.MultiTapePlumbing

open Turing.MultiTapeTM

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ _ _ := ⟨move, Fin.elim0, some symbol, none⟩

-- Sequential execution retains the output accumulated by the first machine.
example : (((finish 0 true).seq (finish 0 false)).runFrom
    (((finish 0 true).seq (finish 0 false)).initCfg []) 2).output = [true, false] := by rfl

-- Rewinding works when the native halt is at either boundary, including on empty input.
example : ((finish (-1) true).rewindInput.runFrom
    ((finish (-1) true).rewindInput.initCfg [false]) 3).inputPos = 1 := by rfl

example : ((finish 1 true).rewindInput.runFrom
    ((finish 1 true).rewindInput.initCfg [false]) 4).inputPos = 1 := by rfl

example : ((finish 1 true).rewindInput.runFrom
    ((finish 1 true).rewindInput.initCfg []) 3).state = none := by rfl

example : ((finish 1 true).rewindInput.runFrom
    ((finish 1 true).rewindInput.initCfg []) 3).output = [true] := by rfl

private def filled (xs : List Bool) : Cfg 1 Bool Unit [] :=
  ⟨none, 1, fun _ => listTape xs, fun _ => xs.length, []⟩

-- Work-tape rewind preserves the contents and resets the head, even for empty contents.
example : ((rewind (.work (0 : Fin 1))).runFrom
    (Rewind.workCfg (filled []) 0 (some .start) 0) 2).workTapePos 0 = 0 := by rfl

example : ((rewind (.work (0 : Fin 1))).runFrom
    (Rewind.workCfg (filled [true, false]) 0 (some .start) 2) 4).state = none := by rfl

example : ((rewind (.work (0 : Fin 1))).runFrom
    (Rewind.workCfg (filled [true, false]) 0 (some .start) 2) 4).workTapes 0 =
      listTape [true, false] := by rfl

-- Output redirection includes the symbol emitted on the halting transition.
example : ((finish 0 true).outputToWorkTape.runFrom
    ((finish 0 true).outputToWorkTape.initCfg []) 1).workTapes 0 0 = some true := by rfl

example : ((finish 0 true).outputToWorkTape.runFrom
    ((finish 0 true).outputToWorkTape.initCfg []) 1).output = [] := by rfl

private def readInput : Turing.MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ input _ := ⟨0, Fin.elim0, input, none⟩

-- Substituted input is read from the work tape, with the real head parked elsewhere.
private def preparedInput (xs : List Bool) : Cfg 1 Bool (InputState Unit) [false] :=
  InputFromWorkTape.classifyCfg 0 (readInput.initCfg xs) .right

example : (readInput.inputFromWorkTape.runFrom (preparedInput [true]) 3).output = [true] := by
  rfl

example : (readInput.inputFromWorkTape.runFrom (preparedInput [true]) 3).inputPos = 0 := by rfl

example : (readInput.inputFromWorkTape.runFrom (preparedInput []) 3).state = none := by rfl

private def sparse : Fin 1 ↪ Fin 3 := ⟨fun _ => 2, fun _ _ _ => Subsingleton.elim _ _⟩

private def writer : Turing.MultiTapeTM 1 Bool Unit where
  q₀ := ()
  tr _ _ _ := ⟨0, fun _ => (some (some true), 1), none, none⟩

-- The injection is not an initial-segment inclusion; unused tape data and heads are retained.
example : ((writer.extendTapes sparse).runFrom
    (ExtendTapes.embed sparse (writer.initCfg [])
      (fun _ _ => some false) (fun _ => 7)) 1).workTapes 0 0 = some false := by rfl

example : ((writer.extendTapes sparse).runFrom
    (ExtendTapes.embed sparse (writer.initCfg [])
      (fun _ _ => some false) (fun _ => 7)) 1).workTapePos 0 = 7 := by rfl

example : ((writer.extendTapes sparse).runFrom
    (ExtendTapes.embed sparse (writer.initCfg [])
      (fun _ _ => some false) (fun _ => 7)) 1).workTapes 2 0 = some true := by rfl

private def bit : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; simpa using h⟩

-- Bounds can differ for inputs of the same encoded length; the public combinator needs no
-- monotonicity premise and hides the machine witnesses.
private lemma constant_computable :
    ComputableInTimeAndSpace (fun _ : Bool => true) bit bit
      (fun b => if b then 1 else 2) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, finish 0 true, fun b => ⟨1, ?_, 0, le_rfl, ?_⟩⟩
  · cases b <;> decide
  · exact ⟨rfl, rfl, spaceUsed_zero_tapes_eq_zero _ _ rfl⟩

example : ComputableInTimeAndSpace (fun _ : Bool => true) bit bit
    (fun b => (if b then 1 else 2) + 6) (fun _ => 3) := by
  have hbit (b : Bool) : bit b = [b] := rfl
  simpa [hbit, Nat.add_assoc] using
    computableInTimeAndSpace_comp constant_computable constant_computable

end CslibTests.MultiTapePlumbing
