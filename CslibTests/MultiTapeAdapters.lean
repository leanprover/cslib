/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToWorkTape
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromWorkTape

namespace CslibTests.MultiTapeAdapters

open Turing.MultiTapeTM

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ _ _ := ⟨move, Fin.elim0, some symbol, none⟩

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

end CslibTests.MultiTapeAdapters
