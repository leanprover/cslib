/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.RewindInput

namespace CslibTests.MultiTapeRewind

open Turing.MultiTapeTM

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ _ _ := ⟨move, Fin.elim0, some symbol, none⟩

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

end CslibTests.MultiTapeRewind
