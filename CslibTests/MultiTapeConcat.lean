/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concat

namespace CslibTests.MultiTapeConcat

open Turing.MultiTapeTM

/-- Emit the symbol under the input head, having first moved the head off the start. Since the head
is left at the right boundary, the second machine of a concatenation only sees the same input if
the head is rewound in between. -/
private def echo : Turing.MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ input _ := ⟨1, Fin.elim0, input, none⟩

example : (echo.runFrom (echo.initCfg [true]) 1).output = [true] := by rfl

-- One step for each machine and three for the rewind in between.
example : ((concat echo echo).runFrom ((concat echo echo).initCfg [true]) 5).state = none := by rfl

example : ((concat echo echo).runFrom ((concat echo echo).initCfg [true]) 5).output =
    [true, true] := by rfl

example : ((concat echo echo).runFrom ((concat echo echo).initCfg [false]) 5).output =
    [false, false] := by rfl

/-- Copy the symbol under the input head to a work tape, then emit it from there. -/
private def echoVia : Turing.MultiTapeTM 1 Bool Bool where
  q₀ := false
  tr q input work := match q with
    | false => ⟨1, fun _ => (some input, 0), none, some true⟩
    | true => ⟨0, fun _ => (none, 0), work 0, none⟩

example : (echoVia.runFrom (echoVia.initCfg [true]) 2).output = [true] := by rfl

-- Two steps for each machine and three for the rewind in between.
example : ((concat echoVia echoVia).runFrom
    ((concat echoVia echoVia).initCfg [true]) 7).output = [true, true] := by rfl

-- Each of the two work tapes is used, and each of them for a single cell.
example : (concat echoVia echoVia).spaceUsed ((concat echoVia echoVia).initCfg [true]) 7 = 2 := by
  rfl

-- The two machines really do run on disjoint blocks of work tapes.
example : ((concat echoVia echoVia).runFrom
    ((concat echoVia echoVia).initCfg [true]) 7).workTapes (concatTapeLeft 1 1 0) 0 =
      some true := by rfl

example : ((concat echoVia echoVia).runFrom
    ((concat echoVia echoVia).initCfg [true]) 7).workTapes (concatTapeRight 1 1 0) 0 =
      some true := by rfl

end CslibTests.MultiTapeConcat
