/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.TapeView
public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Navigation
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Copy
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Eq
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.ListIteration
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed

namespace Turing

namespace UniversalTM

open Routines

/-- TODO document -/
public abbrev Var := ℕ

/-- The cell of a single Turing tape. -/
public structure TapeCell where
  /-- TODO document -/
  c : Option Char
  /-- TODO document -/
  containsHead : Bool

/-- Cells from `k` Turing tapes combined into one cell. -/
public structure MultiCell (k : ℕ) where
  /-- One cell from each tape. -/
  cells : Vector TapeCell k
  /-- Is this the left-most cell (across all tapes)? -/
  isLeftEnd : Bool
  /-- Is this the right-most cell (across all tapes)? -/
  isRightEnd : Bool

public instance : StrEnc TapeCell where
  toData cell := StrEnc.toData (cell.c, cell.containsHead)
  fromData d := do
    let (c, containsHead) ← StrEnc.fromData d
    pure { c, containsHead }
  fromData_toData := by
    intro c
    simp

public instance (α : Type) [StrEnc α] (k : ℕ) : StrEnc (Vector α k) where
  toData v := StrEnc.toData v.toList
  fromData d := do
      let ls : List α ← StrEnc.fromData d
      if h : ls.length = k then
        pure ⟨ls.toArray, h⟩
      else
        none
  fromData_toData := by
    intro v
    simp [Vector.toList]

public instance : StrEnc (MultiCell (k : ℕ)) where
  toData mc := StrEnc.toData (mc.cells, mc.isLeftEnd, mc.isRightEnd)
  fromData d := do
    let (cells, isLeftEnd, isRightEnd) <- StrEnc.fromData d
    pure { cells, isLeftEnd, isRightEnd }
  fromData_toData := by
    intro v
    simp

/-
Outline of UTM:
while the current state is not None:
- for each tape, find the head position on the multi-tape and copy the current symbol to an aux tape.
- now the aux tape contains the symbols in the correct order.
- copy the current state to the aux tape.
- the contents of the aux tape is exactly the input to the transition function
- "evaluate the transition function" by iterating through its table and storing the result on another tape
- execute the actions for each of the tapes:
  - find the head. update the symbol, update the head marking according to the move action
    (potentially extend the tape to the left or right)
- update the current state
-/

/- sub-routines we need:
- move to the first element of a list that satisfies a condition:
  tm₁ tm₂ tm₃: For each item in the list: if tm₁ outputs true on an aux tape, run tm₂.
  if it never outputs true, run tm₃
- evaluate a function given by a list of input-output pairs
- update an element in a list, whose encoding size must be the same
- extend a list to the right
-/

/-- The encoding of the given tapes as a list of `MultiCell`s. -/
def encodeTapes (k : ℕ) (tapes : Fin k → BiTape Char) (shifts : Fin k → ℤ) : List (MultiCell k) :=
  sorry

def getHeadSymbol (k : ℕ) (tapeIdx : ℕ) (mt out aux : Fin k) : MultiTapeTM k Char :=
  -- Find the cell where the tapeIdx-th tape has the head
  find_list mt aux (at_path [0, tapeIdx, 1] mt (copyEnc mt aux))
    -- copy the symbol to out
    (at_path [0, tapeIdx, 0] mt (copy_to_list mt out))
    -- otherwise do nothing (because we know there is a head marker)
    (noop)



end UniversalTM

end Turing
