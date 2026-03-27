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
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.MultiTape
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.ListIteration
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed

namespace Turing

namespace UniversalTM

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
  /-- TODO document -/
  cells : Vector TapeCell k
  /-- TODO document -/
  isLeftEnd : Bool
  /-- TODO document -/
  isRightEnd : Bool

public instance : StrEnc TapeCell where
  toData cell := Data.list [StrEnc.toData cell.c, StrEnc.toData cell.containsHead]
  fromData
    | Data.list [c, containsHead] => do
        pure { c := ← StrEnc.fromData c, containsHead := ← StrEnc.fromData containsHead }
    | _ => none
  fromData_toData := by
    intro c
    sorry

/- Layout of the tapes:
Tape 1: Encoding of the tapes
Tape 2: current state
Tape 3: builds up input for transition function and stores output of transition function
-/

-- def findTapeSymbol (k : ℕ) (tapes : Fin k → BiTape Char) (i : Fin k) : TapeCell :=
--   { c := (tapes i).head, containsHead := true }



end UniversalTM

end Turing
