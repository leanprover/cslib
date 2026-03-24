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

public abbrev Var := ℕ

/-- The cell of a single Turing tape. -/
public structure TapeCell where
  c : Option Char
  containsHead : Bool

/-- Cells from `k` Turing tapes combined into one cell. -/
public structure MultiCell (k : ℕ) where
  cells : Vector TapeCell k
  isLeftEnd : Bool
  isRightEnd : Bool

public instance : StrEnc TapeCell where
  toData cell := Data.list [StrEnc.toData cell.c, StrEnc.toData cell.containsHead]
  fromData
    | Data.list [c, containsHead] => do
        let c' ← StrEnc.fromData c
        let containsHead' ← StrEnc.fromData containsHead
        pure { c := c', containsHead := containsHead' }
    | _ => none
  fromData_toData := by
    intro c
    sorry


end UniversalTM

end Turing
