/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.Encoding
public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines

namespace Turing

namespace Satisfiability

abbrev Var := ℕ

inductive Literal where
  | pos (v : Var)
  | neg (v : Var)

instance : StrEnc Literal where
  encInner
    | Literal.pos v => (StrEnc.enc 0) ++ (StrEnc.enc v)
    | Literal.neg v => (StrEnc.enc 1) ++ (StrEnc.enc v)
  maxDepth := 1
  fieldDepths := #[#[StrEnc.maxDepth ℕ], #[StrEnc.maxDepth ℕ]]
  ctorIndex
    | Literal.pos _ => 0
    | Literal.neg _ => 1
  encFields
    | Literal.pos v => StrEnc.enc v
    | Literal.neg v => StrEnc.enc v
  hEncInner := by sorry
  hDepth := sorry
  hInj := sorry

abbrev Clause := List Literal

abbrev Formula := List Clause

--- The list of all positive variables.
abbrev Assignments := List Var

inductive SATInput where
  | mk (formula : Formula) (assignment : Assignments)

instance : StrEnc SATInput where
  encInner
    | SATInput.mk f a => (StrEnc.enc 0) ++ (StrEnc.enc f) ++ (StrEnc.enc a)
  maxDepth := StrEnc.maxDepth Formula + 1
  fieldDepths :=
    #[#[StrEnc.maxDepth Formula, StrEnc.maxDepth Assignments]]
  ctorIndex := fun _ => 0
  encFields
    | SATInput.mk f a => StrEnc.enc f ++ StrEnc.enc a
  hEncInner := by sorry
  hDepth := sorry
  hInj := sorry

open Routines in
/--
A Turing machine that decides satisfiability given a `SATInput` value on tape 0.
Uses 3 tapes:
- Tape 0: the input (formula and assignment)
- Tape 1: the assignment (copied from input)
- Tape 2: intermediate boolean results

The algorithm:
1. Copy the assignment to tape 1
2. For all clauses, check that there exists some literal that is satisfied
3. Clean up and leave the result on tape 2
-/
def sat : MultiTapeTM 3 Char :=
  -- Copy the assignment to tape 1 and move to the start of the formula on tape 0
  toArg SATInput 0 1 0 ;ₜ copyEnc Assignments 0 1 ;ₜ
  outOfArg SATInput 0 1 0 ;ₜ toArg SATInput 0 0 0 ;ₜ
  -- Check that for all clauses on tape 0…
  all_list Clause 0
    -- …there is some literal…
    (any_list Literal 0
      -- …that is satisfied by the assignment
      (Routines.case Literal 0
        [ -- positive literal: check if the variable is in the assignment
          contains Var 0 1 2,
          -- negative literal: check and negate
          contains Var 0 1 2 ;ₜ negateBool 2
        ])
      2)
    2 ;ₜ
  -- Cleanup
  outOfArg SATInput 0 0 0 ;ₜ
  erase Assignments 1

end Satisfiability

end Turing
