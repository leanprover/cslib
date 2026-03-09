/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.Encoding
public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Navigation
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.MultiTape
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Erase
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.ListIteration

namespace Turing

namespace Satisfiability

public abbrev Var := ℕ

public inductive Literal where
  | pos (v : Var)
  | neg (v : Var)

public instance : StrEnc Literal where
  toData
    | Literal.pos v => Data.list [Data.num 0, Data.num v]
    | Literal.neg v => Data.list [Data.num 1, Data.num v]
  fromData
    | Data.list [Data.num 0, Data.num v] => some (Literal.pos v)
    | Data.list [Data.num 1, Data.num v] => some (Literal.neg v)
    | _ => none
  fromData_toData
    | Literal.pos _ => rfl
    | Literal.neg _ => rfl

public abbrev Clause := List Literal

public abbrev Formula := List Clause

--- The list of all positive variables.
public abbrev Assignments := List Var

public inductive SATInput where
  | mk (formula : Formula) (assignment : Assignments)

public instance : StrEnc SATInput where
  toData
    | SATInput.mk f a => Data.list [StrEnc.toData f, StrEnc.toData a]
  fromData
    | Data.list [fd, ad] => do
      let f ← StrEnc.fromData fd
      let a ← StrEnc.fromData ad
      pure (SATInput.mk f a)
    | _ => none
  fromData_toData
    | SATInput.mk f a => by simp [StrEnc.fromData_toData f, StrEnc.fromData_toData a]

/-- Evaluate a literal given a list of positive-variable assignments. -/
public def evalLiteral (a : Assignments) : Literal → Bool
  | Literal.pos v => a.contains v
  | Literal.neg v => !(a.contains v)

/-- Evaluate a clause (disjunction of literals). -/
public def evalClause (a : Assignments) (c : Clause) : Bool :=
  c.any (evalLiteral a)

/-- Evaluate a formula (conjunction of clauses). -/
public def evalFormula (a : Assignments) (f : Formula) : Bool :=
  f.all (evalClause a)

open Routines in
/--
A Turing machine that decides satisfiability given a `SATInput` value on tape 0.
Uses 5 tapes:
- Tape 0: the input (formula and assignment)
- Tape 1: the assignment (copied from input)
- Tape 2: intermediate boolean results
- Tape 3: temporary tape for inner list iteration (any_list)
- Tape 4: temporary tape for outer list iteration (all_list)

The algorithm:
1. Copy the assignment to tape 1
2. For all clauses, check that there exists some literal that is satisfied
3. Clean up and leave the result on tape 2
-/
public def sat : MultiTapeTM 5 Char :=
  -- Navigate to assignments (arg 1) and copy to tape 1
  toArg 1 0 ;ₜ copyEnc 0 1 ;ₜ outOfArg 1 0 ;ₜ
  -- Navigate to formula (arg 0)
  toArg 0 0 ;ₜ
  -- For all clauses in the formula…
  all_list 0
    -- …there is some literal…
    (any_list 0
      -- …that is satisfied by the assignment.
      -- Navigate to ctor index of literal (first element of Data.list)
      (toArg 0 0 ;ₜ
        -- Dispatch on ctor index
        case_num 0
          [ -- positive literal (ctorIdx=0): skip to var, check membership
            skipRight 0 ;ₜ contains 0 1 3 4 ;ₜ skipLeft 0 ;ₜ outOfArg 0 0,
            -- negative literal (ctorIdx=1): skip to var, check membership, negate
            skipRight 0 ;ₜ contains 0 1 3 4 ;ₜ skipLeft 0 ;ₜ outOfArg 0 0 ;ₜ negateBool 3
          ])
      2 3)
    2 4 ;ₜ
  -- Cleanup
  outOfArg 0 0 ;ₜ
  erase 1

end Satisfiability

end Turing
