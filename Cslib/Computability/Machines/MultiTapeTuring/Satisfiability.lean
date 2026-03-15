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
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed

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

open Routines


/--
A Turing machine that decides satisfiability given a `SATInput` value on tape 0.
Uses 5 tapes:
- Tape 0: the input (formula and assignment)
- Tape 1: the assignment (copied from input)
- Tape 2: intermediate boolean results

The algorithm:
1. Copy the assignment to tape 1
2. For all clauses, check that there exists some literal that is satisfied
3. Clean up and leave the result on tape 2
-/
def sat_verify_core : MultiTapeTM 5 Char :=
  all_list
    -- …there is some literal…
    (any_list
      -- …that is satisfied by the assignment.
      -- Navigate to ctor index of literal (first element of Data.list)
      (toElem 0 0 ;ₜ
        -- Dispatch on ctor index
        case_num 0
          [ -- positive literal (ctorIdx=0): skip to var, check membership
            toElem 1 0 ;ₜ contains 1 0 2 (by decide) ;ₜ outOfList 0,
            -- negative literal (ctorIdx=1): skip to var, check membership, negate
            toElem 1 0 ;ₜ contains 1 0 2 (by decide) ;ₜ outOfList 0 ;ₜ negateBool 2
          ])
      0 2 (by decide))
    0 2 (by decide)


public def sat : MultiTapeTM 5 Char :=
  -- Navigate to assignments (arg 1) and copy to tape 1
  toElem 1 0 ;ₜ copyEnc 0 1 ;ₜ outOfList 0 ;ₜ
  -- Navigate to formula (arg 0)
  toElem 0 0 ;ₜ
  sat_verify_core ;ₜ
  -- Cleanup
  outOfList 0 ;ₜ
  erase 1


-- TODO continue here:
-- We would like the function below to be typed.
-- What happens if the input is not a valid encoding? We cannot check that at runtime (at least
-- it would create additional cost), so we have to put that as a precondition of
-- "computes_function_read_read_push". Is that fine?


lemma sat_verify_core_semantics :
  computes_function_read_read_push
    sat_verify_core
    (fun formula assignments => evalFormula assignments formula)
    0 1 2 (by decide) := by
  sorry

end Satisfiability

end Turing
