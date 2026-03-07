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

section SATInput_tape_lemmas

/-- `toArg SATInput 0 0` positions the head at the formula field. -/
@[simp]
lemma toArg_tape_SATInput_0 {f : Formula} {a : Assignments} {r : List Char} :
    Routines.toArg_tape SATInput 0 0
        (BiTape.mk₁ (StrEnc.enc (SATInput.mk f a) ++ r)) =
      BiTape.mk₂ ((StrEnc.enc (0 : ℕ)).reverse ++ ['('])
        (StrEnc.enc f ++ StrEnc.enc a ++ [')'] ++ r) := by sorry

/-- `toArg SATInput 0 1` positions the head at the assignment field. -/
@[simp]
lemma toArg_tape_SATInput_1 {f : Formula} {a : Assignments} {r : List Char} :
    Routines.toArg_tape SATInput 0 1
        (BiTape.mk₁ (StrEnc.enc (SATInput.mk f a) ++ r)) =
      BiTape.mk₂ ((StrEnc.enc f).reverse ++ (StrEnc.enc (0 : ℕ)).reverse ++ ['('])
        (StrEnc.enc a ++ [')'] ++ r) := by sorry

/-- `copyEnc_tape Assignments` on the positioned tape reads the assignment. -/
@[simp]
lemma copyEnc_tape_Assignments {a : Assignments} {prefix_ suffix_ : List Char}
    {rⱼ : List Char} :
    Routines.copyEnc_tape Assignments
      (BiTape.mk₂ prefix_ (StrEnc.enc a ++ suffix_))
      (BiTape.mk₁ rⱼ) =
    BiTape.mk₁ (StrEnc.enc a ++ rⱼ) := by sorry

/-- `erase_tape Assignments` on a tape with an encoded assignment removes it. -/
@[simp]
lemma erase_tape_Assignments {a : Assignments} {r : List Char} :
    Routines.erase_tape Assignments
      (BiTape.mk₁ (StrEnc.enc a ++ r)) =
    BiTape.mk₁ r := by sorry

end SATInput_tape_lemmas

/-- Evaluate a literal given a list of positive-variable assignments. -/
def evalLiteral (a : Assignments) : Literal → Bool
  | Literal.pos v => a.contains v
  | Literal.neg v => !(a.contains v)

/-- Evaluate a clause (disjunction of literals). -/
def evalClause (a : Assignments) (c : Clause) : Bool :=
  c.any (evalLiteral a)

/-- Evaluate a formula (conjunction of clauses). -/
def evalFormula (a : Assignments) (f : Formula) : Bool :=
  f.all (evalClause a)

/--
The main theorem: `sat` decides satisfiability.
Given a `SATInput` containing a formula and an assignment on tape 0,
`sat` produces `enc(evalFormula assignment formula)` on tape 2,
with tape 0 restored and tape 1 erased.
-/
theorem sat_eval
    {input : SATInput}
    {tapes : Fin 3 → BiTape Char}
    (h_tape0 : tapes 0 = BiTape.mk₁ (StrEnc.enc input))
    (h_tape1 : tapes 1 = BiTape.mk₁ [])
    (h_tape2 : tapes 2 = BiTape.mk₁ []) :
    sat.eval tapes = .some
      (Function.update
        (Function.update tapes 0 (BiTape.mk₁ (StrEnc.enc input)))
        2 (BiTape.mk₁ (StrEnc.enc (match input with
          | SATInput.mk f a => evalFormula a f)))) := by
  obtain ⟨formula, assignment⟩ := input
  simp only [evalFormula]
  unfold sat
  -- Step 1: Resolve all .eval calls via unconditional simp lemmas
  simp only [MultiTapeTM.seq_eval, Routines.part_some_bind_eq,
    Routines.toArg_eval, Routines.copyEnc_eval, Routines.outOfArg_eval,
    Routines.all_list_eval, Routines.erase_eval,
    Routines.Function.update_update]
  -- Step 2: Resolve Function.update lookups and substitute known tape values,
  -- then reduce the *_tape functions via SATInput-specific simp lemmas
  simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),
    Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2),
    Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1),
    h_tape0, h_tape1, h_tape2,
    toArg_tape_SATInput_0, toArg_tape_SATInput_1,
    copyEnc_tape_Assignments, erase_tape_Assignments,
    Routines.outOfArg_toArg_tape,
    Routines.Function.update_update]
  sorry

end Satisfiability

end Turing
