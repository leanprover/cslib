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
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.ListIteration
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed

namespace Turing

namespace Satisfiability

/-- TODO document -/
public abbrev Var := ℕ

/-- TODO document -/
public inductive Literal where
  | pos (v : Var)
  | neg (v : Var)

public instance : StrEnc Literal where
  toData
    | Literal.pos v => StrEnc.toData [0, v]
    | Literal.neg v => StrEnc.toData [1, v]
  fromData d := do
    match StrEnc.fromData d with
    | some [0, v] => some (Literal.pos v)
    | some [1, v] => some (Literal.neg v)
    | _ => none
  fromData_toData
    | Literal.pos _ => by simp
    | Literal.neg _ => by simp

/-- TODO document -/
public abbrev Clause := List Literal

/-- TODO document -/
public abbrev Formula := List Clause

/-- TODO document -/
public abbrev Assignments := List Var

/-- TODO document -/
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

@[simp]
lemma SatInput_toData (formula : Formula) (assignments : Assignments) :
  StrEnc.toData (SATInput.mk formula assignments) =
    Data.list [StrEnc.toData formula, StrEnc.toData assignments] := by
  simp [StrEnc.toData]

@[simp]
lemma Literal_toData (lit : Literal) :
  StrEnc.toData lit = Data.list (
    match lit with
    | Literal.pos v => [StrEnc.toData 0, StrEnc.toData v]
    | Literal.neg v => [StrEnc.toData 1, StrEnc.toData v]) := by
  match lit with
  | Literal.pos v => rfl
  | Literal.neg v => rfl

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


/-
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

-- TODO extend this to any inductive type
/-- TODO document -/
public def case_literal {k : ℕ}
    (pos neg : MultiTapeTM k Char)
    (i : Fin k) :
  MultiTapeTM k Char :=
    -- Navigate to ctor index of literal (first element of Data.list)
  toElem 0 i;ₜ
  -- Dispatch on ctor index
  case_nat i
    [ -- positive literal (ctorIdx=0): skip to var, run `pos`
      outOfList i;ₜ toElem 1 i;ₜ pos;ₜ outOfList i,
      -- negative literal (ctorIdx=1): skip to var, run `neg`
      outOfList i;ₜ toElem 1 i;ₜ neg;ₜ outOfList i
    ]

-- TODO why does the simp linter complain here?
public lemma case_literal.computes_fun {k : ℕ}
    {β γ : Type} [StrEnc β] [StrEnc γ]
    (pos neg : MultiTapeTM k Char)
    {i j r : Fin k}
    (h_inj : [i, j, r].get.Injective)
    {f_pos f_neg : Var → β → γ}
    (h_comp_pos : computes_function_read_read_push pos f_pos i j r)
    (h_comp_neg : computes_function_read_read_push neg f_neg i j r) :
  computes_function_read_read_push
    (case_literal pos neg i)
    (fun lit x => match lit with
    | Literal.pos v => f_pos v x
    | Literal.neg v => f_neg v x)
    i j r := by
  intro lit x views h_lit h_x
  have h_neq : i ≠ r := by
    exact Function.Injective.ne h_inj (show (0 : Fin 3) ≠ 2 by decide)
  have h_ne' : i ≠ j := by
    exact Function.Injective.ne h_inj (show (0 : Fin 3) ≠ 1 by decide)
  match h : lit with
  | Literal.pos v =>
    simp [h_comp_pos v x, case_literal, h_neq, h_neq.symm, h_lit, h_ne'.symm, h_x]
  | Literal.neg v =>
    simp [h_comp_neg v x, case_literal, h_neq, h_neq.symm, h_lit, h_ne'.symm, h_x]


-- TODO why does the simp linter complain here?
public lemma case_literal.computes_fun' {k : ℕ}
    {β γ : Type} [StrEnc β] [StrEnc γ]
    (pos neg : MultiTapeTM k Char)
    {i j r : Fin k}
    (h_inj : [i, j, r].get.Injective)
    {f_pos f_neg : Var → β → γ}
    (h_comp_pos : computes_function_read_read_push' pos f_pos i j r)
    (h_comp_neg : computes_function_read_read_push' neg f_neg i j r) :
  computes_function_read_read_push'
    (case_literal pos neg i)
    (fun lit x => match lit with
    | Literal.pos v => f_pos v x
    | Literal.neg v => f_neg v x)
    i j r := by
  intro lit x ls views h_lit h_x h_ls
  have h_neq : i ≠ r := Function.Injective.ne h_inj (show (0 : Fin 3) ≠ 2 by decide)
  have h_ne' : i ≠ j := Function.Injective.ne h_inj (show (0 : Fin 3) ≠ 1 by decide)
  have h_ner : r ≠ i := by grind
  match h : lit with
  | Literal.pos v =>
    simp [h_comp_pos v x ls, case_literal, h_neq, h_neq.symm, h_lit, h_x, h_ne'.symm, h_ls]
  | Literal.neg v =>
    simp [h_comp_neg v x ls, case_literal, h_neq, h_neq.symm, h_lit, h_ne'.symm, h_x, h_ls]

/-- Check if literal on tape 0 is satisfied by assignment on tape 1 and store result
on tape 2. -/
def sat_verify_eval_literal : MultiTapeTM 5 Char :=
  case_literal
    (contains 1 0 2)
    (contains 1 0 2;ₜ negateBool 2)
    0

lemma sat_verify_eval_literal.computes_fun :
  computes_function_read_read_push
    sat_verify_eval_literal
    (fun lit ass => evalLiteral ass lit)
    0 1 2 := by
  let h_pos := computes_function_read_read_push_swap
    (contains.computes_fun (α := Var) (k := 5) (i := 1) (j := 0) (result := 2) (by decide))
  let h_neg := computes_function_seq₂ h_pos negateBool.computes_head_update
  exact case_literal.computes_fun (β := Assignments) (γ := Bool) _ _ (by decide) h_pos h_neg

def sat_verify_core : MultiTapeTM 5 Char :=
  all_list (any_list sat_verify_eval_literal 0 2) 0 2

lemma sat_verify_core_semantics :
  computes_function_read_read_push
    sat_verify_core
    (fun formula assignments => evalFormula assignments formula)
    0 1 2 := by
  unfold sat_verify_core evalFormula evalClause evalLiteral
  exact all_list.computes_fun_twoary (by decide)
    (any_list.computes_fun_twoary (by decide) sat_verify_eval_literal.computes_fun)


/-- TODO document -/
public def sat_verify : MultiTapeTM 5 Char :=
  -- TODO could also use `at_path`
  -- Navigate to assignments (arg 1) and copy to tape 1
  toElem 1 0;ₜ copyEnc 0 1;ₜ outOfList 0;ₜ
  -- Navigate to formula (arg 0)
  toElem 0 0;ₜ sat_verify_core;ₜ outOfList 0;ₜ
  replace (Data.list []) 1

public theorem sat_verify.computes_fun
  {views : Fin 5 → TapeView}
  (h_input : (views 0).current = StrEnc.toData (SATInput.mk formula assignments))
  (h_second_empty : views 1 = TapeView.empty) :
   sat_verify.eval_struct views = some (Function.update views 2
     ((views 2).pushList (StrEnc.toData (evalFormula assignments formula)))) := by
  simp [sat_verify, h_input, sat_verify_core_semantics formula assignments]
  grind


end Satisfiability

end Turing
