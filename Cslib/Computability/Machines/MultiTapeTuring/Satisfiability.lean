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
public def case_literal {k : ℕ}
    (pos neg : MultiTapeTM k Char)
    (i : Fin k) :
  MultiTapeTM k Char :=
    -- Navigate to ctor index of literal (first element of Data.list)
  toElem 0 i ;ₜ
  -- Dispatch on ctor index
  case_num i
    [ -- positive literal (ctorIdx=0): skip to var, run `pos`
      toElem 1 i ;ₜ pos ;ₜ outOfList i,
      -- negative literal (ctorIdx=1): skip to var, run `neg`
      toElem 1 i ;ₜ neg ;ₜ outOfList i
    ]

@[simp]
public lemma case_literal.computes_fun {k : ℕ}
    {β γ : Type} [StrEnc β] [StrEnc γ]
    (pos neg : MultiTapeTM k Char)
    {i j r : Fin k}
    (h_inj : [i, j, r].get.Injective)
    {f_pos f_neg : Var → β → γ}
    (h_comp_pos : computes_function_read_read_push pos f_pos i j r h_inj)
    (h_comp_neg : computes_function_read_read_push neg f_neg i j r h_inj) :
  computes_function_read_read_push
    (case_literal pos neg i)
    (fun lit x => match lit with
    | Literal.pos v => f_pos v x
    | Literal.neg v => f_neg v x)
    i j r h_inj := by
  sorry


/-- Check if literal on tape 0 is satisfied by assignment on tape 1 and store result
on tape 2. -/
def sat_verify_eval_literal : MultiTapeTM 5 Char :=
  case_literal
    (contains 1 0 2 (by decide))
    (contains 1 0 2 (by decide) ;ₜ negateBool 2)
    0

lemma sat_verify_eval_literal.computes_fun :
  computes_function_read_read_push
    sat_verify_eval_literal
    (fun lit ass => evalLiteral ass lit)
    0 1 2 (by decide) := by
  let h_pos := computes_function_read_read_push_swap
    (contains.computes_fun (α := Var) (k := 5) (i := 1) (j := 0) (result := 2) (by decide))
  let h_neg := computes_function_seq₂ (by decide) h_pos negateBool.computes_head_update
  exact case_literal.computes_fun (β := Assignments) (γ := Bool) _ _ _ h_pos h_neg


def sat_verify_core : MultiTapeTM 5 Char :=
  all_list
    -- …there is some literal…
      (any_list sat_verify_eval_literal 0 2 (by decide))
    0 2 (by decide)

lemma sat_verify_core_semantics :
  computes_function_read_read_push
    sat_verify_core
    (fun formula assignments => evalFormula assignments formula)
    0 1 2 (by decide) := by
  unfold sat_verify_core evalFormula evalClause
  exact all_list.computes_fun' (by decide)
    (any_list.computes_fun' (by decide) sat_verify_eval_literal.computes_fun)


public def sat_verify : MultiTapeTM 5 Char :=
  -- Navigate to assignments (arg 1) and copy to tape 1
  toElem 1 0 ;ₜ copyEnc 0 1 (by decide) ;ₜ outOfList 0 ;ₜ
  -- Navigate to formula (arg 0)
  toElem 0 0 ;ₜ sat_verify_core ;ₜ outOfList 0 ;ₜ
  erase 1

public theorem sat_verify.computes_fun
  {views : Fin 5 → TapeView}
  (h_input : (views 0).current = some (StrEnc.toData (SATInput.mk formula assignments)))
  (h_second_empty : views 1 = TapeView.empty)
  (h_third_empty_list : views 2 = TapeView.ofList []) :
   sat_verify.eval_struct views = some (Function.update views 2
     ((views 2).pushList (StrEnc.toData (evalFormula assignments formula)))) := by
  let line₁ : MultiTapeTM 5 Char := toElem 1 0 ;ₜ copyEnc 0 1 (by decide) ;ₜ outOfList 0
  have h_line₁ : line₁.eval_struct views =
      Function.update views 1 (TapeView.ofEnc assignments) := by
    simp [line₁, h_input, TapeView.current_rev, Function.update_sort]
    rfl
  let line₂ := toElem 0 0 ;ₜ sat_verify_core ;ₜ outOfList 0
  have h_line₂ (views' : Fin 5 → TapeView) :
      (views' 0).current = some (StrEnc.toData (SATInput.mk formula assignments)) →
      (views' 1) = TapeView.ofEnc assignments →
      line₂.eval_struct views' = .some (Function.update views
        2 ((views 2).pushList (StrEnc.toData (evalFormula assignments formula)))) := by
    intro h_v1 h_v2
    simp only [seq_eval_struct, toElem_eval_struct, TapeView.toElem?, Option.bind_some,
      outOfList_eval_struct_valid, line₂]
    rw [sat_verify_core_semantics]
    · sorry
    · sorry
    · sorry
  sorry


end Satisfiability

end Turing
