/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Boolean
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Skip
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.MultiTape

namespace Turing
namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- List iteration
-- ═══════════════════════════════════════════════════════════════════════════

/-- Execute a Turing machine `tm` on every item in the Data.list on tape `i`,
    assuming the state of tape `i` is reset by `tm`. -/
public def run_list {k : ℕ} (i : Fin k) (tm : MultiTapeTM k Char) :
    MultiTapeTM k Char :=
  right i ;ₜ while_neq ')' i (tm ;ₜ skipRight i) ;ₜ
    while_neq '(' i (skipLeft i)

/-- If `tm` computes a function `f` that acts like a folding function, the result of using
`run_list` is a fold with accumulator on tape `j`. -/
@[simp]
public lemma run_list_fold {k : ℕ} (i j : Fin k) (h_neq : i ≠ j) {tm : MultiTapeTM k Char}
  (f : TapeView → Data → TapeView)
  (h_comp : ∀ views, computes_function tm f i j h_neq views)
  (views : Fin k → TapeView) :
  (run_list i tm).eval_struct views = some (Function.update views j
      (((views i).currentList.map (fun ls => ls.foldl f (views j))).getD (views j))) := by
  sorry

public def any_list {k : ℕ}
    (tm : MultiTapeTM k Char) (i j : Fin k) (_h_neq : i ≠ j) : MultiTapeTM k Char :=
  pushList (StrEnc.toData false) j ;ₜ run_list i (tm ;ₜ combineOr j)

@[simp]
public theorem any_list_eval_struct {k : ℕ} (i j : Fin k)
    (h_neq : i ≠ j)
    {tm : MultiTapeTM k Char}
    {f : Data → Bool}
    (h_comp : ∀ views, computes_function_push_bool tm f i j h_neq views)
    (views : Fin k → TapeView) :
    (any_list tm i j h_neq).eval_struct views = some (Function.update views j
      (((views i).currentList.map
        fun ls => (views j).pushList (StrEnc.toData (ls.any f))).getD (views j))) := by
  sorry

/-- Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
    value to tape `tmp`, and compute the logical AND of the results across the list.
    Uses tape `tmp` for intermediate results and accumulates on tape `j`. -/
public def all_list {k : ℕ}
    (tm : MultiTapeTM k Char)
    (i j : Fin k) (h_neq : i ≠ j) : MultiTapeTM k Char :=
  any_list (tm ;ₜ negateBool j) i j h_neq ;ₜ negateBool j

@[simp]
public theorem all_list_eval_struct {k : ℕ} (i j : Fin k)
    (h_neq : i ≠ j)
    {tm : MultiTapeTM k Char}
    {f : Data → Bool}
    (h_comp : ∀ views, computes_function_push_bool tm f i j h_neq views)
    (views : Fin k → TapeView) :
    (all_list tm i j h_neq).eval_struct views = some (Function.update views j
      (((views i).currentList.map
        fun ls => (views j).pushList (StrEnc.toData (ls.all f))).getD (views j))) := by
  sorry

/-- Check if the value on tape `j` is contained in the list on tape `i`
    and store the boolean result on tape `result`. -/
public def contains {k : ℕ}
    (i j result : Fin k) (h_inj : [i, j, result].get.Injective) : MultiTapeTM k Char :=
  any_list (isEq i j result) i result (by sorry)

@[simp]
public lemma contains_eval_struct {k : ℕ} {i j result : Fin k}
    (h_inj : [i, j, result].get.Injective)
    {views : Fin k → TapeView} :
  (contains i j result h_inj).eval_struct views = some (Function.update views result ((do
    let ls <- (views i).currentList
    let item <- (views j).current
    return (views result).pushList (StrEnc.toData (ls.contains item))
  ).getD (views result))) := by
  sorry


end Routines
end Turing
