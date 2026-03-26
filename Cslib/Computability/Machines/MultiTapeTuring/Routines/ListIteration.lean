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
@[simp, grind =>]
public lemma run_list_fold {k : ℕ} (i j : Fin k) (h_neq : i ≠ j)
  {α : Type} [StrEnc α]
  {tm : MultiTapeTM k Char}
  (f : α → TapeView → TapeView)
  (h_comp : computes_function_read_update tm f i j h_neq) :
  computes_function_read_update (α := List α) (run_list i tm)
    (fun ls => ls.foldl (fun acc d => f d acc)) i j h_neq := by
  sorry

public def any_list {k : ℕ}
    (tm : MultiTapeTM k Char) (i j : Fin k) (_h_neq : i ≠ j) : MultiTapeTM k Char :=
  pushList (StrEnc.toData false) j ;ₜ run_list i (tm ;ₜ combineOrUpdate j)

@[simp, grind =>]
public theorem any_list.computes_fun {k : ℕ} {i j : Fin k}
    (h_neq : i ≠ j)
    {α : Type} [StrEnc α]
    {tm : MultiTapeTM k Char}
    {f : α → Bool}
    (h_comp : computes_function_read_push tm f i j h_neq) :
    computes_function_read_push (α := List α)
      (any_list tm i j h_neq)
      (fun ls => ls.any f)
      i j h_neq := by
  sorry

@[simp, grind =>]
public theorem any_list.computes_fun' {k : ℕ} {i j r : Fin k}
    {α β : Type} [StrEnc α] [StrEnc β]
    (h_neq : [i, j, r].get.Injective)
    {tm : MultiTapeTM k Char}
    {f : α → β → Bool}
    (h_comp : computes_function_read_read_push tm f i j r h_neq) :
    computes_function_read_read_push (α := List α)
      (any_list tm i r (by sorry))
      (fun ls y => ls.any (fun d => f d y))
      i j r h_neq := by
  sorry

/-- Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
    value to tape `tmp`, and compute the logical AND of the results across the list.
    Uses tape `tmp` for intermediate results and accumulates on tape `j`. -/
public def all_list {k : ℕ}
    (tm : MultiTapeTM k Char)
    (i j : Fin k) (h_neq : i ≠ j) : MultiTapeTM k Char :=
  any_list (tm ;ₜ negateBool j) i j h_neq ;ₜ negateBool j

@[simp, grind =>]
public theorem all_list.computes_fun {k : ℕ} (i j : Fin k)
    (h_neq : i ≠ j)
    {α : Type} [StrEnc α]
    {tm : MultiTapeTM k Char}
    {f : α → Bool}
    (h_comp : computes_function_read_push tm f i j h_neq) :
    computes_function_read_push
      (all_list tm i j h_neq)
      (List.all · f)
      i j h_neq := by
  simp only [all_list, List.all_eq_not_any_not]
  grind

@[simp, grind =>]
public theorem all_list.computes_fun' {k : ℕ} {i j r : Fin k}
    {α β : Type} [StrEnc α] [StrEnc β]
    (h_neq : [i, j, r].get.Injective)
    {tm : MultiTapeTM k Char}
    {f : α → β → Bool}
    (h_comp : computes_function_read_read_push tm f i j r h_neq) :
    computes_function_read_read_push (α := List α)
      (all_list tm i r (by intro h; grind))
      (fun ls y => ls.all (fun d => f d y))
      i j r h_neq := by
  simp only [all_list, List.all_eq_not_any_not]
  grind

/-- Check if the value on tape `j` is contained in the list on tape `i`
    and store the boolean result on tape `result`. -/
public def contains {k : ℕ}
    (i j result : Fin k) (_inj : [i, j, result].get.Injective) : MultiTapeTM k Char :=
  any_list (isEq i j result) i result (by sorry)

@[simp, grind =>]
public lemma contains.computes_fun {k : ℕ}
    {α : Type} [BEq α] [StrEnc α]
    {i j result : Fin k}
    (h_inj : [i, j, result].get.Injective) :
  computes_function_read_read_push
    (contains i j result h_inj)
    (fun (ls : List α) x => ls.contains x)
    i j result h_inj := by
  simp only [List.contains_eq_any_beq]
  let a := isEq.computes_fun (α := α) i j result h_inj
  grind [contains]


-- @[simp]
-- public lemma contains_eval_struct {k : ℕ} {i j result : Fin k}
--     (h_inj : [i, j, result].get.Injective)
--     {views : Fin k → TapeView} :
--   (contains i j result h_inj).eval_struct views = some (Function.update views result ((do
--     let ls <- (views i).currentList
--     let item <- (views j).current
--     return (views result).pushList (StrEnc.toData (ls.contains item))
--   ).getD (views result))) := by
--   have x := contains.computes_fun h_inj views
--   simp at x
--   sorry


end Routines
end Turing
