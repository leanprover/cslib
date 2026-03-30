/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Boolean
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Skip
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.MultiTape
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Navigation
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.CaseDispatch

set_option autoImplicit false

namespace Turing
namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- List iteration
-- ═══════════════════════════════════════════════════════════════════════════


/-- Execute a Turing machine `tm` on every item in the Data.list on tape `i`,
    assuming the state of tape `i` is reset by `tm`. -/
public def run_list {k : ℕ} (i : Fin k) (tm : MultiTapeTM k Char) :
    MultiTapeTM k Char :=
  right i;ₜ while_neq ')' i (tm;ₜ skipRight i);ₜ outOfList i

-- TODO: clean up (ai) - we probably need lemmas about what skipRight on the last element means,
-- and that outOfList works when we are at the `)` of the list.

/-- Helper: the forward loop `while_neq ')' i (tm;ₜ skipRight i)` iterates `tm`
    over the remaining list elements and folds the result onto tape `j`.
    Tape `i` has path `[idx]` into `StrEnc.toData ls`. -/
private lemma run_list_forward {k : ℕ} {i j : Fin k} (h_neq : i ≠ j)
    {α β : Type} [StrEnc α] [StrEnc β]
    {tm : MultiTapeTM k Char}
    {f : α → β → β}
    (h_comp : computes_function_read_update' tm f i j)
    (ls : List α) (idx : ℕ) (h_idx : idx ≤ ls.length)
    (acc : β) (views : Fin k → TapeView)
    (h_data : (views i).data = StrEnc.toData ls)
    (h_path : (views i).path = [idx])
    (h_j : views j = TapeView.ofEnc acc) :
    (while_neq ')' i (tm;ₜ skipRight i)).eval_struct views = .some
      (Function.update
        (Function.update views j
          (TapeView.ofEnc (ls.drop idx |>.foldl (fun a d => f d a) acc)))
        i ⟨(views i).data, [ls.length], sorry⟩) := by
  -- Induction on the number of remaining elements (ls.length - idx).
  -- Base case: idx = ls.length → tape i is at `)`, while_neq exits immediately.
  -- Inductive step: idx < ls.length →
  --   1. tm reads ls[idx] from tape i, updates tape j to f (ls[idx]) acc
  --   2. skipRight i moves tape i to path [idx + 1]
  --   3. IH handles the remaining elements ls.drop (idx + 1)
  sorry

/-- If `tm` computes a function `f` that acts like a folding function, the result of using
`run_list` is a fold with accumulator on tape `j`. -/
@[simp, grind =>]
public lemma run_list_fold {k : ℕ} {i j : Fin k} (h_neq : i ≠ j)
  {α β : Type} [StrEnc α] [StrEnc β]
  {tm : MultiTapeTM k Char}
  (f : α → β → β)
  (h_comp : computes_function_read_update' tm f i j) :
  computes_function_read_update' (α := List α) (run_list i tm)
    (fun ls => ls.foldl (fun acc d => f d acc)) i j := by
  sorry

/-- TODO document -/
public def any_list {k : ℕ}
    (tm : MultiTapeTM k Char) (i j : Fin k) : MultiTapeTM k Char :=
  pushList (StrEnc.toData false) j;ₜ run_list i (tm;ₜ combineOrUpdate j)

@[simp, grind =>]
public theorem any_list.computes_fun {k : ℕ} {i j : Fin k}
    (h_neq : i ≠ j)
    {α : Type} [StrEnc α]
    {tm : MultiTapeTM k Char}
    {f : α → Bool}
    (h_comp : computes_function_read_push tm f i j) :
    computes_function_read_push (α := List α)
      (any_list tm i j)
      (fun ls => ls.any f)
      i j := by
  -- intro ls views h_ls
  -- have h_inner : computes_function_read_update (tm;ₜ combineOrUpdate j) (fun d tv =>
  --   let b := f d
  --   let acc := (tv.current.at? 0).map (fun d => d = StrEnc.toData true) = some true
  --   if b then tv.pushList (StrEnc.toData true)
  --   else if acc then tv
  --   else tv.pushList (StrEnc.toData false)) i j h_neq := by
  --  grind [combineOrUpdate]
  sorry

@[grind =>]
public theorem any_list.computes_fun_twoary {k : ℕ} {i j r : Fin k}
    {α β : Type} [StrEnc α] [StrEnc β]
    (h_neq : [i, j, r].get.Injective)
    {tm : MultiTapeTM k Char}
    {f : α → β → Bool}
    (h_comp : computes_function_read_read_push tm f i j r) :
    computes_function_read_read_push (α := List α)
      (any_list tm i r)
      (fun ls y => ls.any (fun d => f d y))
      i j r := by
  sorry

@[simp, grind =>]
public theorem any_list.computes_fun' {k : ℕ} {i j : Fin k}
    (h_neq : i ≠ j)
    {α : Type} [StrEnc α]
    {tm : MultiTapeTM k Char}
    {f : α → Bool}
    (h_comp : computes_function_read_push' tm f i j) :
    computes_function_read_push'
      (any_list tm i j)
      (fun ls : List α => ls.any f)
      i j := by
  intro ls out_ls views h_ls h_out_ls
  have h_inner : computes_function_read_update' (tm;ₜ combineOrUpdate j)
      (fun x out_ls => (f x || out_ls.head? == some true) :: out_ls.tail) i j := by
    intro x out_ls views h_acc h_out_ls
    simp [h_comp x out_ls views h_acc h_out_ls,
      combineOrUpdate.computes_fun ((f x) :: out_ls), List.head?_eq_getElem?]
  simp only [any_list, Bool.toData, seq_eval_struct, pushList_eval_struct, Part.coe_some,
    Part.bind_some]
  rw [(run_list_fold h_neq _ h_inner ls (false :: out_ls) _ (by simp [h_neq, h_ls])
      (by simp [StrEnc.toData, h_out_ls, TapeView.pushList]))]
  have h_any_fold : ∀ ls : List α, ∀ first,
    ls.foldl (fun acc d => ((f d) || acc.head? == some true) :: acc.tail) (first :: out_ls) =
      (first || ls.any f) :: out_ls := by
    intro ls
    induction ls with
    | nil => simp
    | cons d rest ih =>
      unfold List.foldl
      intro first
      simp [ih (f d || first)]
      grind
  simp [h_any_fold]


/-- Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
    value to tape `tmp`, and compute the logical AND of the results across the list. -/
public def all_list {k : ℕ} (tm : MultiTapeTM k Char) (i j : Fin k) : MultiTapeTM k Char :=
  any_list (tm;ₜ negateBool j) i j;ₜ negateBool j

@[simp, grind =>]
public theorem all_list.computes_fun {k : ℕ} (i j : Fin k)
    (h_neq : i ≠ j)
    {α : Type} [StrEnc α]
    {tm : MultiTapeTM k Char}
    {f : α → Bool}
    (h_comp : computes_function_read_push tm f i j) :
    computes_function_read_push
      (all_list tm i j)
      (List.all · f)
      i j := by
  simp only [all_list, List.all_eq_not_any_not]
  grind

-- TODO why does the simp linter complain here?
@[grind =>]
public theorem all_list.computes_fun_twoary {k : ℕ} {i j r : Fin k}
    {α β : Type} [StrEnc α] [StrEnc β]
    (h_neq : [i, j, r].get.Injective)
    {tm : MultiTapeTM k Char}
    {f : α → β → Bool}
    (h_comp : computes_function_read_read_push tm f i j r) :
    computes_function_read_read_push (α := List α)
      (all_list tm i r)
      (fun ls y => ls.all (fun d => f d y))
      i j r := by
  simp only [all_list, List.all_eq_not_any_not]
  grind

/-- Check if the value on tape `j` is contained in the list on tape `i`
    and store the boolean result on tape `result`. -/
public def contains {k : ℕ} (i j result : Fin k) : MultiTapeTM k Char :=
  any_list (isEq i j result) i result

-- TODO why does the simp linter complain here?
@[grind =>]
public lemma contains.computes_fun {k : ℕ}
    {α : Type} [BEq α] [StrEnc α]
    {i j result : Fin k}
    (h_inj : [i, j, result].get.Injective) :
  computes_function_read_read_push
    (contains i j result)
    (fun (ls : List α) x => ls.contains x)
    i j result := by
  simp only [List.contains_eq_any_beq]
  have := isEq.computes_fun (α := α) i j result h_inj
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

inductive FindMapState where
  | searching
  | found
  | notFound

instance : StrEnc FindMapState where
  toData
    | FindMapState.searching => StrEnc.toData 0
    | FindMapState.found => StrEnc.toData 1
    | FindMapState.notFound => StrEnc.toData 2
  fromData
    | d =>
      if d == StrEnc.toData 0 then some FindMapState.searching
      else if d == StrEnc.toData 1 then some FindMapState.found
      else if d == StrEnc.toData 2 then some FindMapState.notFound
      else none
  fromData_toData := by
    intro s
    cases s <;> simp [StrEnc.toData]

/-- Execute `tm₁` on every item in the list on tape `i`. For the first item where it
writes `true` to tape `j`, execute `tm₂`. If it never writes `true`, execute `tm₃` after
returning to the list start. -/
public def find_list {k : ℕ} (i j : Fin k) (tm₁ tm₂ tm₃ : MultiTapeTM k Char) :
    MultiTapeTM k Char :=
  replace (StrEnc.toData FindMapState.searching) j;ₜ
  right i;ₜ
  doWhileEq (StrEnc.toData FindMapState.searching) j (
    if_eq ')' i
      (replace (StrEnc.toData FindMapState.notFound) j;ₜ outOfList i)
      (tm₁;ₜ ite_enc (StrEnc.toData true).enc j
        (replace (StrEnc.toData FindMapState.found) j)
        (replace (StrEnc.toData FindMapState.searching) j;ₜ skipRight i)));ₜ
  ite_enc (StrEnc.toData FindMapState.found).enc j
    (clear j;ₜ tm₂)
    (clear j;ₜ tm₃)

public theorem find_list.computes_fun {k : ℕ} {i j : Fin k}
    (h_neq : i ≠ j)
    {α : Type} [StrEnc α]
    {tm₁ tm₂ tm₃ : MultiTapeTM k Char}
    {f : α → Bool}
    (h_comp₁ : computes_function_read_replace tm₁ f i j)
    (views : Fin k → TapeView) :
    ∀ ls : List α, (views i).current = StrEnc.toData ls →
    views j = TapeView.empty →
    (find_list i j tm₁ tm₂ tm₃).eval_struct views = match ls.findIdx? f with
      | some idx => tm₂.eval_struct (Function.update views i ((views i).appendPath idx (by sorry)))
      | none => tm₃.eval_struct views := by
  sorry

end Routines
end Turing
