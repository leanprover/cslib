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
  right i ;ₜ while_neq ')' i (tm ;ₜ skipRight i) ;ₜ
    while_neq '(' i (skipLeft i)

/-- Helper: the forward loop `while_neq ')' i (tm ;ₜ skipRight i)` iterates `tm`
    over the remaining list elements and folds the result onto tape `j`.
    Tape `i` has path `[idx]` into `StrEnc.toData ls`. -/
private lemma run_list_forward {k : ℕ} {i j : Fin k} (h_neq : i ≠ j)
    {α β : Type} [StrEnc α] [StrEnc β]
    {tm : MultiTapeTM k Char}
    {f : α → β → β}
    (h_comp : computes_function_read_update' tm f i j h_neq)
    (ls : List α) (idx : ℕ) (h_idx : idx ≤ ls.length)
    (acc : β) (views : Fin k → TapeView)
    (h_data : (views i).data = StrEnc.toData ls)
    (h_path : (views i).path = [idx])
    (h_j : views j = TapeView.ofEnc acc) :
    (while_neq ')' i (tm ;ₜ skipRight i)).eval_struct views = .some
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

/-- Helper: the backward loop `while_neq '(' i (skipLeft i)` restores
    tape `i` from path `[n]` to path `[]`. -/
private lemma run_list_backward {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} {n : ℕ}
    (h_path : (views i).path = [n]) :
    (while_neq '(' i (skipLeft i)).eval_struct views = .some
      (Function.update views i ⟨(views i).data, [], sorry⟩) := by
  -- The loop iterates n times: each skipLeft moves from [m+1] to [m].
  -- When path = [0], the head character is '(' and the loop exits.
  sorry

/-- If `tm` computes a function `f` that acts like a folding function, the result of using
`run_list` is a fold with accumulator on tape `j`. -/
@[simp, grind =>]
public lemma run_list_fold {k : ℕ} {i j : Fin k} {h_neq : i ≠ j}
  {α β : Type} [StrEnc α] [StrEnc β]
  {tm : MultiTapeTM k Char}
  (f : α → β → β)
  (h_comp : computes_function_read_update' tm f i j h_neq) :
  computes_function_read_update' (α := List α) (run_list i tm)
    (fun ls => ls.foldl (fun acc d => f d acc)) i j h_neq := by
  intro ls y views h_ls h_y
  simp only [run_list, seq_eval_struct]
  -- Step 1: `right i` enters the list, moving to path [0]
  -- h_ls : (views i).current = StrEnc.toData ls = Data.list (ls.map StrEnc.toData)
  have h_valid : ((views i).current.atPath [0]).isSome := by
    simp only [h_ls, StrEnc.toData, Data.atPath]
    sorry -- needs: (Data.list (ls.map StrEnc.toData)).atPath [0] is valid for nonempty,
          -- and for empty lists, the right char after `(` is `)` so while_neq exits
  rw [right_on_nonempty_list h_valid]
  simp only [Part.bind_some]
  -- After right: views' i has data = (views i).data, path = (views i).path ++ [0]
  -- Step 2: forward loop
  set views₁ := Function.update views i ((views i).appendPath 0 h_valid)
  have h_data₁ : (views₁ i).data = StrEnc.toData ls := by
    simp only [views₁, Function.update_self, TapeView.appendPath]
    sorry -- TapeView.appendPath preserves .data; .data depends on h_ls
  have h_path₁ : (views₁ i).path = [0] := by
    simp only [views₁, Function.update_self, TapeView.appendPath]
    sorry -- path becomes (views i).path ++ [0], and (views i).path = [] since current = toData
  have h_j₁ : views₁ j = TapeView.ofEnc y := by
    simp only [views₁, Function.update_of_ne (Ne.symm h_neq), h_y]
  have h_fwd := run_list_forward h_neq h_comp ls 0 (by omega) y views₁ h_data₁ h_path₁ h_j₁
  simp only [List.drop_zero] at h_fwd
  rw [h_fwd]
  simp only [Part.bind_some]
  -- Step 3: backward loop restores tape i to parent
  set views₂ := Function.update (Function.update views₁ j
    (TapeView.ofEnc (ls.foldl (fun a d => f d a) y)))
    i ⟨(views₁ i).data, [ls.length], sorry⟩
  have h_path₂ : (views₂ i).path = [ls.length] := by
    simp [views₂]
  have h_bwd := run_list_backward h_path₂
  rw [h_bwd]
  -- Now need: the result equals Function.update views j (TapeView.ofEnc (fold ...))
  -- views₂ with tape i restored to path [] should equal
  -- views with just tape j updated
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
  -- intro ls views h_ls
  -- have h_inner : computes_function_read_update (tm ;ₜ combineOrUpdate j) (fun d tv =>
  --   let b := f d
  --   let acc := (tv.current.at? 0).map (fun d => d = StrEnc.toData true) = some true
  --   if b then tv.pushList (StrEnc.toData true)
  --   else if acc then tv
  --   else tv.pushList (StrEnc.toData false)) i j h_neq := by
  --  grind [combineOrUpdate]
  sorry

@[simp, grind =>]
public theorem any_list.computes_fun_twoary {k : ℕ} {i j r : Fin k}
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

@[simp, grind =>]
public theorem any_list.computes_fun' {k : ℕ} {i j : Fin k}
    (h_neq : i ≠ j)
    {α : Type} [StrEnc α]
    {tm : MultiTapeTM k Char}
    {f : α → Bool}
    (h_comp : computes_function_read_push' tm f i j h_neq) :
    computes_function_read_push'
      (any_list tm i j h_neq)
      (fun ls : List α => ls.any f)
      i j h_neq := by
  intro ls out_ls views h_ls h_out_ls
  have h_inner : computes_function_read_update' (tm ;ₜ combineOrUpdate j)
      (fun x out_ls => (f x || out_ls.head? == some true) :: out_ls.tail) i j h_neq := by
    intro x out_ls views h_acc h_out_ls
    simp [h_comp x out_ls views h_acc h_out_ls,
      combineOrUpdate.computes_fun ((f x) :: out_ls), List.head?_eq_getElem?]
  simp only [any_list, Bool.toData, seq_eval_struct, pushList_eval_struct, Part.coe_some,
    Part.bind_some]
  rw [(run_list_fold _ h_inner ls (false :: out_ls) _ (by simp [h_neq, h_ls])
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
