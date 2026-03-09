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

/-- Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
    value to tape `tmp`, and compute the logical OR of the results across the list.
    Uses tape `tmp` for intermediate results and accumulates on tape `j`.
    `any_list i tm j tmp = put false j ;ₜ run_list i (tm ;ₜ combineOr tmp j)` -/
public def any_list {k : ℕ} (i : Fin k)
    (tm : MultiTapeTM k Char) (j tmp : Fin k) : MultiTapeTM k Char :=
  put (StrEnc.toData false) j ;ₜ run_list i (tm ;ₜ combineOr tmp j)

/-- Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
    value to tape `tmp`, and compute the logical AND of the results across the list.
    Uses tape `tmp` for intermediate results and accumulates on tape `j`. -/
public def all_list {k : ℕ} (i : Fin k)
    (tm : MultiTapeTM k Char) (j tmp : Fin k) : MultiTapeTM k Char :=
  any_list i (tm ;ₜ negateBool tmp) j tmp ;ₜ negateBool j

/-- Check if the value on tape `i` is contained in the list on tape `j`
    and store the boolean result on tape `result`.
    Uses tape `tmp` for intermediate comparisons. -/
public def contains {k : ℕ}
    (i j result tmp : Fin k) : MultiTapeTM k Char :=
  any_list j (isEq i j tmp) result tmp

-- ═══════════════════════════════════════════════════════════════════════════
-- eval_struct lemmas: List iteration
-- ═══════════════════════════════════════════════════════════════════════════

/-- The result on tape `j` after running `any_list i tm j tmp` on `views`.
    Use `any_list_struct_result_spec` to reduce for specific inputs. -/
public noncomputable def any_list_struct_result {k : ℕ}
    (i : Fin k) (tm : MultiTapeTM k Char) (j tmp : Fin k)
    (views : Fin k → TapeView) : TapeView := sorry

/-- `any_list i tm j tmp` always updates tape `j` with the computed result.
    The actual value is described by `any_list_struct_result`. -/
@[simp]
public lemma any_list_eval_struct {k : ℕ} {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView} :
    (any_list i tm j tmp).eval_struct views = some
      (Function.update views j
        (any_list_struct_result i tm j tmp views)) := by sorry

/-- Reduce `any_list_struct_result` when the list and element function are known.
    `tm` must compute `f(d)` for each element `d` and write the boolean result
    to tape `tmp`, leaving tape `i` unchanged. -/
@[simp]
public lemma any_list_struct_result_spec {k : ℕ} {i j tmp : Fin k}
    (h_ne_ij : i ≠ j) (h_ne_it : i ≠ tmp) (h_ne_jt : j ≠ tmp)
    {tm : MultiTapeTM k Char}
    {ds : List Data} {f : Data → Bool}
    {views : Fin k → TapeView}
    (h_path_i : (views i).path = [])
    (h_data_i : (views i).data = Data.list ds)
    (h_empty_j : (views j).data = Data.list [])
    (h_empty_tmp : (views tmp).data = Data.list [])
    (h_tm : ∀ (d : Data) (vs : Fin k → TapeView),
      (vs i).current = some d →
      (vs tmp).data = Data.list [] →
      ∃ vs', tm.eval_struct vs = some vs' ∧
        (vs' i) = (vs i) ∧
        (vs' tmp) = ⟨StrEnc.toData (f d), []⟩) :
    any_list_struct_result i tm j tmp views =
      ⟨StrEnc.toData (ds.any f), []⟩ := by sorry

/-- When tape `i` holds a `Data.num` (not a list), `run_list` does not iterate,
    so `any_list` simply returns `false`. -/
@[simp]
public lemma any_list_struct_result_num {k : ℕ} {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    {n : ℕ}
    (h_path_i : (views i).path = [])
    (h_data_i : (views i).data = Data.num n)
    (h_empty_j : (views j).data = Data.list []) :
    any_list_struct_result i tm j tmp views =
      ⟨StrEnc.toData false, []⟩ := by sorry

/-- When tape `i` is empty, `run_list` does not iterate,
    so `any_list` simply returns `false`. -/
@[simp]
public lemma any_list_struct_result_empty {k : ℕ} {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    (h_data_i : (views i).data = Data.list [])
    (h_empty_j : (views j).data = Data.list []) :
    any_list_struct_result i tm j tmp views =
      ⟨StrEnc.toData false, []⟩ := by sorry

/-- The result on tape `j` after running `all_list i tm j tmp` on `views`. -/
public noncomputable def all_list_struct_result {k : ℕ}
    (i : Fin k) (tm : MultiTapeTM k Char) (j tmp : Fin k)
    (views : Fin k → TapeView) : TapeView := sorry

/-- `all_list i tm j tmp` always updates tape `j` with the computed result. -/
@[simp]
public lemma all_list_eval_struct {k : ℕ} {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView} :
    (all_list i tm j tmp).eval_struct views = some
      (Function.update views j
        (all_list_struct_result i tm j tmp views)) := by sorry

/-- Reduce `all_list_struct_result` when the list and element function are known.
    `tm` must compute `f(d)` for each element `d`. -/
@[simp]
public lemma all_list_struct_result_spec {k : ℕ} {i j tmp : Fin k}
    (h_ne_ij : i ≠ j) (h_ne_it : i ≠ tmp) (h_ne_jt : j ≠ tmp)
    {tm : MultiTapeTM k Char}
    {ds : List Data} {f : Data → Bool}
    {views : Fin k → TapeView}
    (h_path_i : (views i).path = [])
    (h_data_i : (views i).data = Data.list ds)
    (h_empty_j : (views j).data = Data.list [])
    (h_empty_tmp : (views tmp).data = Data.list [])
    (h_tm : ∀ (d : Data) (vs : Fin k → TapeView),
      (vs i).current = some d →
      (vs tmp).data = Data.list [] →
      ∃ vs', tm.eval_struct vs = some vs' ∧
        (vs' i) = (vs i) ∧
        (vs' tmp) = ⟨StrEnc.toData (f d), []⟩) :
    all_list_struct_result i tm j tmp views =
      ⟨StrEnc.toData (ds.all f), []⟩ := by sorry

/-- When tape `i` holds a `Data.num` (not a list), `run_list` does not iterate,
    so `all_list` returns `true` (vacuous conjunction). -/
@[simp]
public lemma all_list_struct_result_num {k : ℕ} {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    {n : ℕ}
    (h_path_i : (views i).path = [])
    (h_data_i : (views i).data = Data.num n)
    (h_empty_j : (views j).data = Data.list []) :
    all_list_struct_result i tm j tmp views =
      ⟨StrEnc.toData true, []⟩ := by sorry

/-- When tape `i` is empty, `run_list` does not iterate,
    so `all_list` returns `true` (vacuous conjunction). -/
@[simp]
public lemma all_list_struct_result_empty {k : ℕ} {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    (h_data_i : (views i).data = Data.list [])
    (h_empty_j : (views j).data = Data.list []) :
    all_list_struct_result i tm j tmp views =
      ⟨StrEnc.toData true, []⟩ := by sorry

/-- `contains i j result tmp` checks if the current element of tape `i` appears
    in the list on tape `j`, storing the boolean result on tape `result`. -/
@[simp]
public lemma contains_eval_struct {k : ℕ} {i j result tmp : Fin k}
    {views : Fin k → TapeView}
    {d : Data} {ds : List Data}
    (h_current_i : (views i).current = some d)
    (h_path_j : (views j).path = [])
    (h_data_j : (views j).data = Data.list ds)
    (h_empty_r : (views result).data = Data.list [])
    (h_empty_tmp : (views tmp).data = Data.list []) :
    (contains i j result tmp).eval_struct views = some
      (Function.update views result
        ⟨StrEnc.toData (decide (d ∈ ds)), []⟩) := by sorry

/-- When tape `j` holds a `Data.num` (not a list), `contains` returns `false`. -/
@[simp]
public lemma contains_eval_struct_num {k : ℕ} {i j result tmp : Fin k}
    {views : Fin k → TapeView}
    {n : ℕ}
    (h_path_j : (views j).path = [])
    (h_data_j : (views j).data = Data.num n)
    (h_empty_r : (views result).data = Data.list []) :
    (contains i j result tmp).eval_struct views = some
      (Function.update views result
        ⟨StrEnc.toData false, []⟩) := by sorry

/-- When tape `j` is empty, `contains` returns `false`. -/
@[simp]
public lemma contains_eval_struct_empty {k : ℕ} {i j result tmp : Fin k}
    {views : Fin k → TapeView}
    (h_data_j : (views j).data = Data.list [])
    (h_empty_r : (views result).data = Data.list []) :
    (contains i j result tmp).eval_struct views = some
      (Function.update views result
        ⟨StrEnc.toData false, []⟩) := by sorry

end Routines
end Turing
