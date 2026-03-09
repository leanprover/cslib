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

/-- After `run_list i (tm ;ₜ combineOr tmp j)` processes a list `ds` on tape `i`,
    with an initial boolean accumulator `b₀` on tape `j` and empty tape `tmp`,
    the result on tape `j` is `enc(ds.any f || b₀)`, where `f` is the boolean
    function computed by `tm` (writing its result to tape `tmp`).
    Tape `i` is restored to its original state. -/
@[simp]
public lemma run_list_combineOr_eval {i j tmp : Fin k}
    (h_ne_ij : i ≠ j) (h_ne_it : i ≠ tmp) (h_ne_jt : j ≠ tmp)
    {tm : MultiTapeTM k Char}
    {ds : List Data} {f : Data → Bool} {b₀ : Bool}
    {tapes : Fin k → BiTape Char}
    {r_i : List Char}
    (h_tape_i : tapes i = BiTape.mk₁ (Data.enc (Data.list ds) ++ r_i))
    (h_tape_j : tapes j = BiTape.mk₁ (StrEnc.enc b₀))
    (h_tape_tmp : tapes tmp = BiTape.mk₁ [])
    (h_halts : ∀ tapes,
      (tm ;ₜ combineOr tmp j ;ₜ skipRight i).HaltsOn tapes)
    (h_tm : ∀ (d : Data) (t : Fin k → BiTape Char)
      (l r : List Char),
      t i = BiTape.mk₂ l (Data.enc d ++ r) →
      t tmp = BiTape.mk₁ [] →
      ∃ t', tm.eval t = .some t' ∧ t' i = t i ∧
        t' tmp = BiTape.mk₁ (StrEnc.enc (f d))) :
    (run_list i (tm ;ₜ combineOr tmp j)).eval tapes = .some (Function.update tapes j
      (BiTape.mk₁ (StrEnc.enc (ds.any f || b₀)))) := by sorry

/-- Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
    value to tape `tmp`, and compute the logical OR of the results across the list.
    Uses tape `tmp` for intermediate results and accumulates on tape `j`.
    `any_list i tm j tmp = put false j ;ₜ run_list i (tm ;ₜ combineOr tmp j)` -/
public def any_list {k : ℕ} (i : Fin k)
    (tm : MultiTapeTM k Char) (j tmp : Fin k) : MultiTapeTM k Char :=
  put (StrEnc.toData false) j ;ₜ run_list i (tm ;ₜ combineOr tmp j)

/-- The result on tape `j` after running `any_list i tm j tmp` on `tapes`.
    Use simp lemmas like `any_list_result_spec` to reduce this for specific inputs. -/
public noncomputable def any_list_result {k : ℕ}
    (i : Fin k) (tm : MultiTapeTM k Char) (j tmp : Fin k)
    (tapes : Fin k → BiTape Char) : BiTape Char := sorry

/-- Unconditional simp lemma: `any_list` always produces an update to tape `j`.
    The actual content of tape `j` is described by `any_list_result`, which has its
    own simp rules for specific inputs. -/
@[simp]
public lemma any_list_eval {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {tapes : Fin k → BiTape Char} :
    (any_list i tm j tmp).eval tapes = .some (Function.update tapes j
      (any_list_result i tm j tmp tapes)) := by sorry

/-- Reduce `any_list_result` when the list on tape `i` and the function computed by
    `tm` are known. The inner `tm` writes its boolean result to tape `tmp`. -/
@[simp]
public lemma any_list_result_spec {i j tmp : Fin k}
    (h_ne_ij : i ≠ j) (h_ne_it : i ≠ tmp) (h_ne_jt : j ≠ tmp)
    {tm : MultiTapeTM k Char}
    {ds : List Data} {f : Data → Bool}
    {tapes : Fin k → BiTape Char}
    {r_i : List Char}
    (h_tape_i : tapes i = BiTape.mk₁ (Data.enc (Data.list ds) ++ r_i))
    (h_tape_j : tapes j = BiTape.mk₁ [])
    (h_tape_tmp : tapes tmp = BiTape.mk₁ [])
    (h_halts : ∀ tapes, (tm ;ₜ combineOr tmp j ;ₜ skipRight i).HaltsOn tapes)
    (h_tm : ∀ (d : Data) (t : Fin k → BiTape Char)
      (l r : List Char),
      t i = BiTape.mk₂ l (Data.enc d ++ r) →
      t tmp = BiTape.mk₁ [] →
      ∃ t', tm.eval t = .some t' ∧ t' i = t i ∧
        t' tmp = BiTape.mk₁ (StrEnc.enc (f d))) :
    any_list_result i tm j tmp tapes =
      BiTape.mk₁ (StrEnc.enc (ds.any f)) := by sorry

/-- Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
    value to tape `tmp`, and compute the logical AND of the results across the list.
    Uses tape `tmp` for intermediate results and accumulates on tape `j`. -/
public def all_list {k : ℕ} (i : Fin k)
    (tm : MultiTapeTM k Char) (j tmp : Fin k) : MultiTapeTM k Char :=
  any_list i (tm ;ₜ negateBool tmp) j tmp ;ₜ negateBool j

/-- The result on tape `j` after running `all_list i tm j tmp` on `tapes`. -/
public noncomputable def all_list_result {k : ℕ}
    (i : Fin k) (tm : MultiTapeTM k Char) (j tmp : Fin k)
    (tapes : Fin k → BiTape Char) : BiTape Char := sorry

/-- Unconditional simp lemma: `all_list` always produces an update to tape `j`. -/
@[simp]
public lemma all_list_eval {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {tapes : Fin k → BiTape Char} :
    (all_list i tm j tmp).eval tapes = .some (Function.update tapes j
      (all_list_result i tm j tmp tapes)) := by sorry

/-- Reduce `all_list_result` when the list on tape `i` and the function computed by
    `tm` are known. -/
@[simp]
public lemma all_list_result_spec {i j tmp : Fin k}
    (h_ne_ij : i ≠ j) (h_ne_it : i ≠ tmp) (h_ne_jt : j ≠ tmp)
    {tm : MultiTapeTM k Char}
    {ds : List Data} {f : Data → Bool}
    {tapes : Fin k → BiTape Char}
    {r_i : List Char}
    (h_tape_i : tapes i = BiTape.mk₁ (Data.enc (Data.list ds) ++ r_i))
    (h_tape_j : tapes j = BiTape.mk₁ [])
    (h_tape_tmp : tapes tmp = BiTape.mk₁ [])
    (h_halts : ∀ tapes,
      (tm ;ₜ negateBool tmp ;ₜ combineOr tmp j ;ₜ skipRight i).HaltsOn tapes)
    (h_tm : ∀ (d : Data) (t : Fin k → BiTape Char)
      (l r : List Char),
      t i = BiTape.mk₂ l (Data.enc d ++ r) →
      t tmp = BiTape.mk₁ [] →
      ∃ t', tm.eval t = .some t' ∧ t' i = t i ∧
        t' tmp = BiTape.mk₁ (StrEnc.enc (f d))) :
    all_list_result i tm j tmp tapes =
      BiTape.mk₁ (StrEnc.enc (ds.all f)) := by sorry

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
    (h_data_i : (views i).data = some (Data.list ds))
    (h_empty_j : (views j).data = none)
    (h_empty_tmp : (views tmp).data = none)
    (h_tm : ∀ (d : Data) (vs : Fin k → TapeView),
      (vs i).current = some d →
      (vs tmp).data = none →
      ∃ vs', tm.eval_struct vs = some vs' ∧
        (vs' i) = (vs i) ∧
        (vs' tmp) = ⟨some (StrEnc.toData (f d)), []⟩) :
    any_list_struct_result i tm j tmp views =
      ⟨some (StrEnc.toData (ds.any f)), []⟩ := by sorry

/-- When tape `i` holds a `Data.num` (not a list), `run_list` does not iterate,
    so `any_list` simply returns `false`. -/
@[simp]
public lemma any_list_struct_result_num {k : ℕ} {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    {n : ℕ}
    (h_path_i : (views i).path = [])
    (h_data_i : (views i).data = some (Data.num n))
    (h_empty_j : (views j).data = none) :
    any_list_struct_result i tm j tmp views =
      ⟨some (StrEnc.toData false), []⟩ := by sorry

/-- When tape `i` is empty, `run_list` does not iterate,
    so `any_list` simply returns `false`. -/
@[simp]
public lemma any_list_struct_result_empty {k : ℕ} {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    (h_data_i : (views i).data = none)
    (h_empty_j : (views j).data = none) :
    any_list_struct_result i tm j tmp views =
      ⟨some (StrEnc.toData false), []⟩ := by sorry

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
    (h_data_i : (views i).data = some (Data.list ds))
    (h_empty_j : (views j).data = none)
    (h_empty_tmp : (views tmp).data = none)
    (h_tm : ∀ (d : Data) (vs : Fin k → TapeView),
      (vs i).current = some d →
      (vs tmp).data = none →
      ∃ vs', tm.eval_struct vs = some vs' ∧
        (vs' i) = (vs i) ∧
        (vs' tmp) = ⟨some (StrEnc.toData (f d)), []⟩) :
    all_list_struct_result i tm j tmp views =
      ⟨some (StrEnc.toData (ds.all f)), []⟩ := by sorry

/-- When tape `i` holds a `Data.num` (not a list), `run_list` does not iterate,
    so `all_list` returns `true` (vacuous conjunction). -/
@[simp]
public lemma all_list_struct_result_num {k : ℕ} {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    {n : ℕ}
    (h_path_i : (views i).path = [])
    (h_data_i : (views i).data = some (Data.num n))
    (h_empty_j : (views j).data = none) :
    all_list_struct_result i tm j tmp views =
      ⟨some (StrEnc.toData true), []⟩ := by sorry

/-- When tape `i` is empty, `run_list` does not iterate,
    so `all_list` returns `true` (vacuous conjunction). -/
@[simp]
public lemma all_list_struct_result_empty {k : ℕ} {i j tmp : Fin k}
    {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    (h_data_i : (views i).data = none)
    (h_empty_j : (views j).data = none) :
    all_list_struct_result i tm j tmp views =
      ⟨some (StrEnc.toData true), []⟩ := by sorry

/-- `contains i j result tmp` checks if the current element of tape `i` appears
    in the list on tape `j`, storing the boolean result on tape `result`. -/
@[simp]
public lemma contains_eval_struct {k : ℕ} {i j result tmp : Fin k}
    {views : Fin k → TapeView}
    {d : Data} {ds : List Data}
    (h_current_i : (views i).current = some d)
    (h_path_j : (views j).path = [])
    (h_data_j : (views j).data = some (Data.list ds))
    (h_empty_r : (views result).data = none)
    (h_empty_tmp : (views tmp).data = none) :
    (contains i j result tmp).eval_struct views = some
      (Function.update views result
        ⟨some (StrEnc.toData (decide (d ∈ ds))), []⟩) := by sorry

/-- When tape `j` holds a `Data.num` (not a list), `contains` returns `false`. -/
@[simp]
public lemma contains_eval_struct_num {k : ℕ} {i j result tmp : Fin k}
    {views : Fin k → TapeView}
    {n : ℕ}
    (h_path_j : (views j).path = [])
    (h_data_j : (views j).data = some (Data.num n))
    (h_empty_r : (views result).data = none) :
    (contains i j result tmp).eval_struct views = some
      (Function.update views result
        ⟨some (StrEnc.toData false), []⟩) := by sorry

/-- When tape `j` is empty, `contains` returns `false`. -/
@[simp]
public lemma contains_eval_struct_empty {k : ℕ} {i j result tmp : Fin k}
    {views : Fin k → TapeView}
    (h_data_j : (views j).data = none)
    (h_empty_r : (views result).data = none) :
    (contains i j result tmp).eval_struct views = some
      (Function.update views result
        ⟨some (StrEnc.toData false), []⟩) := by sorry

end Routines
end Turing
