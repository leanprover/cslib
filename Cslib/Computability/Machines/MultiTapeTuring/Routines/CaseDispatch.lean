/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines

namespace Turing
namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- Case dispatch
-- ═══════════════════════════════════════════════════════════════════════════

/-- Branch on the `Data` constructor: `num_branch` if the value is a number,
    `list_branch` if it is a list. The head stays at the start of the encoding. -/
public def case_data {k : ℕ} (i : Fin k)
    (num_branch list_branch : MultiTapeTM k Char) : MultiTapeTM k Char := sorry

@[simp]
public lemma case_data_eval {k : ℕ} {i : Fin k}
    {num_branch list_branch : MultiTapeTM k Char}
    {tapes : Fin k → BiTape Char}
    {d : Data} {r : List Char}
    (h_tape : tapes i = BiTape.mk₁ (Data.enc d ++ r)) :
    (case_data i num_branch list_branch).eval tapes =
      match d with
      | Data.num _ => num_branch.eval tapes
      | Data.list _ => list_branch.eval tapes := by sorry

/-- Dispatch on the numeric value of a `Data.num` encoding.
    Reads the number `n` and runs `branches[n]`.
    The head stays at the start of the encoding. -/
public def case_num {k : ℕ} (i : Fin k)
    (branches : List (MultiTapeTM k Char)) : MultiTapeTM k Char := sorry

@[simp]
public lemma case_num_eval {k : ℕ} {i : Fin k}
    {branches : List (MultiTapeTM k Char)}
    {tapes : Fin k → BiTape Char}
    {n : ℕ} {r : List Char}
    (h_tape : tapes i = BiTape.mk₁ (Data.enc (Data.num n) ++ r))
    (h_idx : n < branches.length) :
    (case_num i branches).eval tapes = branches[n].eval tapes := by sorry

/-- `case_num` on a `false` value (encoded as `Data.num 0`) dispatches to the first branch. -/
@[simp]
public lemma case_num_false_eval {i : Fin k}
    {tm₀ : MultiTapeTM k Char} {tms : List (MultiTapeTM k Char)}
    {tapes : Fin k → BiTape Char}
    {r : List Char}
    (h_tape : tapes i = BiTape.mk₁ (StrEnc.enc false ++ r)) :
    (case_num i (tm₀ :: tms)).eval tapes = tm₀.eval tapes := by
  exact case_num_eval h_tape (by simp)

/-- `case_num` on a `true` value (encoded as `Data.num 1`) dispatches to the second branch. -/
@[simp]
public lemma case_num_true_eval {i : Fin k}
    {tm₀ tm₁ : MultiTapeTM k Char}
    {tms : List (MultiTapeTM k Char)}
    {tapes : Fin k → BiTape Char}
    {r : List Char}
    (h_tape : tapes i = BiTape.mk₁ (StrEnc.enc true ++ r)) :
    (case_num i (tm₀ :: tm₁ :: tms)).eval tapes =
      tm₁.eval tapes := by
  exact case_num_eval h_tape (by simp)

/-- `case_data i nb lb` branches on the constructor of the `Data` value.
    Runs `nb` if it is a `num`, `lb` if it is a `list`. -/
@[simp]
public lemma case_data_eval_struct {k : ℕ} {i : Fin k}
    {num_branch list_branch : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    {d : Data}
    (h_path : (views i).path = [])
    (h_data : (views i).data = some d) :
    (case_data i num_branch list_branch).eval_struct views =
      match d with
      | Data.num _ => num_branch.eval_struct views
      | Data.list _ => list_branch.eval_struct views := by sorry

/-- `case_num i branches` dispatches on the numeric value at the current position
    of tape `i`. If `currentNum` is `some n` and `n < branches.length`, runs
    `branches[n]`. Otherwise (tape empty, not a num, or out of range), does nothing. -/
@[simp]
public lemma case_num_eval_struct {k : ℕ} {i : Fin k}
    {branches : List (MultiTapeTM k Char)}
    {views : Fin k → TapeView} :
    (case_num i branches).eval_struct views =
      match (views i).currentNum with
      | some n => if h : n < branches.length then branches[n].eval_struct views else some views
      | none => some views := by sorry

/-- `case_num` on `false` (= `Data.num 0`) dispatches to the first branch. -/
@[simp]
public lemma case_num_false_eval_struct {k : ℕ} {i : Fin k}
    {tm₀ : MultiTapeTM k Char} {tms : List (MultiTapeTM k Char)}
    {views : Fin k → TapeView}
    (h_data : (views i).currentNum = some 0) :
    (case_num i (tm₀ :: tms)).eval_struct views =
      tm₀.eval_struct views := by
  simp [h_data]

/-- `case_num` on `true` (= `Data.num 1`) dispatches to the second branch. -/
@[simp]
public lemma case_num_true_eval_struct {k : ℕ} {i : Fin k}
    {tm₀ tm₁ : MultiTapeTM k Char}
    {tms : List (MultiTapeTM k Char)}
    {views : Fin k → TapeView}
    (h_data : (views i).currentNum = some 1) :
    (case_num i (tm₀ :: tm₁ :: tms)).eval_struct views =
      tm₁.eval_struct views := by
  simp [h_data]

/-- Dispatch on the numeric value of the first element of a list.
    Pops the first element from the list on tape `i`. If it is `Data.num n`
    and `n < branches.length`, runs `branches[n]` on the updated views
    (with the element removed). If the pop fails, the element is not a number,
    or the index is out of range, leaves the tape unmodified. -/
public def case_popList_num {k : ℕ} (i : Fin k)
    (branches : List (MultiTapeTM k Char)) : MultiTapeTM k Char :=
    sorry

@[simp]
public lemma case_popList_num_eval_struct {k : ℕ} {i : Fin k}
    {branches : List (MultiTapeTM k Char)}
    {views : Fin k → TapeView} :
    (case_popList_num i branches).eval_struct views =
      match (views i).popList with
      | some (Data.num n, tv') =>
        if h : n < branches.length then
          branches[n].eval_struct (Function.update views i tv')
        else some views
      | some (Data.list _, _) => some views
      | none => some views := by sorry

end Routines
end Turing
