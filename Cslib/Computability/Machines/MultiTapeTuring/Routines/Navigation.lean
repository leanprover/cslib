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
-- Argument navigation (for Data.list values)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Navigate to the `argIdx`-th element of a `Data.list` encoding on tape `i`.
    Moves past `(` and then skips `argIdx` Data elements. -/
public def toArg {k : ℕ} (argIdx : ℕ) (i : Fin k) : MultiTapeTM k Char := sorry

/-- The tape state after `toArg` — depends only on the tape being navigated. -/
public noncomputable def toArg_tape (argIdx : ℕ)
    (tape : BiTape Char) : BiTape Char := sorry

@[simp]
public lemma toArg_eval {k : ℕ} {argIdx : ℕ} {i : Fin k}
    {tapes : Fin k → BiTape Char} :
    (toArg argIdx i).eval tapes = .some
      (Function.update tapes i (toArg_tape argIdx (tapes i))) := by sorry

/-- Navigate back from the `argIdx`-th element (inverse of `toArg`). -/
public def outOfArg {k : ℕ} (argIdx : ℕ) (i : Fin k) : MultiTapeTM k Char := sorry

/-- The tape state after `outOfArg` — depends only on the tape being navigated. -/
public noncomputable def outOfArg_tape (argIdx : ℕ)
    (tape : BiTape Char) : BiTape Char := sorry

@[simp]
public lemma outOfArg_eval {k : ℕ} {argIdx : ℕ} {i : Fin k}
    {tapes : Fin k → BiTape Char} :
    (outOfArg argIdx i).eval tapes = .some
      (Function.update tapes i (outOfArg_tape argIdx (tapes i))) := by sorry

/-- `outOfArg` is the inverse of `toArg`: navigating in and back out restores the tape. -/
@[simp]
public lemma outOfArg_toArg_tape (argIdx : ℕ) (tape : BiTape Char) :
    outOfArg_tape argIdx (toArg_tape argIdx tape) = tape := by sorry

/-- `toArg argIdx i` descends into the `argIdx`-th element of the topmost
    `Data.list` on tape `i`, appending `argIdx` to the path.
    Only descends if the current element is a `Data.list` with a valid index;
    otherwise, the `TapeView` is unchanged. -/
@[simp]
public lemma toArg_eval_struct_valid {k : ℕ} {argIdx : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    {ds : List Data}
    (h_current : (views i).current = some (Data.list ds))
    (h_bound : argIdx < ds.length) :
    (toArg argIdx i).eval_struct views = some
      (Function.update views i
        ⟨(views i).data, (views i).path ++ [argIdx]⟩) := by sorry

@[simp]
public lemma toArg_eval_struct_invalid {k : ℕ} {argIdx : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    (h_invalid : ∀ ds, (views i).current = some (Data.list ds) → ds.length ≤ argIdx) :
    (toArg argIdx i).eval_struct views = some views := by sorry

/-- `outOfArg argIdx i` ascends back from the `argIdx`-th element,
    removing it from the end of the path. If the path ends with `argIdx`,
    strips it. If the path is empty or the tape is empty, does not change
    the `TapeView`. -/
@[simp]
public lemma outOfArg_eval_struct_valid {k : ℕ} {argIdx : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    {rest : List ℕ}
    (h_path : (views i).path = rest ++ [argIdx]) :
    (outOfArg argIdx i).eval_struct views = some
      (Function.update views i
        ⟨(views i).data, rest⟩) := by sorry

@[simp]
public lemma outOfArg_eval_struct_empty_path {k : ℕ} {argIdx : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    (h_path : (views i).path = []) :
    (outOfArg argIdx i).eval_struct views = some views := by sorry

@[simp]
public lemma outOfArg_eval_struct_none {k : ℕ} {argIdx : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    (h_none : (views i).data = none) :
    (outOfArg argIdx i).eval_struct views = some views := by sorry

end Routines
end Turing
