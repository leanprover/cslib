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

/-- Navigate to the `idx`-th element of a `Data.list` encoding on tape `i`.
Moves past `(` and then skips `idx` Data elements.
If `i` is larger than the length of the list, does nothing. -/
public def toElem {k : ℕ} (idx : ℕ) (i : Fin k) : MultiTapeTM k Char := sorry

/-- If positioned on the element of a list, navigates to the list containing it. -/
public def outOfList {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry

/-- `toElem idx i` moves to the `idx`th element of the `Data.list` currently pointed to
on tape `i`. Only descends if the current element is a `Data.list` with at least `idx` elements,
otherwise, the `TapeView` is unchanged. -/
@[simp]
public lemma toElem_eval_struct {k : ℕ} {idx : ℕ} {i : Fin k} {views : Fin k → TapeView} :
  (toElem idx i).eval_struct views = some
    (Function.update views i
      (match (views i).current with
      | some (Data.list ds) =>
        if idx < ds.length then
          ⟨(views i).data, (views i).path ++ [idx]⟩
        else views i
      | _ => views i)) := by sorry

/-- `outOfArg argIdx i` ascends back from the `argIdx`-th element,
    removing it from the end of the path. If the path ends with `argIdx`,
    strips it. If the path is empty or the tape is empty, does not change
    the `TapeView`. -/
@[simp]
public lemma outOfList_eval_struct_valid {k : ℕ} {argIdx : ℕ} {i : Fin k}
    {views : Fin k → TapeView} :
    (outOfList i).eval_struct views = some
      (Function.update views i
        ⟨(views i).data, (views i).path.dropLast⟩) := by sorry

end Routines
end Turing
