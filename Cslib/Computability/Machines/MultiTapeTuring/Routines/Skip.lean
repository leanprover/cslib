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
-- Skip right / left across a Data-encoded value
-- ═══════════════════════════════════════════════════════════════════════════

-- TODO If we do not specify a max nesting depth when constructing the skip
-- machine, it requires an additional tape to count the nesting depth.
-- if the nesting depth is bounded by a constant, this is still fine,
-- but we need to account for it - so maybe it's better to just do it
-- when constructing it?

/-- Skip to the right across a Data-encoded value. -/
public def skipRight {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry

/-- Skip to the left across a Data-encoded value (inverse of `skipRight`). -/
public def skipLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry


@[simp, grind =>]
public lemma skipLeft_haltsOn {k : ℕ} (i : Fin k) : ∀ t, (skipLeft i).HaltsOn t := by
  sorry

@[simp, grind =>]
public lemma skipRight_haltsOn {k : ℕ} (i : Fin k) : ∀ t, (skipRight i).HaltsOn t := by
  sorry

-- TODO would be nice to make this a simp lemma.

/-- `skipRight i` moves to the next sibling element within a list,
    incrementing the last path index, or to the end of the list. -/
@[simp]
public lemma skipRight_eval_struct {k j : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    (h_nonempty : (views i).path.getLast?.isSome)
    (h_left : (views i).headPos = .leftEnd) :
    (skipRight i).eval_struct views = .some (Function.update views i (
        let idx : ℕ := (views i).path.getLast?.get h_nonempty
        if h_next : ((views i).parent.current.atPath [idx.succ]).isSome then
            (views i).parent.appendPath idx.succ h_next
          else
            (views i).parent.toRightEnd)) := by sorry

/-- `skipLeft i` is the inverse of `skipRight i`.
    When positioned at the right end of a non-empty list, it moves to the
    left end of the last entry in the list.
    When positioned at the left end of a non-first item in a list, it moves
    to the left end of the previous item. -/
public lemma skipLeft_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} :
    (skipLeft i).eval_struct views = .some (Function.update views i (
      if h_right : (views i).headPos = .rightEnd then
        if h_empty : (views i).currentList.isEmpty then
          views i
        else
          ((views i).appendPath
            ((views i).currentList.length - 1) (by
              rw [TapeView.current_atPath_length_sub_one_isSome_of_non_empty _ h_empty])).toLeftEnd
      else
        if h_path : (views i).path.getLast?.isSome then
          let idx := (views i).path.getLast?.get h_path
          if h_prev : 0 < idx then
            (views i).parent.appendPath (idx - 1) (by
              unfold TapeView.current;
              have : idx - 1 ≤ idx := by omega
              apply Data.atPath_isSome_of_le_isSome this
              simp [idx, (views i).h_path]
              )
          else
            views i
        else
          (views i))) := by sorry

end Routines
end Turing
