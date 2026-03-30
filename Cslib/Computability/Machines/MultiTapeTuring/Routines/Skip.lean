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

/-- `skipLeft i` when positioned at the right end of a non-empty list moves to
    the left end of the last entry in the list.
    This is the inverse of `skipRight_eval_struct` when `skipRight` reaches
    the end of the list. -/
public lemma skipLeft_eval_struct_rightEnd {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    (h_right : (views i).headPos = .rightEnd)
    (h_nonempty : (views i).currentList.length > 0)
    (h_last : ((views i).current.atPath [(views i).currentList.length - 1]).isSome) :
    (skipLeft i).eval_struct views = .some (Function.update views i
      ((views i).appendPath ((views i).currentList.length - 1) h_last).toLeftEnd) := by sorry

/-- `skipLeft i` when positioned at the left end of a non-first item in a list
    moves to the left end of the previous item.
    This is the inverse of `skipRight_eval_struct` when `skipRight` advances
    to the next sibling. -/
public lemma skipLeft_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    (h_nonempty : (views i).path.getLast?.isSome)
    (h_left : (views i).headPos = .leftEnd)
    (h_not_first : (views i).path.getLast?.get h_nonempty > 0)
    (h_prev : ((views i).parent.current.atPath
      [(views i).path.getLast?.get h_nonempty - 1]).isSome) :
    (skipLeft i).eval_struct views = .some (Function.update views i
      ((views i).parent.appendPath
        ((views i).path.getLast?.get h_nonempty - 1) h_prev)) := by sorry

end Routines
end Turing
