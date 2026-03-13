/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Erase

namespace Turing
namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- List operations
-- ═══════════════════════════════════════════════════════════════════════════

/-- Prepend a Data element to a list encoding on tape `i`. -/
@[expose]
public def pushList {k : ℕ} (d : Data) (i : Fin k) : MultiTapeTM k Char :=
  right i ;ₜ put d i ;ₜ left i ;ₜ write '(' i

/-- Remove the first element from a list encoding on tape `i`.
    Running `popEnc` on an empty list does not modify the tape. -/
public def popList {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry

/-- `pushList d i` prepends a Data element to the topmost `Data.list` on tape `i`. -/
@[simp]
public lemma pushList_eval_struct {k : ℕ} {d : Data} {i : Fin k}
    {views : Fin k → TapeView} :
    (pushList d i).eval_struct views = some
      (Function.update views i ((views i).pushList d)) := by sorry

@[simp]
public lemma popList_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} :
    (popList i).eval_struct views = some
      (Function.update views i (views i).popList) := by sorry

end Routines
end Turing
