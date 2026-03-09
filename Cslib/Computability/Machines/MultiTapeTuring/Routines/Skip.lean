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

/-- Skip to the right across a Data-encoded value.
    Works for both `[...]` (num) and `(...)` (list) encodings. -/
public def skipRight {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry

/-- Skip to the left across a Data-encoded value (inverse of `skipRight`). -/
public def skipLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry

/-- `skipRight i` moves to the next sibling element within a list,
    incrementing the last path index. -/
@[simp]
public lemma skipRight_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    {rest : List ℕ} {idx : ℕ}
    (h_path : (views i).path = rest ++ [idx]) :
    (skipRight i).eval_struct views = some
      (Function.update views i
        ⟨(views i).data, rest ++ [idx + 1]⟩) := by sorry

/-- `skipLeft i` moves to the previous sibling element within a list,
    decrementing the last path index. -/
@[simp]
public lemma skipLeft_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    {rest : List ℕ} {idx : ℕ}
    (h_path : (views i).path = rest ++ [idx + 1]) :
    (skipLeft i).eval_struct views = some
      (Function.update views i
        ⟨(views i).data, rest ++ [idx]⟩) := by sorry

end Routines
end Turing
