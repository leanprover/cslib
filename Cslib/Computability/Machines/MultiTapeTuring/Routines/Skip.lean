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

/-- Skip to the right across a Data-encoded value.
    Works for both `[...]` (num) and `(...)` (list) encodings. -/
public def skipRight {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry

/-- Skip to the left across a Data-encoded value (inverse of `skipRight`). -/
public def skipLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry

/-- `skipRight i` moves to the next sibling element within a list,
    incrementing the last path index. -/
public lemma skipRight_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    {rest : List ℕ} {idx : ℕ}
    (h_hasNext : (views i).next.isSome) :
    (skipRight i).eval_struct views = some
      (Function.update views i ((views i).next.get h_hasNext)) := by sorry

/-- `skipLeft i` moves to the previous sibling element within a list,
    decrementing the last path index. -/
public lemma skipLeft_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    {rest : List ℕ} {idx : ℕ}
    (h_path : (views i).path = rest ++ [idx + 1]) :
    (skipLeft i).eval_struct views = some
      (Function.update views i
        ⟨(views i).data, rest ++ [idx]⟩) := by sorry

end Routines
end Turing
