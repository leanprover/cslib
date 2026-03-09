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
-- Erase
-- ═══════════════════════════════════════════════════════════════════════════

/-- Erase the Data-encoded value at the head of tape `i`. -/
public def erase {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry

/-- `erase i` clears the tape, setting data to `Data.list []` and path to `[]`. -/
@[simp]
public lemma erase_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} :
    (erase i).eval_struct views = some
      (Function.update views i ⟨Data.list [], []⟩) := by sorry

end Routines
end Turing
