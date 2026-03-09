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

/-- The tape state after `erase` — depends only on the tape being erased. -/
public noncomputable def erase_tape (tape : BiTape Char) : BiTape Char := sorry

@[simp]
public lemma erase_eval {k : ℕ} {i : Fin k}
  {tapes : Fin k → BiTape Char} :
  (erase i).eval tapes = .some (Function.update tapes i
      (erase_tape (tapes i))) := by sorry

@[simp]
public lemma erase_tape_spec {d : Data} {r : List Char} :
  erase_tape (BiTape.mk₁ (Data.enc d ++ r)) = BiTape.mk₁ r := by sorry

/-- `erase i` clears the tape, setting data to `none` and path to `[]`. -/
@[simp]
public lemma erase_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} :
    (erase i).eval_struct views = some
      (Function.update views i ⟨none, []⟩) := by sorry

end Routines
end Turing
