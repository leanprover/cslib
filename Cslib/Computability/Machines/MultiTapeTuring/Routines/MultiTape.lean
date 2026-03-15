/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Erase
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed

namespace Turing
namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- Copy and comparison
-- ═══════════════════════════════════════════════════════════════════════════

/-- Copy a Data-encoded value from tape `i` to tape `j`
    (prepending the encoding to tape `j`). -/
public def copyEnc {k : ℕ} (i j : Fin k) : MultiTapeTM k Char := sorry

/-- Compare Data-encoded values on tapes `i` and `j`.
    Runs `tm_eq` if values are equal, `tm_neq` if not.
    Tapes `i` and `j` are restored to their original positions. -/
public def eqEnc {k : ℕ} (i j : Fin k)
    (tm_eq tm_neq : MultiTapeTM k Char) : MultiTapeTM k Char := sorry

/-- Compare values on tapes `i` and `j` and put the boolean result on tape `result`. -/
public def isEq {k : ℕ} (i j : Fin k) (result : Fin k) :
    MultiTapeTM k Char :=
  eqEnc i j (put (StrEnc.toData true) result) (put (StrEnc.toData false) result)

@[grind =>]
public lemma isEq.computes_fun {k : ℕ} (i j result : Fin k)
    {α : Type} [StrEnc α] [DecidableEq α]
    (h_neq : [i, j, result].get.Injective) :
    computes_function_read_read_push
      (isEq i j result)
      (fun (d₁ : α) (d₂ : α) => decide (d₁ = d₂)) i j result h_neq := by
  sorry

/-- `copyEnc i j` copies the `Data` element at the current path position
    of tape `i` and writes it to tape `j` (which must be empty).
    Tape `i` is not modified. -/
@[simp]
public lemma copyEnc_eval_struct {k : ℕ} {i j : Fin k}
    {views : Fin k → TapeView}
    {d : Data}
    (h_ne : i ≠ j)
    (h_current : (views i).current = some d)
    (h_empty_j : (views j).data = Data.list []) :
    (copyEnc i j).eval_struct views = some
      (Function.update views j ⟨d, []⟩) := by sorry

/-- `isEq i j result` compares the `Data` elements at the current positions
    of tapes `i` and `j`, and writes the boolean result to tape `result`
    (which must be empty). -/
@[simp]
public lemma isEq_eval_struct {k : ℕ} {i j result : Fin k}
    {views : Fin k → TapeView}
    {d₁ d₂ : Data}
    (h_current_i : (views i).current = some d₁)
    (h_current_j : (views j).current = some d₂)
    (h_empty_r : (views result).data = Data.list []) :
    (isEq i j result).eval_struct views = some
      (Function.update views result
        ⟨StrEnc.toData (decide (d₁ = d₂)), []⟩) := by sorry

end Routines
end Turing
