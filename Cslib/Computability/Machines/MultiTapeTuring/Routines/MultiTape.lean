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
-- Copy and comparison
-- ═══════════════════════════════════════════════════════════════════════════

/-- Copy a Data-encoded value from tape `i` to tape `j`
    (prepending the encoding to tape `j`). -/
public def copyEnc {k : ℕ} (i j : Fin k) : MultiTapeTM k Char := sorry

/-- The tape `j` state after `copyEnc` — depends on the source tape `i`
    and target tape `j`. -/
public noncomputable def copyEnc_tape
    (tape_i tape_j : BiTape Char) : BiTape Char := sorry

/-- `copyEnc` only modifies tape `j` (tape `i` is restored to its original position). -/
@[simp]
public lemma copyEnc_eval {k : ℕ}
  {i j : Fin k} {tapes : Fin k → BiTape Char} :
  (copyEnc i j).eval tapes = .some
    (Function.update tapes j (copyEnc_tape (tapes i) (tapes j))) := by sorry

@[simp]
public lemma copyEnc_tape_spec {d : Data}
  {lᵢ rᵢ : List Char}
  {rⱼ : List Char} :
  copyEnc_tape (BiTape.mk₂ lᵢ (Data.enc d ++ rᵢ)) (BiTape.mk₁ rⱼ) =
    BiTape.mk₁ (Data.enc d ++ rⱼ) := by sorry

/-- Compare Data-encoded values on tapes `i` and `j`.
    Runs `tm_eq` if values are equal, `tm_neq` if not.
    Tapes `i` and `j` are restored to their original positions. -/
public def eqEnc {k : ℕ} (i j : Fin k)
    (tm_eq tm_neq : MultiTapeTM k Char) : MultiTapeTM k Char := sorry

/-- Compare values on tapes `i` and `j` and put the boolean result on tape `result`. -/
public def isEq {k : ℕ} (i j : Fin k) (result : Fin k) :
    MultiTapeTM k Char :=
  eqEnc i j (put (StrEnc.toData true) result) (put (StrEnc.toData false) result)

@[simp]
public lemma isEq_eval {k : ℕ}
  {i j result : Fin k}
  {tapes : Fin k → BiTape Char}
  {d₁ d₂ : Data}
  {lᵢ rᵢ lⱼ rⱼ : List Char}
  {rₖ : List Char}
  (h_tapei : tapes i = BiTape.mk₂ lᵢ (Data.enc d₁ ++ rᵢ))
  (h_tapej : tapes j = BiTape.mk₂ lⱼ (Data.enc d₂ ++ rⱼ))
  (h_tapek : tapes result = BiTape.mk₁ rₖ) :
  (isEq i j result).eval tapes = .some
    (Function.update tapes result
      (BiTape.mk₁ (StrEnc.enc (decide (d₁ = d₂)) ++ rₖ))) := by sorry

/-- `copyEnc i j` copies the `Data` element at the current path position
    of tape `i` and writes it to tape `j` (which must be empty).
    Tape `i` is not modified. -/
@[simp]
public lemma copyEnc_eval_struct {k : ℕ} {i j : Fin k}
    {views : Fin k → TapeView}
    {d : Data}
    (h_ne : i ≠ j)
    (h_current : (views i).current = some d)
    (h_empty_j : (views j).data = none) :
    (copyEnc i j).eval_struct views = some
      (Function.update views j ⟨some d, []⟩) := by sorry

/-- `isEq i j result` compares the `Data` elements at the current positions
    of tapes `i` and `j`, and writes the boolean result to tape `result`
    (which must be empty). -/
@[simp]
public lemma isEq_eval_struct {k : ℕ} {i j result : Fin k}
    {views : Fin k → TapeView}
    {d₁ d₂ : Data}
    (h_current_i : (views i).current = some d₁)
    (h_current_j : (views j).current = some d₂)
    (h_empty_r : (views result).data = none) :
    (isEq i j result).eval_struct views = some
      (Function.update views result
        ⟨some (StrEnc.toData (decide (d₁ = d₂))), []⟩) := by sorry

end Routines
end Turing
