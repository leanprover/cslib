/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Routines.CaseDispatch
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Erase
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put

namespace Turing
namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- Boolean operations
-- ═══════════════════════════════════════════════════════════════════════════

/-- Combine two Bool values using logical OR.
    Reads booleans from tapes `i` and `j`, stores `i || j` on tape `j`,
    and erases tape `i`.
    If `i` holds true: erase both, put true on `j`.
    If `i` holds false: erase `i`, leave `j` unchanged. -/
public def combineOr {k : ℕ} (i j : Fin k) : MultiTapeTM k Char :=
  case_num i [erase i, erase i ;ₜ erase j ;ₜ put (StrEnc.toData true) j]

@[simp]
public lemma combineOr_eval {i j : Fin k} {b₁ b₂ : Bool}
    {tapes : Fin k → BiTape Char}
    {r_j : List Char}
    (h_tape_i : tapes i = BiTape.mk₁ (StrEnc.enc b₁))
    (h_tape_j : tapes j = BiTape.mk₁ (StrEnc.enc b₂ ++ r_j)) :
    (combineOr i j).eval tapes = .some
      (Function.update (Function.update tapes i (BiTape.mk₁ []))
        j (BiTape.mk₁ (StrEnc.enc (b₁ || b₂) ++ r_j))) := by
  simp [combineOr]
  sorry

/-- Negate a Bool value on tape `j`. -/
public def negateBool {k : ℕ} (j : Fin k) : MultiTapeTM k Char :=
  case_num j
    [erase j ;ₜ put (StrEnc.toData true) j,
     erase j ;ₜ put (StrEnc.toData false) j]

@[simp]
public lemma negateBool_eval {j : Fin k} {b : Bool}
    {tapes : Fin k → BiTape Char}
    {r : List Char}
    (h_tape : tapes j = BiTape.mk₁ (StrEnc.enc b ++ r)) :
    (negateBool j).eval tapes = .some (Function.update tapes j
      (BiTape.mk₁ (StrEnc.enc (!b) ++ r))) := by sorry

/-- `combineOr i j` dispatches on tape `i`: if `i` holds `false`, erases `i`
    (leaving `j` unchanged). If `i` holds `true`, erases both and writes `true` on `j`.
    If `i` does not hold a boolean, does nothing. -/
@[simp]
public lemma combineOr_eval_struct {k : ℕ} {i j : Fin k}
    {views : Fin k → TapeView} :
    (combineOr i j).eval_struct views =
      match (views i).currentAs Bool with
      | some false => some (Function.update views i ⟨none, []⟩)
      | some true => some
          (Function.update (Function.update views i ⟨none, []⟩)
            j ⟨some (StrEnc.toData true), []⟩)
      | none => some views := by sorry

/-- `negateBool j` replaces the topmost boolean on tape `j` with its negation. -/
@[simp]
public lemma negateBool_eval_struct {k : ℕ} {j : Fin k}
    {views : Fin k → TapeView}
    {b : Bool}
    (h_path : (views j).path = [])
    (h_data : (views j).data = some (StrEnc.toData b)) :
    (negateBool j).eval_struct views = some
      (Function.update views j
        ⟨some (StrEnc.toData (!b)), []⟩) := by sorry

end Routines
end Turing
