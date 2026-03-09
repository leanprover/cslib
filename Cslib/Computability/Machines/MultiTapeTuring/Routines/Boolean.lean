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

/-- Combine two Bool values using logical OR, operating on lists.
    Pops the first element from tape `i`.
    If it is `false`, leaves tape `j` unchanged.
    If it is `true`, pops the first element from tape `j` and pushes `true`.
    If tape `i` cannot be popped, does nothing. -/
public def combineOr {k : ℕ} (i j : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public lemma combineOr_eval_struct {k : ℕ} {i j : Fin k}
    {views : Fin k → TapeView} :
    (combineOr i j).eval_struct views = some
      (match (views i).popList with
      | some (b_data, vi') =>
        let views' := Function.update views i vi'
        if b_data = StrEnc.toData true then
          match (views' j).popList with
          | some (_, vj') =>
            Function.update (Function.update views' i vi')
              j ((vj').pushList (StrEnc.toData true))
          | none => views'
        else views'
      | none => views) := by sorry

/-- Negate a Bool value on tape `j`.
    Pops the first element from tape `j` and pushes its negation. -/
public def negateBool {k : ℕ} (j : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public lemma negateBool_eval_struct {k : ℕ} {j : Fin k}
    {views : Fin k → TapeView} :
    (negateBool j).eval_struct views = some
      (match (views j).popList with
      | some (b_data, vj') =>
        if b_data = StrEnc.toData false then
          Function.update views j (vj'.pushList (StrEnc.toData true))
        else if b_data = StrEnc.toData true then
          Function.update views j (vj'.pushList (StrEnc.toData false))
        else views
      | none => views) := by sorry

end Routines
end Turing
