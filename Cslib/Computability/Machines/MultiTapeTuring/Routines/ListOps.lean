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
public def pushList {k : ℕ} (d : Data) (i : Fin k) : MultiTapeTM k Char :=
  right i ;ₜ put d i ;ₜ left i ;ₜ write '(' i

@[simp]
public lemma pushList_eval {k : ℕ} {d : Data}
  {ds : List Data} {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {r : List Char}
  (h_tape : tapes i = BiTape.mk₁ (Data.enc (Data.list ds) ++ r)) :
  (pushList d i).eval tapes = .some (Function.update tapes i
      (BiTape.mk₁ (Data.enc (Data.list (d :: ds)) ++ r))) := by sorry

/-- Remove the first element from a list encoding on tape `i`.
    Running `popEnc` on an empty list does not modify the tape. -/
public def popEnc {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public lemma popEnc_eval_cons {k : ℕ}
  {d : Data} {ds : List Data} {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {r : List Char}
  (h_tape : tapes i = BiTape.mk₁ (Data.enc (Data.list (d :: ds)) ++ r)) :
  (popEnc i).eval tapes = .some (Function.update tapes i
      (BiTape.mk₁ (Data.enc (Data.list ds) ++ r))) := by sorry

@[simp]
public lemma popEnc_eval_nil {k : ℕ} {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {r : List Char}
  (h_tape : tapes i = BiTape.mk₁ (Data.enc (Data.list []) ++ r)) :
  (popEnc i).eval tapes = .some tapes := by sorry

/-- `pushList d i` prepends a Data element to the topmost `Data.list` on tape `i`. -/
@[simp]
public lemma pushList_eval_struct {k : ℕ} {d : Data} {i : Fin k}
    {views : Fin k → TapeView}
    {ds : List Data}
    (h_path : (views i).path = [])
    (h_data : (views i).data = some (Data.list ds)) :
    (pushList d i).eval_struct views = some
      (Function.update views i
        ⟨some (Data.list (d :: ds)), []⟩) := by sorry

/-- `popEnc i` removes the first element from the topmost `Data.list` on tape `i`. -/
@[simp]
public lemma popEnc_eval_struct_cons {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    {d : Data} {ds : List Data}
    (h_path : (views i).path = [])
    (h_data : (views i).data = some (Data.list (d :: ds))) :
    (popEnc i).eval_struct views = some
      (Function.update views i
        ⟨some (Data.list ds), []⟩) := by sorry

/-- `popEnc i` on an empty list is a no-op. -/
@[simp]
public lemma popEnc_eval_struct_nil {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    (h_path : (views i).path = [])
    (h_data : (views i).data = some (Data.list [])) :
    (popEnc i).eval_struct views = some views := by sorry

end Routines
end Turing
