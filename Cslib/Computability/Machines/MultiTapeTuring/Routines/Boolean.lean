/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Routines.CaseDispatch
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Erase
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.ListOps
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed

namespace Turing
namespace Routines


-- ═══════════════════════════════════════════════════════════════════════════
-- Boolean operations
-- ═══════════════════════════════════════════════════════════════════════════

public def combineOrUpdate {k : ℕ} (j : Fin k) :
  MultiTapeTM k Char := sorry

-- @[simp]
-- public lemma combineOr_eval_struct {k : ℕ}
--     (in₁ in₂ out : Fin k)
--     (h_inj : [in₁, in₂, out].get.Injective)
--     {views : Fin k → TapeView} :
--     (combineOr in₁ in₂ out h_inj).eval_struct views = some
--       (match (views i).popList with
--       | some (b_data, vi') =>
--         let views' := Function.update views i vi'
--         if b_data = StrEnc.toData true then
--           match (views' j).popList with
--           | some (_, vj') =>
--             Function.update (Function.update views' i vi')
--               j ((vj').pushList (StrEnc.toData true))
--           | none => views'
--         else views'
--       | none => views) := by sorry

/-- Negate a Bool value on tape `j`.
    Pops the first element from tape `j` and pushes its negation. -/
public def negateBool {k : ℕ} (j : Fin k) : MultiTapeTM k Char :=
  case_popList_num j
    [-- false (0) → push true (1)
     pushList (StrEnc.toData true) j,
     -- true (1) → push false (0)
     pushList (StrEnc.toData false) j]

@[simp, grind <=]
public lemma negateBool.computes_head_update {k : ℕ} {i : Fin k} :
  computes_function_head_update (negateBool i) (fun b : Bool => !b) i := by
  sorry

grind_pattern negateBool.computes_head_update => negateBool i

-- TODO from here below the simp lemmas are nice. Let us try to find a similarly nice
-- simpe lemma for case_popList_num. Maybe the array is the problem?
@[simp]
public lemma negateBool_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} :
    (negateBool i).eval_struct views = some
      (Function.update views i (match views i with
      | ⟨Data.list (Data.num 0 :: rest), []⟩ => ⟨Data.list (Data.num 1 :: rest), []⟩
      | ⟨Data.list (Data.num 1 :: rest), []⟩ => ⟨Data.list (Data.num 0 :: rest), []⟩
      | _ => views i)) := by
  match h_v : views i with
  | ⟨Data.list (Data.num 0 :: rest), []⟩ => simp [negateBool, h_v]
  | ⟨Data.list (Data.num 1 :: rest), []⟩ => simp [negateBool, h_v]
  | v => sorry

public def test : MultiTapeTM 1 Char := pushList (StrEnc.toData true) 0 ;ₜ negateBool 0

public lemma test_eval_struct
    {views : Fin 1 → TapeView}
    (h_data : (views 0) = ⟨Data.list [], []⟩)
      :
    test.eval_struct views = some
      (Function.update views 0 ⟨Data.list [StrEnc.toData false], []⟩) := by
  simp [test, h_data]

end Routines
end Turing
