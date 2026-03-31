/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Routines.CaseDispatch
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.ListOps
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed

namespace Turing
namespace Routines


-- ═══════════════════════════════════════════════════════════════════════════
-- Boolean operations
-- ═══════════════════════════════════════════════════════════════════════════

/-- TODO document -/
public def combineOrUpdate {k : ℕ} (j : Fin k) :
  MultiTapeTM k Char := ite_list_head j true
      (popList j;ₜ popList j;ₜ pushList (StrEnc.toData true) j)
      noop

@[simp]
public lemma combineOrUpdate.computes_fun {k : ℕ} {j : Fin k} :
  computes_function_update (combineOrUpdate j) (fun (ls : List Bool) =>
    (ls.head? == some true || ls[1]? == some true) :: ls.tail.tail) j := by
  sorry

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
  computes_function_head_update (negateBool i) Bool.not i := by
  sorry

grind_pattern negateBool.computes_head_update => negateBool i


end Routines
end Turing
