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

namespace Turing
namespace Routines

/-- Turing machine `tm` computes a function on data from tape `i` and updates tape `j`. -/
-- TODO move this somewhere else
public def computes_function {k : ℕ}
  (tm : MultiTapeTM k Char) (f : TapeView → Data → TapeView)
  (i j : Fin k) (_h_neq : i ≠ j)
  (views : Fin k → TapeView) :=
  tm.eval_struct views = some (Function.update views j
    (((views i).current.map (f (views j))).getD (views j)))


-- TODO could generalize this to `f` having a preimage β.
public def computes_function_push {k : ℕ}
  {α : Type} [StrEnc α]
  (tm : MultiTapeTM k Char) (f : Data → α)
  (i j : Fin k) (_h_neq : i ≠ j) :=
  computes_function tm (fun tv d => tv.pushList (StrEnc.toData (f d))) i j _h_neq

public def computes_function_push_bool {k : ℕ}
  (tm : MultiTapeTM k Char) (f : Data → Bool)
  (i j : Fin k) (h_neq : i ≠ j) :=
  computes_function_push (α := Bool) tm f i j h_neq

/-- Turing machine `tm` updates the head of tape `i`. -/
public def computes_function_update {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char) (f : α → β)
  (i : Fin k)
  (views : Fin k → TapeView) :=
  tm.eval_struct views = some (Function.update views i ((views i).updateListHeadTyped f))

@[simp]
public def computes_fun_push_bool_update_seq {k : ℕ}
  (tm₁ tm₂ : MultiTapeTM k Char) (f₁ : Data → Bool) (f₂ : Data → Data)
  (i : Fin k) :=
  computes_function_push_bool tm f i i (by simp)


-- ═══════════════════════════════════════════════════════════════════════════
-- Boolean operations
-- ═══════════════════════════════════════════════════════════════════════════

/-- Combine two Bool values using logical OR, operating on lists.
    Pops the first element from tape `i`.
    If it is `false`, leaves tape `j` unchanged.
    If it is `true`, pops the first element from tape `j` and pushes `true`.
    If tape `i` cannot be popped, does nothing. -/
public def combineOr {k : ℕ} (j : Fin k) : MultiTapeTM k Char := sorry

-- @[simp]
-- public lemma combineOr_eval_struct {k : ℕ} {i j : Fin k}
--     {views : Fin k → TapeView} :
--     (combineOr i j).eval_struct views = some
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

@[simp]
public lemma computes_fun_negateBool {k : ℕ} {i : Fin k} {views : Fin k → TapeView} :
    computes_function_update (negateBool i) (fun b : Bool => !b) i views := by
  sorry

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
