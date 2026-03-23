/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put

namespace Turing
namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- List operations
-- ═══════════════════════════════════════════════════════════════════════════

/-- Prepend a Data element to a list encoding on tape `i`. -/
@[expose]
public def pushList {k : ℕ} (d : Data) (i : Fin k) : MultiTapeTM k Char :=
  write none i ;ₜ right i ;ₜ put d i ;ₜ left i ;ₜ write '(' i

/-- Remove the first element from a list encoding on tape `i`.
    Running `popEnc` on an empty list does not modify the tape. -/
public def popList {k : ℕ} (i : Fin k) : MultiTapeTM k Char := sorry

/-- `pushList d i` prepends a Data element to the topmost `Data.list` on tape `i`. -/
@[simp]
public lemma pushList_eval_struct {k : ℕ} {d : Data} {i : Fin k}
    {views : Fin k → TapeView} :
    (pushList d i).eval_struct views = some
      (Function.update views i ((views i).pushList d)) := by
  simp only [MultiTapeTM.eval_struct, pushList, MultiTapeTM.seq_eval]
  sorry
  -- match h_vi : views i with
  -- | ⟨Data.list ds, [], _⟩ =>
  --   -- Step 1: compute toBiTape for this view
  --   have h_bi : (views i).toBiTape =
  --       BiTape.mk₁ ('(' :: (ds.map Data.enc).flatten ++ [')']) := by
  --     simp [h_vi, TapeView.toBiTape, TapeView.encodedPos, Data.enc_list]
  --   -- Step 2: write none + right produces mk₁ (flat ++ [')'])
  --   have h_wr : ((BiTape.mk₁
  --       ('(' :: (ds.map Data.enc).flatten ++ [')'])).write none).move_right =
  --       BiTape.mk₁ ((ds.map Data.enc).flatten ++ [')']) := by
  --     simp [BiTape.mk₁, BiTape.write, BiTape.move_right,
  --       StackTape.cons_none_nil, StackTape.nil_head, StackTape.nil_tail,
  --       StackTape.map_some_head, StackTape.map_some_tail]
  --   -- Now chain: unfold eval_struct, use eval simp lemmas, put_eval, and connect back
  --   simp [TapeView.pushList, h_vi, Data.enc_list,
  --     TapeView.toBiTape, TapeView.encodedPos,
  --     write.eval, right.eval, left.eval, put_eval,
  --     Function.update_idem, Function.update_self,
  --     Function.iterate_zero, h_bi, h_wr,
  --     Part.bind_some, BiTape.mk₁, BiTape.move_left, BiTape.write,
  --     StackTape.cons_none_nil, StackTape.nil_head, StackTape.nil_tail,
  --     StackTape.map_some_head, StackTape.map_some_tail,
  --     ← TapeView.toBiTape_comp_update, TapeView.ofBiTapes?_toBiTape]
  -- | ⟨Data.list _, _ :: _, _⟩ =>
  --   simp only [TapeView.pushList, h_vi]
  --   sorry
  -- | ⟨Data.num _, [], _⟩ =>
  --   simp only [TapeView.pushList, h_vi]
  --   sorry
  -- | ⟨Data.num _, _ :: _, _⟩ =>
  --   simp only [TapeView.pushList, h_vi]
  --   sorry

@[simp]
public lemma popList_eval_struct {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView} :
    (popList i).eval_struct views = some
      (Function.update views i (views i).popList) := by sorry

end Routines
end Turing
