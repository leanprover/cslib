/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding

namespace Turing

namespace Routines

variable {k : ℕ}

/--
A Turing machine that executes `tm` a number of times as given by the first word on tape `i`.
If tape `i` is empty, do not execute the TM.
Note that the iteration counter is not directly available to `tm`. -/
public def loop (i : ℕ) {h_i : i < k}
  (tm : MultiTapeTM k (WithSep OneTwo)) : MultiTapeTM (k + 3) (WithSep OneTwo) :=
  sorry
  -- let target : Fin (k + (aux + 3)) := ⟨aux, by omega⟩
  -- let counter : Fin (k + (aux + 3)) := ⟨aux + 1, by omega⟩
  -- let cond : Fin (k + (aux + 3)) := ⟨aux + 2, by omega⟩
  -- (copy (k := k + (aux + 3)) i target (h_neq := by grind) <;>
  -- push counter [] <;>
  -- neq target counter cond (by grind) (by grind) (by grind) <;>
  -- doWhile cond (
  --   pop cond <;>
  --   tm.toMultiTapeTM <;>
  --   succ counter <;>
  --   neq target counter cond (by grind) (by grind) (by grind)) <;>
  -- pop cond <;>
  -- pop counter <;>
  -- pop target).set_aux_tapes (aux + 3)


@[simp]
public theorem loop_eval_list {i : ℕ} {h_i : i < k}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {tapes : Fin (k + 3) → List (List OneTwo)} :
  (loop i tm (h_i := h_i)).eval_list tapes =
      (((Part.bind · tm.eval_list)^[dya_inv ((tapes ⟨i, by omega⟩).headD [])]
        (Part.some (tapes_take tapes k (by omega))))).map
          fun tapes' => tapes_extend_by tapes' tapes := by
  sorry

end Routines
end Turing
