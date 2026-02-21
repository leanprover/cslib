/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.AddRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.LoopCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

namespace Turing

variable {k : ℕ}

namespace Routines

-- Multiplies the heads of 0 and 1 and stores the result in 2.
def mul₀ : MultiTapeTM 9 (WithSep OneTwo) :=
  (push 2 []) <;> loop 0 (h_i := by omega) (add_assign 1 2 3)

@[simp]
lemma add_assign_iter {i j aux : Fin (k + 6)} {r : ℕ}
  (h_inj : [i, j, aux, aux + 1, aux + 2, aux + 3].get.Injective)
  {tapes : Fin (k + 6) → List (List OneTwo)} :
  (Part.bind · (add_assign i j aux h_inj).eval_list)^[r] (.some tapes) =
    Part.some (Function.update tapes j (
      if r = 0 then
        tapes j
      else
        (dya ((dya_inv ((tapes j).headD [])) + r * (dya_inv ((tapes i).headD [])))) ::
          (tapes j).tail)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    simp only [ih, Part.bind_some]
    rw [add_assign_eval_list]
    have h_neq : i ≠ j := Function.Injective.ne h_inj (a₁ := 0) (a₂ := 1) (by grind)
    simp
    grind

@[simp]
theorem mul₀_eval_list {tapes : Fin 9 → List (List OneTwo)} :
  mul₀.eval_list tapes = .some
    (Function.update tapes 2 (
      (dya (dya_inv ((tapes 0).headD []) * dya_inv ((tapes 1).headD [])) :: (tapes 2)))) := by
  by_cases h_zero: dya_inv ((tapes 0).head?.getD []) = 0
  · simp [mul₀, h_zero]
    grind
  · simp [mul₀, h_zero]
    grind

/--
A Turing machine that multiplies the heads of tapes i and j and pushes the result to tape l.
If tapes are empty, their heads are assumed to be zero.
-/
public def mul
  (i j l : Fin (k + 9))
  (aux : Fin (k + 9) := ⟨k + 3, by omega⟩)
  (h_inj : [i, j, l, aux, aux + 1, aux + 2, aux + 3, aux + 4, aux + 5].get.Injective := by decide) :
  MultiTapeTM (k + 9) (WithSep OneTwo) :=
  mul₀.with_tapes [i, j, l, aux, aux + 1, aux + 2, aux + 3, aux + 4, aux + 5].get h_inj

@[simp, grind =]
public theorem mul_eval_list (i j l aux : Fin (k + 9))
  {h_inj : [i, j, l, aux, aux + 1, aux + 2, aux + 3, aux + 4, aux + 5].get.Injective}
  {tapes : Fin (k + 9) → List (List OneTwo)} :
  (mul i j l aux h_inj).eval_list tapes =
      .some (Function.update tapes l (
        (dya (dya_inv ((tapes i).headD []) * dya_inv ((tapes j).headD [])) :: (tapes l)))) := by
  simpa [mul] using apply_updates_function_update h_inj

end Routines

end Turing
