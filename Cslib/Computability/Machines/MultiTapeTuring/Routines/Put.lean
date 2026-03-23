/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines

namespace Turing
namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- Put characters and Data values
-- ═══════════════════════════════════════════════════════════════════════════

/-- Write a list of characters to tape `i` by repeatedly moving left and writing,
    effectively prepending the characters to the tape content. -/
public def putChars : List Char → Fin k → MultiTapeTM k Char
  | [], _ => noop
  | c :: rest, i => putChars rest i ;ₜ left i ;ₜ write c i

@[simp]
public theorem putChars.eval {i : Fin k} {tapes : Fin k → BiTape Char}
    {h_empty : (tapes i) = Ø}
    {ls : List Char} :
  (putChars ls i).eval tapes = .some (Function.update tapes i (BiTape.mk₁ ls)) := by
  sorry


def clear (i : Fin k) : MultiTapeTM k Char := while_neq none i (write none i ;ₜ right i)

@[simp]
theorem clear.eval_inner {i : Fin k} {tapes : Fin k → BiTape Char} {ls : List Char} :
  Function.update tapes i ((Turing.BiTape.mk₁ ls).write none).move_right =
    Function.update tapes i (BiTape.mk₁ ls.tail) := by
  ext1 j
  by_cases h_ij : i = j
  · subst h_ij
    simp only [Function.update_self]
    cases ls with | nil | cons _ _ <;>
      simp [BiTape.mk₁, BiTape.write, BiTape.move_right]
  · have h : i ≠ j := by omega
    grind

lemma clear.eval_inner_iter {i : Fin k} {tapes : Fin k → BiTape Char} (ls : List Char)
    (h_tape_i : tapes i = BiTape.mk₁ ls)
    (n : ℕ)
    (h_n : n ≤ ls.length) :
  ((write none i ;ₜ right i).eval_tot (by simp))^[n] tapes =
    Function.update tapes i (BiTape.mk₁ (ls.drop n)) := by
  induction n with
  | zero => simp [h_tape_i]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp

-- TODO change this so that it does not need `ls` but works with a tape and a condition that
-- the left side is empty
theorem clear.eval {i : Fin k} {tapes : Fin k → BiTape Char} {ls : List Char}
    (h_tape_i : tapes i = BiTape.mk₁ ls) :
  (clear i).eval tapes = .some (Function.update tapes i (BiTape.mk₁ [])) := by
  have h_min : ∀ n' < ls.length,
      (((write none i ;ₜ right i).eval_tot (by simp))^[n'] tapes i).head ≠ none := by
    intro n' h_n'
    rw [clear.eval_inner_iter ls h_tape_i n' (by omega)]
    simp [Function.update_self, BiTape.mk₁, h_n']
  unfold clear
  rw [while_neq.eval' ls.length
    (by rw [clear.eval_inner_iter ls h_tape_i ls.length (by omega)]; simp [BiTape.mk₁])
    h_min]
  rw [clear.eval_inner_iter ls h_tape_i ls.length (by omega)]
  simp

/-- Prepend the encoding of a `Data` value to tape `i`. -/
public def put {k : ℕ} (d : Data) (i : Fin k) : MultiTapeTM k Char :=
  putChars (Data.enc d) i

/-- Prepend the encoding of a value of type `α` (via its `StrEnc` instance) to tape `i`. -/
public def putEnc {k : ℕ} {α : Type*} [StrEnc α] (x : α) (i : Fin k) :
    MultiTapeTM k Char :=
  put (StrEnc.toData x) i

/-- `put d i` writes a `Data` value to tape `i` if the tape is empty.
    If the tape already has data, `put` is a no-op.
    Resets the path to `[]`. -/
@[simp]
public lemma put_eval_struct_empty {k : ℕ} {d : Data} {i : Fin k}
    {views : Fin k → TapeView}
    (h_empty : (views i).path = []) :
    (put d i).eval_struct views = some
      (Function.update views i (.ofData d)) := by sorry



end Routines
end Turing
