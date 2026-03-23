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

/-- Prepend the encoding of a `Data` value to tape `i`. -/
public def put {k : ℕ} (d : Data) (i : Fin k) : MultiTapeTM k Char :=
  putChars (Data.enc d) i

public lemma put_eval {k : ℕ} {d : Data} {i : Fin k}
    {tapes : Fin k → BiTape Char}
    {old : List Char}
    (h_tape : (tapes i) = BiTape.mk₁ old) :
    (put d i).eval tapes = some
      (Function.update tapes i (BiTape.mk₁ (d.enc ++ old))) := by
  unfold put
  induction d.enc with
  | nil => simp [putChars, h_tape]
  | cons c rest ih =>
    simp [putChars, ih, BiTape.mk₁, BiTape.move_left, BiTape.write]
    cases rest <;> cases old <;> simp [StackTape.map_some, StackTape.cons, StackTape.nil]

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


/-- Replace the contents of tape `i` by the encoding of `d`. -/
public def replace {k : ℕ} (d : Data) (i : Fin k) : MultiTapeTM k Char :=
  clear i ;ₜ put d i

@[simp]
public lemma replace.eval_struct {k : ℕ} {d : Data} {i : Fin k} {views : Fin k → TapeView}
  (h_data : (views i).path = []) :
  (replace d i).eval_struct views = some
    (Function.update views i (.ofData d)) := by
  simp only [MultiTapeTM.eval_struct, replace, MultiTapeTM.seq_eval]
  rw [clear.eval (ls := (views i).data.enc) (by simp [TapeView.toBiTape, h_data])]
  simp [put_eval (old := []), ← TapeView.toBiTape_ofData]


end Routines
end Turing
