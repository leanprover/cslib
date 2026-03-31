/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines

namespace Turing
namespace Routines

/-- Run a Turing machine `tm` sequentially `n` times. -/
public def iterate_n {k : ℕ} (tm : MultiTapeTM k Char) : ℕ → MultiTapeTM k Char
  | 0 => noop
  | n + 1 => tm;ₜ iterate_n tm n

@[simp]
public lemma iterate_n_zero {k : ℕ} {tm : MultiTapeTM k Char} :
    iterate_n tm 0 = noop := by rfl

@[simp]
public lemma iterate_n_succ {k : ℕ} {tm : MultiTapeTM k Char} {n : ℕ} :
    iterate_n tm (n + 1) = tm;ₜ iterate_n tm n := by rfl

@[simp]
public lemma iterate_n_succ' {k : ℕ} {tm : MultiTapeTM k Char} {n : ℕ} :
    (iterate_n tm (n + 1)).eval = (iterate_n tm n;ₜ tm).eval := by
  induction n with
  | zero =>
    simp only [iterate_n_succ, iterate_n_zero]
    funext tapes
    rw [MultiTapeTM.seq_eval, MultiTapeTM.seq_eval]
    simp [noop.eval]
  | succ n ih =>
    funext tapes
    simp only [iterate_n_succ]
    -- Goal: (tm ;ₜ (tm ;ₜ iterate_n tm n)).eval tapes =
    --       ((tm ;ₜ iterate_n tm n) ;ₜ tm).eval tapes
    simp only [MultiTapeTM.seq_eval]
    -- Now everything is >>= form. Convert to Part.bind for Part.bind_assoc
    change (tm.eval tapes).bind (fun t => (tm.eval t).bind fun s => (iterate_n tm n).eval s) =
      ((tm.eval tapes).bind fun t => (iterate_n tm n).eval t).bind fun t => tm.eval t
    rw [Part.bind_assoc]
    congr 1
    funext tapes'
    -- Goal: (tm.eval tapes').bind (fun s => (iterate_n tm n).eval s) =
    --       (iterate_n tm n).eval tapes' >>= tm.eval
    -- By ih: (iterate_n tm (n+1)).eval = (iterate_n tm n ;ₜ tm).eval
    -- i.e. (tm ;ₜ iterate_n tm n).eval = (iterate_n tm n ;ₜ tm).eval
    have := congr_fun ih tapes'
    simp only [iterate_n_succ, MultiTapeTM.seq_eval] at this
    exact this

/-- If `tm` always produces `f tapes` on input `tapes`, then `iterate_n tm n` produces `f^[n]`. -/
public lemma iterate_n_eval_of_total {k : ℕ} {tm : MultiTapeTM k Char}
    {f : (Fin k → BiTape Char) → (Fin k → BiTape Char)}
    (h : ∀ tapes, tm.eval tapes = Part.some (f tapes))
    {n : ℕ} {tapes : Fin k → BiTape Char} :
    (iterate_n tm n).eval tapes = Part.some (f^[n] tapes) := by
  induction n generalizing tapes with
  | zero => simp [iterate_n_zero, noop.eval]
  | succ n ih =>
    simp only [iterate_n_succ]
    rw [MultiTapeTM.seq_eval]
    simp only [h]
    change (Part.some (f tapes)).bind (fun t => (iterate_n tm n).eval t) = _
    rw [Part.bind_some, ih]
    simp [Function.iterate_succ']

end Routines
end Turing
