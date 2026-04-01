/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines

namespace Turing
namespace Routines

/-- Iterating a pointwise update `fun t => Function.update t i (f (t i))` is the same as
    iterating `f` on the `i`-th component. -/
@[simp]
public lemma Function.iterate_update {α : Type*} {β : Type*} [DecidableEq α]
    {i : α} {f : β → β} {g : α → β} {n : ℕ} :
    (fun t => Function.update t i (f (t i)))^[n] g = Function.update g i (f^[n] (g i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp, ih, Function.update_self,
      Function.update_idem]

/-- Run a Turing machine `tm` sequentially `n` times. -/
public def iterate_n {k : ℕ} (tm : MultiTapeTM k Char) : ℕ → MultiTapeTM k Char
  | 0 => noop
  | n + 1 => tm;ₜ iterate_n tm n

@[simp]
public lemma iterate_n_zero {k : ℕ} {tm : MultiTapeTM k Char} :
    iterate_n tm 0 = noop := by rfl

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
    have := congr_fun ih tapes'
    simp only [iterate_n_succ, MultiTapeTM.seq_eval] at this
    exact this

/-- Evaluating `iterate_n tm n` is the same as iterating the monadic bind `(· >>= tm.eval)`. -/
@[simp]
public lemma iterate_n_eval_bind {k : ℕ} {tm : MultiTapeTM k Char}
    {n : ℕ} {tapes : Fin k → BiTape Char} :
    (iterate_n tm n).eval tapes = ((· >>= tm.eval)^[n]) (pure tapes) := by
  have aux : ∀ (m : ℕ) (p : Part (Fin k → BiTape Char)),
      p >>= (fun x => ((· >>= tm.eval)^[m]) (pure x)) =
      ((· >>= tm.eval)^[m]) p := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      intro p
      simp only [Function.iterate_succ', Function.comp]
      rw [← ihm, bind_assoc]
  induction n generalizing tapes with
  | zero => simp [iterate_n_zero, noop.eval]
  | succ n ih =>
    rw [iterate_n_succ, MultiTapeTM.seq_eval]
    -- Goal: tm.eval tapes >>= (iterate_n tm n).eval =
    --       ((· >>= tm.eval)^[n+1]) (pure tapes)
    -- Unfold iterate on RHS: g^[n+1] (pure tapes) = g^[n] (g (pure tapes))
    --                       = g^[n] (pure tapes >>= tm.eval) = g^[n] (tm.eval tapes)
    change tm.eval tapes >>= (iterate_n tm n).eval =
      ((· >>= tm.eval)^[n]) (pure tapes >>= tm.eval)
    rw [pure_bind]
    conv_lhs => arg 2; ext t; rw [ih]
    exact aux n (tm.eval tapes)

/-- If `tm` always produces `f tapes` on input `tapes`, then `iterate_n tm n` produces `f^[n]`. -/
public lemma iterate_n_eval_of_total {k : ℕ} {tm : MultiTapeTM k Char}
    {f : (Fin k → BiTape Char) → (Fin k → BiTape Char)}
    (h : ∀ tapes, tm.eval tapes = Part.some (f tapes))
    {n : ℕ} {tapes : Fin k → BiTape Char} :
    (iterate_n tm n).eval tapes = Part.some (f^[n] tapes) := by
  rw [iterate_n_eval_bind]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp, ih]
    change (Part.some (f^[n] tapes)).bind tm.eval = _
    rw [Part.bind_some, h]

/-- Structural version: if `tm.eval_struct` always produces `f views`,
    then `iterate_n tm n` produces `f^[n]`. -/
@[simp]
public lemma iterate_n_eval_struct_of_total {k : ℕ}
    {tm : MultiTapeTM k Char}
    {f : (Fin k → TapeView) → (Fin k → TapeView)}
    (h : ∀ views, tm.eval_struct views = Part.some (f views))
    {n : ℕ} {views : Fin k → TapeView} :
    (iterate_n tm n).eval_struct views =
      Part.some (f^[n] views) := by
  induction n generalizing views with
  | zero => simp [iterate_n_zero, noop.eval_struct]
  | succ n ih =>
    simp only [iterate_n_succ, seq_eval_struct, h, Part.bind_some]
    exact ih

end Routines
end Turing
