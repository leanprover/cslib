/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines
public import Cslib.Computability.Machines.MultiTapeTuring.TapeView
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Iterate
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Navigation
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Skip

namespace Turing
namespace Routines

/-- Move left `n` times on tape `i`. -/
public def left_n {k : ℕ} (n : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  iterate_n (left i) n

/-- Move right `n` times on tape `i`. -/
public def right_n {k : ℕ} (n : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  iterate_n (right i) n

@[simp]
public lemma left_n.eval {k : ℕ} {n : ℕ} {i : Fin k} {tapes : Fin k → BiTape Char} :
    (left_n n i).eval tapes = Part.some
      (Function.update tapes i (BiTape.move_left^[n] (tapes i))) := by
  simp only [left_n]
  rw [iterate_n_eval_of_total (fun t => left.eval)]
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp, ih, Function.update_self,
      Function.update_idem]

@[simp]
public lemma right_n.eval {k : ℕ} {n : ℕ} {i : Fin k} {tapes : Fin k → BiTape Char} :
    (right_n n i).eval tapes = Part.some
      (Function.update tapes i (BiTape.move_right^[n] (tapes i))) := by
  simp only [right_n]
  rw [iterate_n_eval_of_total (fun t => right.eval)]
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp, ih, Function.update_self,
      Function.update_idem]

/-- Check characters left-to-right starting from the current (left-end) position.
    After checking, returns the head to the original position before running
    the then/else branch. -/
public def ite_enc_from_left {k : ℕ}
    (v : List Char) (i : Fin k)
    (then_branch else_branch : MultiTapeTM k Char) :
    MultiTapeTM k Char := match v with
  | [] => then_branch
  | c :: cs => if_eq c i
      (right i;ₜ ite_enc_from_left cs i (left i;ₜ then_branch) (left i;ₜ else_branch))
      else_branch

/-- Check a value by first moving left to the start, then comparing left-to-right,
    then returning to the original (right-end) position. -/
public def ite_enc_from_right {k : ℕ}
    (v : List Char) (i : Fin k)
    (then_branch else_branch : MultiTapeTM k Char) :
    MultiTapeTM k Char :=
  left_n (v.length - 1) i;ₜ
    ite_enc_from_left v i
      (right_n (v.length - 1) i;ₜ then_branch)
      (right_n (v.length - 1) i;ₜ else_branch)

@[simp]
public lemma ite_enc_from_left.eval {k : ℕ} {v : List Char} {i : Fin k}
    {then_branch else_branch : MultiTapeTM k Char}
    {tapes : Fin k → BiTape Char} :
    (ite_enc_from_left v i then_branch else_branch).eval tapes =
      if ∀ n, (h : n < v.length) →
        (BiTape.move_right^[n] (tapes i)).head = some v[n]
      then
        then_branch.eval tapes
      else
        else_branch.eval tapes := by
  induction v generalizing tapes then_branch else_branch with
  | nil => simp [ite_enc_from_left]
  | cons c cs ih =>
    simp only [ite_enc_from_left, if_eq.eval]
    by_cases h : (tapes i).head = some c
    · simp only [h, ↓reduceIte, MultiTapeTM.seq_eval, right.eval, Part.bind_some, Part.bind_eq_bind]
      rw [ih]
      simp only [MultiTapeTM.seq_eval, left.eval, Part.bind_some, Part.bind_eq_bind,
        Function.update_self, Function.update_idem,
        BiTape.move_right_move_left, Function.update_eq_self]
      congr 1
      ext
      constructor <;> intro h' n hn
      · match n with
        | 0 => simpa using h
        | n + 1 => simpa [Function.iterate_succ] using h' n (by simp_all)
      · simpa [Function.iterate_succ] using h' (n + 1) (by simp_all)
    · simp only [h, ↓reduceIte]
      have : ¬∀ n, (hn : n < (c :: cs).length) →
          (BiTape.move_right^[n] (tapes i)).head = some (c :: cs)[n] := by
        intro h'; exact h (by simpa using h' 0 (by simp))
      exact (if_neg this).symm

@[simp]
public lemma ite_enc_from_right.eval {k : ℕ} {v : List Char} {i : Fin k}
    {then_branch else_branch : MultiTapeTM k Char}
    {tapes : Fin k → BiTape Char} :
    (ite_enc_from_right v i then_branch else_branch).eval tapes =
      if ∀ n, (h : n < v.length) →
        (BiTape.move_right^[n] (BiTape.move_left^[v.length - 1] (tapes i))).head = some v[n]
      then
        then_branch.eval tapes
      else
        else_branch.eval tapes := by
  have cancel : BiTape.move_right^[v.length - 1]
      (BiTape.move_left^[v.length - 1] (tapes i)) = tapes i :=
    Function.LeftInverse.iterate
      (f := BiTape.move_left) (g := BiTape.move_right)
      BiTape.move_left_move_right _ _
  simp only [ite_enc_from_right]
  rw [MultiTapeTM.seq_eval]
  simp only [left_n.eval]
  change (Part.some (Function.update tapes i
    (BiTape.move_left^[v.length - 1] (tapes i)))).bind
    (fun t => (ite_enc_from_left v i
      (right_n (v.length - 1) i;ₜ then_branch)
      (right_n (v.length - 1) i;ₜ else_branch)).eval t) = _
  rw [Part.bind_some, ite_enc_from_left.eval]
  simp only [Function.update_self]
  split <;> {
    rw [MultiTapeTM.seq_eval]
    simp only [right_n.eval]
    change (Part.some (Function.update (Function.update tapes i _) i _)).bind _ = _
    rw [Part.bind_some]
    simp [Function.update_idem, cancel, Function.update_eq_self]
  }

/-- Runs `then_branch` if `(views i).current = v`, otherwise `else_branch`.
    Works regardless of whether the head is at the left or right end. -/
public def ite {k : ℕ} (v : Data) (i : Fin k)
    (then_branch else_branch : MultiTapeTM k Char) :
    MultiTapeTM k Char :=
  if_eq '(' i
    (ite_enc_from_left v.enc i then_branch else_branch)
    (ite_enc_from_right v.enc.reverse i then_branch else_branch)

@[simp]
public lemma ite.eval_struct {k : ℕ} {v : Data} {i : Fin k}
    {then_branch else_branch : MultiTapeTM k Char}
    {views : Fin k → TapeView} :
    (ite v i then_branch else_branch).eval_struct views =
      if (views i).current = v then
        then_branch.eval_struct views
      else
        else_branch.eval_struct views := by
  -- simp only [ite, MultiTapeTM.eval_struct, ite_enc_from_left.eval, Function.comp_apply,
  --   TapeView.ite_enc_condition_iff]
  -- split <;> rfl
  sorry

end Routines
end Turing
