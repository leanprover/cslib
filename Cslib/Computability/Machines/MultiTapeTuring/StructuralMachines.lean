/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.Encoding
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator

namespace Turing

namespace Routines


public instance : Fintype Char := by sorry

public def right (i : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public lemma right_eval {i : Fin k} {tapes : Fin k → BiTape Char} :
    (right i).eval tapes = .some
      (Function.update tapes i (tapes i).move_right) := by sorry

public def while_eq (c : Char) (i : Fin k)  (tm : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

@[simp]
public lemma while_eq_eval {i : Fin k} {c : Char}
  {tm : MultiTapeTM k Char}
  {tapes : Fin k → BiTape Char}
  (h_halts : ∀ tapes, tm.HaltsOn tapes) :
    (while_eq c i tm).eval tapes =
    ⟨∃ n, ((tm.eval_tot h_halts)^[n] tapes i).head ≠ .some c,
      fun h_loopEnds => (tm.eval_tot h_halts)^[Nat.find h_loopEnds] tapes⟩ := by
    sorry

public def while_neq (c : Char) (i : Fin k) (tm : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

@[simp]
public lemma while_neq_eval {i : Fin k} {c : Char}
  {tm : MultiTapeTM k Char}
  {tapes : Fin k → BiTape Char}
  (h_halts : ∀ tapes, tm.HaltsOn tapes) :
    (while_eq c i tm).eval tapes =
    ⟨∃ n, ((tm.eval_tot h_halts)^[n] tapes i).head = .some c,
      fun h_loopEnds => (tm.eval_tot h_halts)^[Nat.find h_loopEnds] tapes⟩ := by
    sorry

-- TODO We are only
-- dealing with a _max_ depth and not an exact depth,
-- We have to check that there is an opening parenthesis!

--- Skip to the right across a StrEnc-encoded value.
def skipRight_numeric {k : ℕ} (depth : ℕ) (i : Fin k) :
    MultiTapeTM k Char :=
  match depth with
  | 0     => while_neq ')' i (right i) ;ₜ right i
  | d + 1 => while_eq '(' i (right i ;ₜ skipRight_numeric d i) ;ₜ right i

--- Skip to the right across a StrEnc-encoded value.
public def skipRight {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k) :
    MultiTapeTM k Char := skipRight_numeric (StrEnc.maxDepth α) i

@[simp]
public lemma skipRight_eval {k : ℕ} {α : Type*} [StrEnc α] {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {x : α}
  {l r : List Char}
  (h_hasValue : tapes i = BiTape.mk₂ l ((StrEnc.enc x) ++ r)) :
  (skipRight α i).eval tapes = .some (Function.update tapes i
      (BiTape.mk₂ ((StrEnc.enc x).reverse ++ l) r)) := by sorry

end Routines

end Turing
