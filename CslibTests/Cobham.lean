/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import Cslib.Computability.FunctionAlgebras.Cobham.Defs
import Mathlib.Data.Fin.VecNotation

/-! # Cobham's function algebra tests

These tests evaluate a few terms of Cobham's algebra, over the binary alphabet and a
three-symbol alphabet, and check that some simple unary functions are denoted by limited
terms, including one built by limited recursion on notation.
-/

namespace CslibTests.Cobham

open Cslib Cslib.Cobham

/-! ## Evaluation -/

/-- Recursion on notation counting the symbols of its argument in unary, bounded by the
successor `x ↦ true :: x`. -/
private def unaryLength : Cobham Bool 1 :=
  boundedRec empty (fun _ => comp (cons true) fun _ => proj 1) (cons true)

example : unaryLength.eval ![[true, false, true]] = [true, true, true] := by decide

example : unaryLength.eval ![[]] = [] := by decide

example : (comp (cons true) fun _ => cons false).eval ![[true]] = [true, false, true] := by
  decide

example : (smash (2 : Fin 3)).eval ![[0, 1], [0, 0, 0]] = List.replicate 6 2 := by decide

/-! ## Functions denoted by limited unary terms -/

example : ∃ c : Cobham Bool 1, c.Limited ∧ ∀ x, c.eval (fun _ => x) = x :=
  ⟨proj 0, trivial, fun _ => rfl⟩

example : ∃ c : Cobham Bool 1, c.Limited ∧ ∀ x, c.eval (fun _ => x) = true :: false :: x :=
  ⟨comp (cons true) fun _ => cons false, by simp, fun _ => rfl⟩

example : ∃ c : Cobham (Fin 3) 1, c.Limited ∧
    ∀ x, c.eval (fun _ => x) = List.replicate (x.length * x.length) 0 :=
  ⟨comp (smash 0) fun _ => proj 0, by simp, fun _ => rfl⟩

/-- The recursion in `unaryLength` computes the unary length, for any parameter vector. -/
private theorem unaryLength_rec (v : Fin 0 → List Bool) (x : List Bool) :
    recNotation empty.eval (fun _ => (comp (cons true) fun _ => proj 1).eval) v x =
      List.replicate x.length true := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [ih, List.replicate_succ]

/-- Unary length is denoted by a limited term: its bound `x ↦ true :: x` is a limited term,
and the recursion is length-bounded by it. -/
example : ∃ c : Cobham Bool 1, c.Limited ∧
    ∀ x, c.eval (fun _ => x) = List.replicate x.length true := by
  refine ⟨unaryLength, ?_, fun x => ?_⟩
  · simp only [unaryLength, limited_boundedRec, limited_empty, limited_comp, limited_cons,
      limited_proj, implies_true, true_and]
    intro v x
    simp [unaryLength_rec]
  · simp [unaryLength, unaryLength_rec]

end CslibTests.Cobham
