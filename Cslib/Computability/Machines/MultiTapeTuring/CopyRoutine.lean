/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]

def copy₁ : MultiTapeTM 2 (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
lemma copy₁_eval_list {tapes : Fin 2 → List (List α)} :
  copy₁.eval_list tapes =
    Part.some (Function.update tapes 1 (((tapes 0).headD []) :: tapes 1)) := by
  sorry

/--
A Turing machine that copies the first word on tape `i` to tape `j`.
If Tape `i` is empty, pushes the empty word to tape `j`.
-/
public def copy {k : ℕ} (i j : ℕ)
  (h_neq : i ≠ j := by decide)
  (h_i_lt : i < k := by decide)
  (h_j_lt : j < k := by decide) :
  MultiTapeTM k (WithSep α) :=
  copy₁.with_tapes [⟨i, h_i_lt⟩, ⟨j, h_j_lt⟩].get (by intro x y; grind)

@[simp, grind =]
public lemma copy_eval_list
  {k : ℕ} {i j : ℕ} {h_neq : i ≠ j} {h_i_lt : i < k} {h_j_lt : j < k}
  {tapes : Fin k → List (List α)} :
  (copy i j (h_neq := h_neq) (h_i_lt) (h_j_lt)).eval_list tapes = Part.some
    (Function.update tapes ⟨j, h_j_lt⟩
      (((tapes ⟨i, h_i_lt⟩).headD []) :: (tapes ⟨j, h_j_lt⟩))) := by
  have h_inj : [(⟨i, h_i_lt⟩ : Fin k), ⟨j, h_j_lt⟩].get.Injective := by intro x y; grind
  simp_all [copy]

end Routines

end Turing
