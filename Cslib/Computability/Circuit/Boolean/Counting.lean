/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Circuit.Counting

import Mathlib.Tactic.Linarith

/-!
# Counting De Morgan circuits

This file specializes the generic circuit counting bound to the five De Morgan operations,
all of arity at most two. The resulting factorial correction is used in Shannon's lower bound.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n s : ℕ}

/-- Boolean functions on `n` inputs computable with at most `s` De Morgan gates. -/
noncomputable abbrev computableFunctions (n s : ℕ) : Finset (BooleanFunction n) :=
  Circuits.computableFunctions interpretation n s

theorem mem_computableFunctions {f : BooleanFunction n} :
    f ∈ computableFunctions n s ↔
      ∃ c : Circuit signature n 1, c.Computes interpretation (fun x _ => f x) ∧ c.size ≤ s :=
  Circuits.mem_computableFunctions

/-- The De Morgan counting bound, accounting for gate relabelings. -/
theorem card_computableFunctions_mul_factorial_le (n s : ℕ) :
    (computableFunctions n s).card * s.factorial ≤
      (s + 1) * (5 * (n + s + 1) ^ 2) ^ s * (n + s) := by
  apply Circuits.card_computableFunctions_mul_factorial_le interpretation n s
  · nlinarith [Nat.le_mul_self (n + s + 1)]
  · intro g hg
    have h := Line.card_le (σ := signature) n g 2 (fun op => by cases op <;> simp)
    simp only [Op.card] at h
    exact h.trans (Nat.mul_le_mul_left 5
      (Nat.pow_le_pow_left (by omega : n + g + 1 ≤ n + s + 1) 2))

end Cslib.Circuits.Boolean
