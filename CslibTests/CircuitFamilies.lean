/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.Family

/-!
# Circuit family tests

Slices of languages built from slices, a constant-size family for the empty language, unary
languages in P/poly, and compatibility of the Shannon and Lupanov bounds for families.
-/

namespace CslibTests.CircuitFamilies

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

example (f : ∀ n, BooleanFunction n) : (Language.ofSlices f).slice 3 = f 3 := by
  simp

-- Every slice of the empty language is the constant `false`, which costs one gate.
example : (0 : Language Bool) ∈ SIZE interpretation fun _ => 1 := by
  rw [mem_SIZE_iff_complexity_le]
  intro n
  have h : (0 : Language Bool).slice n = fun _ => false := by
    funext x
    rw [Bool.eq_iff_iff]
    simp [Language.notMem_zero]
  rw [h]
  exact (Synthesis.const false).complexity_le

-- The language of all-`true` words is unary.
example : ({w | ∀ b ∈ w, b = true} : Language Bool) ∈ PPoly :=
  mem_PPoly_of_unary fun _ hw => hw

-- The same language defeats every family of size `2ⁿ/n`, yet has a family of size
-- `(1 + ε) 2ⁿ/n`, at all large lengths.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ L : Language Bool, ∃ N : ℕ,
      (∀ F : CircuitFamily signature, F.Decides interpretation L →
        ∀ n ≥ N, 2 ^ n / (n : ℝ) < (F n).size) ∧
      ∃ F : CircuitFamily signature, F.Decides interpretation L ∧
        ∀ n ≥ N, ((F n).size : ℝ) ≤ (1 + ε) * 2 ^ n / n := by
  obtain ⟨L, N, hL⟩ := exists_language_lt_size
  obtain ⟨M, hM⟩ := exists_decides_size_le ε hε
  obtain ⟨F, hF, hs⟩ := hM L
  exact ⟨L, max N M, fun F hF n hn => hL F hF n ((le_max_left N M).trans hn),
    F, hF, fun n hn => hs n ((le_max_right N M).trans hn)⟩

end CslibTests.CircuitFamilies
