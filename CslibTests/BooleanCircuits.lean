/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.Counting
import Cslib.Computability.Circuit.Boolean.Lupanov
import Cslib.Computability.Circuit.Boolean.Shannon

/-!
# Boolean circuit tests

Zero-input constants, zero-gate projections, shared AND/NAND outputs, and compatibility of
the Shannon and Lupanov bounds.
-/

namespace CslibTests.BooleanCircuits

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

example (value : Bool) :
    ∃ c : Circuit signature 0 1, c.Computes interpretation (fun _ _ => value) ∧ c.size ≤ 1 :=
  (Synthesis.const (s := inputs 0) value).exists_circuit

example {n : ℕ} (i : Fin n) :
    ∃ c : Circuit signature n 1, c.Computes interpretation (fun x _ => x i) ∧ c.size ≤ 0 := by
  have h : Synthesis interpretation (inputs n) {fun x => x i} 0 :=
    Synthesis.of_subset (Set.singleton_subset_iff.mpr ⟨i, rfl⟩)
  exact h.exists_circuit

example : ¬ (Circuit.id signature 1).Computes interpretation (fun x _ => !x 0) := by
  intro h
  have := congrFun (h fun _ => true) 0
  simp at this

private def conjunction : BooleanFunction 2 := fun x => x 0 && x 1

private theorem conjunction_synthesis : Synthesis interpretation (inputs 2) {conjunction} 1 :=
  Synthesis.gate (I := interpretation) .and (fun i x => x i) (fun i => ⟨i, rfl⟩)

example : ∃ c : Circuit signature 2 2,
    (∀ x, c.eval interpretation x 0 = conjunction x ∧
      c.eval interpretation x 1 = !conjunction x) ∧ c.size ≤ 2 := by
  have h := conjunction_synthesis.comp
    (Synthesis.of_mem (Set.mem_union_right _ (Set.mem_singleton conjunction))).not
  have hout : Synthesis interpretation (inputs 2)
      (Set.range fun i : Fin 2 => if i = 0 then conjunction else fun x => !conjunction x) 2 :=
    h.mono Set.Subset.rfl (by rintro _ ⟨i, rfl⟩; dsimp only; split <;> simp) le_rfl
  obtain ⟨c, hc, hg⟩ := hout.exists_circuit_outputs
  exact ⟨c, fun x => ⟨by simpa using congrFun (hc x) 0, by simpa using congrFun (hc x) 1⟩, hg⟩

example : computableFunctions 0 0 = ∅ := by
  apply Finset.card_eq_zero.mp
  simpa using card_computableFunctions_mul_factorial_le 0 0

example : (fun x : Fin 1 → Bool => x 0) ∈ computableFunctions 1 0 :=
  mem_computableFunctions.mpr
    ⟨Circuit.id signature 1, by simp [Circuit.Computes, funext_iff, Fin.forall_fin_one], le_rfl⟩

example (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : BooleanFunction n,
      (∀ c : Circuit signature n 1,
        c.Computes interpretation (fun x _ => f x) → 2 ^ n / (n : ℝ) < (c.size : ℝ)) ∧
      ∃ c : Circuit signature n 1,
        c.Computes interpretation (fun x _ => f x) ∧ (c.size : ℝ) ≤ (1 + ε) * 2 ^ n / n := by
  obtain ⟨N, hN⟩ := Shannon.exists_hard_function
  obtain ⟨M, hM⟩ := Lupanov.exists_circuit ε hε
  refine ⟨max N M, fun n hn => ?_⟩
  obtain ⟨f, hf⟩ := hN n ((le_max_left N M).trans hn)
  exact ⟨f, hf, hM n ((le_max_right N M).trans hn) f⟩

end CslibTests.BooleanCircuits
