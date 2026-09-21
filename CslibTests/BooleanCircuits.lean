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

Zero-input constants, zero-gate projections, shared outputs, and compatibility of the
Shannon and Lupanov bounds.
-/

namespace CslibTests.BooleanCircuits

open Cslib.Circuits Cslib.Circuits.Boolean

example (value : Bool) :
    ∃ g ≤ 1, ∃ c : Circuit signature 0 g 1, c.Computes interpretation (fun _ => value) :=
  (Synthesis.const (s := inputs 0) value).exists_circuit

example {n : ℕ} (i : Fin n) :
    ∃ g ≤ 0, ∃ c : Circuit signature n g 1, c.Computes interpretation (fun x => x i) := by
  have h : Synthesis interpretation (inputs n) {fun x => x i} 0 :=
    Synthesis.of_subset (Set.singleton_subset_iff.mpr ⟨i, rfl⟩)
  exact h.exists_circuit

example : ¬ (Circuit.id signature 1).Computes interpretation (fun x => !x 0) := by
  intro h
  have := h (fun _ => true)
  simp at this

private def conjunction : BooleanFunction 2 := fun x => x 0 && x 1

private theorem conjunction_synthesis : Synthesis interpretation (inputs 2) {conjunction} 1 :=
  Synthesis.gate (I := interpretation) .and (fun i x => x i) (fun i => ⟨i, rfl⟩)

example : ∃ g ≤ 2, ∃ c : Circuit signature 2 g 2,
    ∀ x, c.eval interpretation x 0 = conjunction x ∧
      c.eval interpretation x 1 = !conjunction x := by
  have h := conjunction_synthesis.comp
    (Synthesis.not_of_mem (Set.mem_union_right _ (Set.mem_singleton conjunction)))
  have hout : Synthesis interpretation (inputs 2)
      (Set.range fun i : Fin 2 => if i = 0 then conjunction else fun x => !conjunction x) 2 :=
    h.mono Set.Subset.rfl (by rintro _ ⟨i, rfl⟩; dsimp only; split <;> simp) le_rfl
  obtain ⟨g, hg, c, hc⟩ := hout.exists_circuit_family
  exact ⟨g, hg, c, fun x => ⟨by simpa using hc x 0, by simpa using hc x 1⟩⟩

example : computableFunctions 0 0 = ∅ := by
  apply Finset.card_eq_zero.mp
  simpa using card_computableFunctions_mul_factorial_le 0 0

example : (fun x : Fin 1 → Bool => x 0) ∈ computableFunctions 1 0 := by
  exact mem_computableFunctions.mpr ⟨0, le_rfl, Circuit.id signature 1, by intro x; rfl⟩

example (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : BooleanFunction n,
      (∀ {g} (c : Circuit signature n g 1),
        c.Computes interpretation f → 2 ^ n / (n : ℝ) < (c.size : ℝ)) ∧
      ∃ g, ∃ c : Circuit signature n g 1,
        c.Computes interpretation f ∧ (c.size : ℝ) ≤ (1 + ε) * 2 ^ n / n := by
  obtain ⟨N, hN⟩ := Shannon.exists_hard_function
  obtain ⟨M, hM⟩ := Lupanov.exists_circuit ε hε
  refine ⟨max N M, fun n hn => ?_⟩
  obtain ⟨f, hf⟩ := hN n ((le_max_left N M).trans hn)
  exact ⟨f, hf, hM n ((le_max_right N M).trans hn) f⟩

end CslibTests.BooleanCircuits
