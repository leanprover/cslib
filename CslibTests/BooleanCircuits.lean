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
    ∃ g ≤ 1, ∃ c : Circuit signature 0 g 1, c.Computes (fun _ => value) :=
  (Synthesis.const (s := inputs 0) value).exists_circuit

example {n : ℕ} (i : Fin n) :
    ∃ g ≤ 0, ∃ c : Circuit signature n g 1, c.Computes (fun x => x i) := by
  have h : Synthesis (inputs n) {fun x => x i} 0 :=
    Synthesis.of_subset (Set.singleton_subset_iff.mpr ⟨i, rfl⟩)
  exact h.exists_circuit

example : ¬ (Circuit.id signature 1).Computes (fun x => !x 0) := by
  intro h
  have := h (fun _ => true)
  simp at this

private def conjunction : BooleanFunction 2 := fun x => x 0 && x 1

example : ∃ g ≤ 2, ∃ c : Circuit signature 2 g 2,
    ∀ x, c.eval interpretation x 0 = conjunction x ∧
      c.eval interpretation x 1 = !conjunction x := by
  have hand : Synthesis (inputs 2) {conjunction} 1 :=
    Synthesis.gate .and (fun i x => x i) (fun i => ⟨i, rfl⟩)
  have hkeep : Synthesis (inputs 2 ∪ {conjunction}) {conjunction} 0 :=
    Synthesis.of_subset Set.subset_union_right
  have h := hand.comp (hkeep.union hkeep.not)
  obtain ⟨g, p, hg, _, hout⟩ := h 0 .empty (inputs_subset_available _)
  obtain ⟨w, hw⟩ := mem_available.mp (hout (Set.mem_union_left _ (Set.mem_singleton _)))
  obtain ⟨v, hv⟩ := mem_available.mp (hout (Set.mem_union_right _ (Set.mem_singleton _)))
  let c : Circuit signature 2 g 2 := ⟨p, Fin.cases w (fun _ => v)⟩
  exact ⟨g, hg, c, fun x => ⟨hw x, hv x⟩⟩

example : computableFunctions 0 0 = ∅ := by
  apply Finset.card_eq_zero.mp
  simpa using card_computableFunctions_mul_factorial_le 0 0

example : (fun x : Fin 1 → Bool => x 0) ∈ computableFunctions 1 0 := by
  exact mem_computableFunctions.mpr ⟨0, le_rfl, Circuit.id signature 1, by intro x; rfl⟩

example (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : BooleanFunction n,
      (∀ {g} (c : Circuit signature n g 1),
        c.Computes f → 2 ^ n / (n : ℝ) < (c.size : ℝ)) ∧
      ∃ g, ∃ c : Circuit signature n g 1,
        c.Computes f ∧ (c.size : ℝ) ≤ (1 + ε) * 2 ^ n / n := by
  obtain ⟨N, hN⟩ := Shannon.exists_hard_function
  obtain ⟨M, hM⟩ := Lupanov.exists_circuit ε hε
  refine ⟨max N M, fun n hn => ?_⟩
  obtain ⟨f, hf⟩ := hN n ((le_max_left N M).trans hn)
  exact ⟨f, hf, hM n ((le_max_right N M).trans hn) f⟩

end CslibTests.BooleanCircuits
