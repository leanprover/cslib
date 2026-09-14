/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.Lupanov

/-!
# Boolean synthesis tests

Zero-input constants, zero-gate projections, and shared AND/NAND outputs.
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

example : ∃ g ≤ 2, ∃ c : Circuit signature 2 g 2,
    ∀ x, c.eval interpretation x 0 = conjunction x ∧
      c.eval interpretation x 1 = !conjunction x := by
  have hand : Synthesis interpretation (inputs 2) {conjunction} 1 :=
    Synthesis.gate (I := interpretation) .and (fun i x => x i) (fun i => ⟨i, rfl⟩)
  have hkeep : Synthesis interpretation (inputs 2 ∪ {conjunction}) {conjunction} 0 :=
    Synthesis.of_subset Set.subset_union_right
  have h := hand.comp (hkeep.union hkeep.not)
  have hout : Synthesis interpretation (inputs 2)
      (Set.range fun i : Fin 2 => if i = 0 then conjunction else fun x => !conjunction x) 2 :=
    h.mono Set.Subset.rfl (by rintro _ ⟨i, rfl⟩; dsimp only; split <;> simp) le_rfl
  obtain ⟨g, hg, c, hc⟩ := hout.exists_circuit_family
  exact ⟨g, hg, c, fun x => ⟨by simpa using hc x 0, by simpa using hc x 1⟩⟩

end CslibTests.BooleanCircuits
