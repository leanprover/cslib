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
  obtain ⟨⟨g, p⟩, hg, _, hout⟩ := h ⟨0, .empty⟩ (by
    rintro _ ⟨i, rfl⟩
    exact ⟨Wire.input i, fun x => Program.trace_input _ _ x i⟩)
  obtain ⟨w, hw⟩ := hout (Set.mem_union_left _ (Set.mem_singleton _))
  obtain ⟨v, hv⟩ := hout (Set.mem_union_right _ (Set.mem_singleton _))
  let c : Circuit signature 2 g 2 := ⟨p, Fin.cases w (fun _ => v)⟩
  exact ⟨g, hg, c, fun x => ⟨hw x, hv x⟩⟩

end CslibTests.BooleanCircuits
