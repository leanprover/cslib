/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.Synthesis
import Cslib.Computability.Circuit.Composition

/-!
# Circuit composition tests

Sequential and parallel composition of De Morgan circuits obtained from synthesis.
-/

namespace CslibTests.CircuitComposition

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

private theorem and_circuit : ∃ c : Circuit signature 2 1,
    c.Computes interpretation (single fun x => x 0 && x 1) ∧ c.size ≤ 1 := by
  have h := (Synthesis.of_mem (I := interpretation) (s := inputs 2) ⟨0, rfl⟩).and
    (Synthesis.of_mem (I := interpretation) (s := inputs 2) ⟨1, rfl⟩)
  exact h.exists_circuit

private theorem not_circuit : ∃ c : Circuit signature 1 1,
    c.Computes interpretation (single fun x => !x 0) ∧ c.size ≤ 1 := by
  have h := (Synthesis.of_mem (I := interpretation) (s := inputs 1) ⟨0, rfl⟩).not
  exact h.exists_circuit

-- Feeding AND into NOT computes NAND with the two gates.
example : ∃ c : Circuit signature 2 1,
    c.Computes interpretation (single fun x => !(x 0 && x 1)) ∧ c.size ≤ 2 := by
  obtain ⟨c, hc, hcs⟩ := and_circuit
  obtain ⟨d, hd, hds⟩ := not_circuit
  exact ⟨d.comp c, hc.comp hd, by simp only [Circuit.size_comp]; omega⟩

-- AND and its negation side by side, from separate circuits.
example : ∃ c : Circuit signature 2 (1 + 1),
    c.Computes interpretation
      (fun x => Fin.append (fun _ : Fin 1 => x 0 && x 1) fun _ : Fin 1 => !(x 0 && x 1)) ∧
      c.size ≤ 3 := by
  obtain ⟨c, hc, hcs⟩ := and_circuit
  obtain ⟨d, hd, hds⟩ := not_circuit
  exact ⟨c.append (d.comp c), hc.append (hc.comp hd),
    by simp only [Circuit.size_append, Circuit.size_comp]; omega⟩

end CslibTests.CircuitComposition
