/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.Synthesis
import Cslib.Computability.Circuit.Complexity

/-!
# Circuit complexity tests

Upper bounds on the extended and natural-number complexity of De Morgan circuits from synthesis,
and the calculus of support complexity, including the empty support on zero inputs.
The natural-number examples assume completeness of the basis.
-/

namespace CslibTests.CircuitComplexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

example : ecomplexity interpretation (single fun x : BitString 2 => x 0 && x 1) ≤ 1 := by
  have h := (Synthesis.of_mem (I := interpretation) (s := inputs 2) ⟨0, rfl⟩).and
    (Synthesis.of_mem (I := interpretation) (s := inputs 2) ⟨1, rfl⟩)
  exact h.ecomplexity_le

example {n : ℕ} (i : Fin n) : ecomplexity interpretation (single fun x => x i) = 0 := by
  have h : Synthesis interpretation (inputs n) {fun x => x i} 0 :=
    Synthesis.of_subset (Set.singleton_subset_iff.mpr ⟨i, rfl⟩)
  exact nonpos_iff_eq_zero.mp h.ecomplexity_le

section Complete

variable [interpretation.IsComplete]

example : complexity interpretation (single fun x : BitString 2 => !(x 0 && x 1)) ≤ 2 := by
  have h := (Synthesis.of_mem (I := interpretation) (s := inputs 2) ⟨0, rfl⟩).and
    (Synthesis.of_mem (I := interpretation) (s := inputs 2) ⟨1, rfl⟩)
  have hnot := (Synthesis.of_mem (I := interpretation) (s := inputs 1) ⟨0, rfl⟩).not
  exact (complexity_comp_le (single fun x : BitString 2 => x 0 && x 1)
    (single fun x : BitString 1 => !x 0)).trans (Nat.add_le_add h.complexity_le hnot.complexity_le)

-- On inputs whose second bit is true, conjunction is just a free projection.
example : complexityOn interpretation {x : BitString 2 | x 1 = true}
    (single fun x => x 0 && x 1) = 0 := by
  calc
    _ = complexityOn interpretation {x : BitString 2 | x 1 = true}
        (fun x => x ∘ fun _ : Fin 1 => 0) :=
      complexityOn_congr fun x hx => by
        funext i
        change x 1 = true at hx
        simp [single, hx]
    _ = 0 := complexityOn_wiring _

end Complete

-- Even on an empty support, a zero-input circuit needs a gate to provide its output.
example : ecomplexityOn interpretation ∅ (single fun _ : BitString 0 => false) = 1 := by
  apply le_antisymm
  · have h : Synthesis interpretation (inputs 0) {fun _ => false} 1 := Synthesis.const false
    exact ecomplexityOn_le_ecomplexity.trans h.ecomplexity_le
  · apply le_ecomplexityOn_iff.mpr
    intro c _
    have hsize : 1 ≤ c.size := by
      cases c.outputs 0 with
      | input i => exact i.elim0
      | gate i => have := i.isLt; omega
    exact_mod_cast hsize

variable {n m : ℕ}

example (S : Set (BitString n)) (f : BitString n → BitString m) :
    ecomplexityOn interpretation S f ≤ ecomplexity interpretation f :=
  ecomplexityOn_le_ecomplexity

end CslibTests.CircuitComplexity
