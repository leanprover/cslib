/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.Synthesis
import Cslib.Computability.Circuit.Complexity

/-!
# Circuit complexity tests

Upper bounds on the extended complexity of De Morgan circuits from synthesis, and the calculus
of support complexity.
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

variable {n m : ℕ}

example (S : Set (BitString n)) (f : BitString n → BitString m) :
    ecomplexityOn interpretation S f ≤ ecomplexity interpretation f :=
  ecomplexityOn_le_ecomplexity

end CslibTests.CircuitComplexity
