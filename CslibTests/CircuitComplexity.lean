/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.Synthesis
import Cslib.Computability.Circuit.RelativeComplexity

/-!
# Circuit complexity tests

Upper bounds on the extended complexity of De Morgan circuits from synthesis, and the calculus
of support and relative complexity.
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

variable {n m k : ℕ}

example (S : Set (BitString n)) (f : BitString n → BitString m) :
    ecomplexityOn interpretation S f ≤ ecomplexity interpretation f :=
  ecomplexityOn_le_ecomplexity

-- Relative complexity is complexity on the graph.
example (F : BitString n → BitString m) (G : BitString n → BitString k) :
    ecomplexityGiven interpretation F G =
      ecomplexityOn interpretation (graph G) (fun z => F (z ∘ Fin.castAdd k)) :=
  ecomplexityGiven_eq_ecomplexityOn_graph F G

example (F : BitString n → BitString m) (G : BitString n → BitString k) :
    ecomplexityGiven interpretation F G ≤ ecomplexity interpretation F ∧
      ecomplexity interpretation F ≤
        ecomplexity interpretation G + ecomplexityGiven interpretation F G :=
  ⟨ecomplexityGiven_le_ecomplexity F G, ecomplexity_le_add_ecomplexityGiven F G⟩

-- Given `F` together with more information, `F` itself is free.
example (F : BitString n → BitString m) (G : BitString n → BitString k) :
    ecomplexityGiven interpretation F (fun x => Fin.append (F x) (G x)) = 0 :=
  nonpos_iff_eq_zero.mp ((ecomplexityGiven_append_le F F G).trans_eq (ecomplexityGiven_self F))

end CslibTests.CircuitComplexity
