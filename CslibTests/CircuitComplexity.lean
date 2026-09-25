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
example (f : BitString n → BitString m) (g : BitString n → BitString k) :
    ecomplexityGiven interpretation f g =
      ecomplexityOn interpretation (graph g) (fun z => f (z ∘ Fin.castAdd k)) :=
  ecomplexityGiven_eq_ecomplexityOn_graph f g

example (f : BitString n → BitString m) (g : BitString n → BitString k) :
    ecomplexityGiven interpretation f g ≤ ecomplexity interpretation f ∧
      ecomplexity interpretation f ≤
        ecomplexity interpretation g + ecomplexityGiven interpretation f g :=
  ⟨ecomplexityGiven_le_ecomplexity f g, ecomplexity_le_add_ecomplexityGiven f g⟩

-- A circuit reading `x` and `g x` that outputs `f x` bounds the relative complexity.
example (f : BitString n → BitString m) (g : BitString n → BitString k)
    (c : Circuit signature (n + k) m) (hc : ∀ x, c.eval interpretation (Fin.append x (g x)) = f x) :
    ecomplexityGiven interpretation f g ≤ c.size :=
  (ecomplexityGiven_le_iff f g).mpr ⟨c, hc, le_rfl⟩

-- Given `f` together with more information, `f` itself is free.
example (f : BitString n → BitString m) (g : BitString n → BitString k) :
    ecomplexityGiven interpretation f (fun x => Fin.append (f x) (g x)) = 0 :=
  nonpos_iff_eq_zero.mp ((ecomplexityGiven_append_le f f g).trans_eq (ecomplexityGiven_self f))

end CslibTests.CircuitComplexity
