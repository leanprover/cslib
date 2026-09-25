/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.LupanovConstruction
public import Cslib.Computability.Circuit.Complexity

/-!
# Completeness of the De Morgan basis

Every Boolean function has a De Morgan circuit, by the Lupanov construction with no data
bits, so the basis is complete and `complexity interpretation f` is the circuit complexity of
`f` over it, for any number of outputs. This agrees with the standard measure of
[Jukna, Chapter 1][Jukna2012] up to the counting of constants and negations; see
`Cslib.Computability.Circuit.Boolean.Basic`.

## References

* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

public section

namespace Cslib.Circuits.Boolean

/-- Every Boolean function has a De Morgan circuit. -/
instance : interpretation.IsComplete where
  exists_computes_single f := by
    obtain ⟨c, hc, -⟩ :=
      (Lupanov.synthesis (d := 0) (s := 1) f Nat.one_pos).exists_circuit
    exact ⟨c, hc⟩

end Cslib.Circuits.Boolean
