/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuits.Program

/-!
# Circuits

A circuit is a straight-line `Program` together with a choice of output wires.
Any input or internal-gate wire may be designated as an output, and designating
an output is free: projections and duplicated outputs cost no gates. The size
of a circuit is its gate count and its depth is the maximum depth of a
designated output wire.

A dependent pair `Σ gateCount, Circuit σ inputCount gateCount outputCount`
hides the gate count for constructions that compute it along the way.

For the standard Boolean circuit model, see [Arora and Barak, Section 6.1][AroraBarak09].
Here a topological ordering is part of the representation, and the Boolean gate
basis is generalized to an arbitrary `Signature` and `Interpretation`. Our size
counts only operation gates; Arora and Barak count all nodes, including inputs.
An output wire may also supply a later gate.

This file defines evaluation (`Circuit.eval`), the flattened views
`Circuit.computation` and `Circuit.trace`, the zero-gate identity circuit
`Circuit.id`, and the structural bounded-fan-in predicate
`Circuit.FanInAtMost`. Evaluation commutes with homomorphisms
(`Circuit.map_eval`).

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*,
  Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits

universe v u u₁ u₂

variable {σ : Signature.{v}} {inputCount gateCount outputCount : Nat}
variable {U : Type u} {U₁ : Type u₁} {U₂ : Type u₂}

/-- A straight-line program with designated output wires. -/
structure Circuit (σ : Signature) (inputCount gateCount outputCount : Nat) where
  /-- The internal gates of the circuit. -/
  program : Program σ inputCount gateCount
  /-- The input or internal-gate wire carrying each output. -/
  outputs : Fin outputCount → Wire inputCount gateCount

/-- The zero-gate identity circuit, whose outputs are its inputs. -/
def Circuit.id (σ : Signature) (inputCount : Nat) : Circuit σ inputCount 0 inputCount where
  program := .empty
  outputs := fun input => Wire.input input

/-- Every gate in a circuit has at most `r` arguments. -/
def Circuit.FanInAtMost (c : Circuit σ inputCount gateCount outputCount) (r : Nat) : Prop :=
  c.program.FanInAtMost r

/-- Bounded fan-in is decidable for every concrete circuit. -/
instance Circuit.instDecidableFanInAtMost
    (c : Circuit σ inputCount gateCount outputCount)
    (r : Nat) : Decidable (c.FanInAtMost r) :=
  Program.instDecidableFanInAtMost c.program r

/-- The number of gates in a circuit. Designating outputs is free. -/
def Circuit.size (_ : Circuit σ inputCount gateCount outputCount) : Nat :=
  gateCount

/-- The depth of every designated output wire in a circuit. -/
def Circuit.outputDepths (c : Circuit σ inputCount gateCount outputCount) : Fin outputCount → Nat :=
  c.program.wireDepths ∘ c.outputs

/-- The maximum depth of a designated output wire in a circuit. -/
def Circuit.depth (c : Circuit σ inputCount gateCount outputCount) : Nat :=
  Fin.foldl outputCount (fun depth k => max depth (c.outputDepths k)) 0

/-- Read the designated output wires after evaluating the program. -/
def Circuit.eval
    (c : Circuit σ inputCount gateCount outputCount)
    (i : Interpretation σ U)
    (x : Fin inputCount → U) : Fin outputCount → U :=
  c.program.trace i x ∘ c.outputs

@[simp] theorem Circuit.eval_id
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U) :
    (Circuit.id σ inputCount).eval interpretation input = input := by
  funext output
  exact Program.trace_input .empty interpretation input output

/-- Evaluating a circuit commutes with a homomorphism. -/
theorem Circuit.map_eval
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (c : Circuit σ inputCount gateCount outputCount)
    (h : Homomorphism i₁ i₂)
    (x : Fin inputCount → U₁) :
    h.map ∘ c.eval i₁ x = c.eval i₂ (h.map ∘ x) := by
  funext k
  exact congrFun (c.program.map_trace h x) (c.outputs k)

/-- All internal-gate values followed by the designated output values. -/
def Circuit.computation
    (c : Circuit σ inputCount gateCount outputCount)
    (i : Interpretation σ U)
    (x : Fin inputCount → U) : Fin (gateCount + outputCount) → U :=
  Fin.addCases (c.program.eval i x) (c.eval i x)

/-- The input and internal-gate values followed by the designated outputs. -/
def Circuit.trace
    (c : Circuit σ inputCount gateCount outputCount)
    (i : Interpretation σ U)
    (x : Fin inputCount → U) : Fin (inputCount + gateCount + outputCount) → U :=
  Fin.addCases (c.program.trace i x) (c.eval i x)

end Cslib.Circuits
