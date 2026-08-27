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

This file defines evaluation (`Circuit.eval`), the flattened views
`Circuit.computation` and `Circuit.trace`, the zero-gate identity circuit
`Circuit.id`, and the structural bounded-fan-in predicate
`Circuit.FanInAtMost`. Evaluation commutes with homomorphisms
(`Circuit.map_eval`).
-/

@[expose] public section

namespace Cslib.Circuits

/-- A straight-line program with designated output wires. -/
structure Circuit (σ : Signature) (n g m : Nat) where
  /-- The internal gates of the circuit. -/
  program : Program σ n g
  /-- The input or internal-gate wire carrying each output. -/
  outputs : Fin m → Wire n g

/-- The zero-gate identity circuit, whose outputs are its inputs. -/
def Circuit.id (σ : Signature) (n : Nat) : Circuit σ n 0 n where
  program := .empty
  outputs := fun input => Wire.input input

/-- Every gate in a circuit has at most `r` arguments. -/
def Circuit.FanInAtMost (c : Circuit σ n g m) (r : Nat) : Prop :=
  c.program.FanInAtMost r

/-- Bounded fan-in is decidable for every concrete circuit. -/
instance Circuit.instDecidableFanInAtMost
    (c : Circuit σ n g m)
    (r : Nat) : Decidable (c.FanInAtMost r) :=
  Program.instDecidableFanInAtMost c.program r

/-- The number of gates in a circuit. Designating outputs is free. -/
def Circuit.size (_ : Circuit σ n g m) : Nat :=
  g

/-- The depth of every designated output wire in a circuit. -/
def Circuit.outputDepths (c : Circuit σ n g m) : Fin m → Nat :=
  c.program.wireDepths ∘ c.outputs

/-- The maximum depth of a designated output wire in a circuit. -/
def Circuit.depth (c : Circuit σ n g m) : Nat :=
  Fin.foldl m (fun depth k => max depth (c.outputDepths k)) 0

/-- Read the designated output wires after evaluating the program. -/
def Circuit.eval
  (c : Circuit σ n g m)
  (i : Interpretation σ U)
  (x : Fin n → U) : Fin m → U :=
  c.program.trace i x ∘ c.outputs

@[simp] theorem Circuit.eval_id
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (Circuit.id σ n).eval interpretation input = input := by
  funext output
  exact Program.trace_input .empty interpretation input output

/-- Evaluating a circuit commutes with a homomorphism. -/
theorem Circuit.map_eval
  {i₁ : Interpretation σ U₁}
  {i₂ : Interpretation σ U₂}
  (c : Circuit σ n g m)
  (h : Homomorphism i₁ i₂)
  (x : Fin n → U₁) :
  h.map ∘ c.eval i₁ x = c.eval i₂ (h.map ∘ x) := by
  funext k
  exact congrFun (c.program.map_trace h x) (c.outputs k)

/-- All internal-gate values followed by the designated output values. -/
def Circuit.computation
  (c : Circuit σ n g m)
  (i : Interpretation σ U)
  (x : Fin n → U) : Fin (g + m) → U :=
  Fin.addCases (c.program.eval i x) (c.eval i x)

/-- The input and internal-gate values followed by the designated outputs. -/
def Circuit.trace
  (c : Circuit σ n g m)
  (i : Interpretation σ U)
  (x : Fin n → U) : Fin (n + g + m) → U :=
  Fin.addCases (c.program.trace i x) (c.eval i x)

end Cslib.Circuits
