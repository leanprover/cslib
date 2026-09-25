/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Program

/-!
# Circuits

A circuit is a straight-line `Program` together with a choice of output wires.
Any input or internal-gate wire may be designated as an output, and designating
an output is free: projections and duplicated outputs cost no gates. The size
of a circuit is its gate count and its depth is the maximum depth of a
designated output wire.

For the standard Boolean circuit model, see [Arora and Barak, Section 6.1][AroraBarak09].
Here a topological ordering is part of the representation, and the Boolean gate
basis is generalized to an arbitrary `Signature` and `Interpretation`. Our size
counts only operation gates; Arora and Barak count all nodes, including inputs.
An output wire may also supply a later gate.

A circuit computes a function with as many values as it has outputs when its designated
outputs agree with the function on every input; a single-valued function is computed by a
circuit with one output. Evaluation commutes with homomorphisms of interpretations.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*,
  Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits

universe v u u₁ u₂

variable {σ : Signature.{v}} {inputCount outputCount : Nat}
variable {U : Type u} {U₁ : Type u₁} {U₂ : Type u₂}

/-- A straight-line program with designated output wires. -/
structure Circuit (σ : Signature) (inputCount outputCount : Nat) where
  /-- The number of gates in the program; inputs and designated outputs cost nothing. -/
  {size : Nat}
  /-- The internal gates of the circuit. -/
  program : Program σ inputCount size
  /-- The input or internal-gate wire carrying each output. -/
  outputs : Fin outputCount → Wire inputCount size

/-- The zero-gate circuit whose outputs are the inputs chosen by `select`. Projections,
duplications, and permutations of the inputs cost no gates. -/
def Circuit.wiring (σ : Signature) (select : Fin outputCount → Fin inputCount) :
    Circuit σ inputCount outputCount :=
  ⟨.empty, fun output => Wire.input (select output)⟩

/-- The zero-gate identity circuit, whose outputs are its inputs. -/
abbrev Circuit.id (σ : Signature) (inputCount : Nat) : Circuit σ inputCount inputCount :=
  Circuit.wiring σ _root_.id

@[simp] theorem Circuit.size_wiring (select : Fin outputCount → Fin inputCount) :
    (Circuit.wiring σ select).size = 0 := rfl

@[simp] theorem Circuit.program_wiring (select : Fin outputCount → Fin inputCount) :
    (Circuit.wiring σ select).program = .empty := rfl

@[simp] theorem Circuit.outputs_wiring (select : Fin outputCount → Fin inputCount) :
    (Circuit.wiring σ select).outputs = fun output => Wire.input (select output) := rfl

/-- Every gate in a circuit has at most `r` arguments. -/
def Circuit.FanInAtMost (c : Circuit σ inputCount outputCount) (r : Nat) : Prop :=
  c.program.FanInAtMost r

/-- Bounded fan-in is decidable for every concrete circuit. -/
instance Circuit.instDecidableFanInAtMost
    (c : Circuit σ inputCount outputCount)
    (r : Nat) : Decidable (c.FanInAtMost r) :=
  Program.instDecidableFanInAtMost c.program r

@[simp] theorem Circuit.fanInAtMost_wiring (select : Fin outputCount → Fin inputCount)
    (r : Nat) : (Circuit.wiring σ select).FanInAtMost r := trivial

/-- The depth of every designated output wire in a circuit. -/
def Circuit.outputDepths (c : Circuit σ inputCount outputCount) : Fin outputCount → Nat :=
  c.program.wireDepths ∘ c.outputs

/-- The maximum depth of a designated output wire in a circuit. -/
def Circuit.depth (c : Circuit σ inputCount outputCount) : Nat :=
  Fin.foldl outputCount (fun depth k => max depth (c.outputDepths k)) 0

@[simp] theorem Circuit.outputDepths_wiring (select : Fin outputCount → Fin inputCount) :
    (Circuit.wiring σ select).outputDepths = fun _ => 0 := by
  funext output
  simp only [Circuit.outputDepths, Circuit.program_wiring, Circuit.outputs_wiring,
    Function.comp_apply, Program.wireDepths, Wire.input, Fin.addCases_left]

@[simp] theorem Circuit.depth_wiring (select : Fin outputCount → Fin inputCount) :
    (Circuit.wiring σ select).depth = 0 := by
  unfold Circuit.depth
  simp only [Circuit.outputDepths_wiring, Nat.max_zero]
  clear select
  induction outputCount with
  | zero => rfl
  | succ outputCount ih => simpa only [Fin.foldl_succ] using ih

/-- Read the designated output wires after evaluating the program. -/
def Circuit.eval
    (c : Circuit σ inputCount outputCount)
    (i : Interpretation σ U)
    (x : Fin inputCount → U) : Fin outputCount → U :=
  c.program.trace i x ∘ c.outputs

/-- Output `j` of a wiring circuit is input `select j`. -/
@[simp] theorem Circuit.eval_wiring (select : Fin outputCount → Fin inputCount)
    (interpretation : Interpretation σ U) (input : Fin inputCount → U) :
    (Circuit.wiring σ select).eval interpretation input = input ∘ select := by
  funext output
  exact Program.trace_input .empty interpretation input (select output)

/-- A circuit computes `f` when its outputs agree with `f` on every input. -/
def Circuit.Computes (c : Circuit σ inputCount outputCount)
    (interpretation : Interpretation σ U) (f : (Fin inputCount → U) → Fin outputCount → U) :
    Prop :=
  ∀ x, c.eval interpretation x = f x

/-- A circuit computes `F` on the support `S` when its outputs agree with `F` on every input in
`S`; what `F` does outside `S` does not matter. -/
def Circuit.ComputesOn (c : Circuit σ inputCount outputCount)
    (interpretation : Interpretation σ U) (S : Set (Fin inputCount → U))
    (F : (Fin inputCount → U) → Fin outputCount → U) : Prop :=
  ∀ x ∈ S, c.eval interpretation x = F x

/-- Computing on every input is computing. -/
@[simp] theorem Circuit.computesOn_univ_iff (c : Circuit σ inputCount outputCount)
    (interpretation : Interpretation σ U) (F : (Fin inputCount → U) → Fin outputCount → U) :
    c.ComputesOn interpretation Set.univ F ↔ c.Computes interpretation F := by
  simp [Circuit.ComputesOn, Circuit.Computes]

/-- A circuit that computes `F` computes it on every support. -/
theorem Circuit.Computes.computesOn {c : Circuit σ inputCount outputCount}
    {interpretation : Interpretation σ U} {F : (Fin inputCount → U) → Fin outputCount → U}
    (h : c.Computes interpretation F) (S : Set (Fin inputCount → U)) :
    c.ComputesOn interpretation S F :=
  fun x _ => h x

/-- A wiring circuit computes the selection of its inputs. -/
theorem Circuit.wiring_computes (select : Fin outputCount → Fin inputCount)
    (interpretation : Interpretation σ U) :
    (Circuit.wiring σ select).Computes interpretation fun x => x ∘ select := by
  intro x
  simp

/-- Evaluating a circuit commutes with a homomorphism. -/
theorem Circuit.map_eval
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (c : Circuit σ inputCount outputCount)
    (h : Homomorphism i₁ i₂)
    (x : Fin inputCount → U₁) :
    h.map ∘ c.eval i₁ x = c.eval i₂ (h.map ∘ x) := by
  funext k
  exact congrFun (c.program.map_trace h x) (c.outputs k)

/-- All internal-gate values followed by the designated output values. -/
def Circuit.computation
    (c : Circuit σ inputCount outputCount)
    (i : Interpretation σ U)
    (x : Fin inputCount → U) : Fin (c.size + outputCount) → U :=
  Fin.addCases (c.program.eval i x) (c.eval i x)

/-- The input and internal-gate values followed by the designated outputs. -/
def Circuit.trace
    (c : Circuit σ inputCount outputCount)
    (i : Interpretation σ U)
    (x : Fin inputCount → U) : Fin (inputCount + c.size + outputCount) → U :=
  Fin.addCases (c.program.trace i x) (c.eval i x)

end Cslib.Circuits
