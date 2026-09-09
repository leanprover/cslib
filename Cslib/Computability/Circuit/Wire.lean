/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Init
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Logic.Equiv.Defs

/-!
# Circuit wires and renamings

A `Wire inputCount gateCount` refers to an original input or an internal gate.
`Wire.Renaming` fixes the original inputs and maps each gate to an input or gate
in the target namespace. This file provides identity and composition, extension
by a gate, replacement of the last gate, and renaming by a permutation.
-/

@[expose] public section

namespace Cslib.Circuits

/-- A wire is either an original input or the output of an earlier gate. -/
abbrev Wire (inputCount gateCount : Nat) := Fin (inputCount + gateCount)

/-- Regard an original input as a wire. -/
abbrev Wire.input {inputCount gateCount : Nat} (input : Fin inputCount) :
    Wire inputCount gateCount :=
  Fin.castAdd gateCount input

/-- Regard a gate output as a wire. -/
abbrev Wire.gate {inputCount gateCount : Nat} (gate : Fin gateCount) : Wire inputCount gateCount :=
  Fin.natAdd inputCount gate

/-- A renaming of gate wires that fixes every original input. Gate wires may be
sent to either inputs or gates in the target namespace. -/
structure Wire.Renaming (inputCount sourceGateCount targetGateCount : Nat) where
  /-- The target wire representing each source gate. -/
  gates : Fin sourceGateCount → Wire inputCount targetGateCount

namespace Wire.Renaming

variable {inputCount gateCount sourceGateCount middleGateCount targetGateCount : Nat}
variable {U : Type*}

/-- Apply an input-fixing wire renaming. -/
def apply (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount) :
    Wire inputCount sourceGateCount → Wire inputCount targetGateCount :=
  Fin.addCases Wire.input ρ.gates

instance : CoeFun (Wire.Renaming inputCount sourceGateCount targetGateCount)
    fun _ => Wire inputCount sourceGateCount → Wire inputCount targetGateCount :=
  ⟨apply⟩

@[simp] theorem apply_input
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount) (input : Fin inputCount) :
    ρ (Wire.input input) = Wire.input input := by
  simp [apply]

@[simp] theorem apply_gate
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount) (gate : Fin sourceGateCount) :
    ρ (Wire.gate gate) = ρ.gates gate := by
  simp [apply]

/-- The identity wire renaming. -/
def id : Wire.Renaming inputCount gateCount gateCount where
  gates := Wire.gate

@[simp] theorem id_apply (wire : Wire inputCount gateCount) :
    (id : Wire.Renaming inputCount gateCount gateCount) wire = wire := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire <;> simp [id]

/-- Compose input-fixing wire renamings. -/
def comp
    (outer : Wire.Renaming inputCount middleGateCount targetGateCount)
    (inner : Wire.Renaming inputCount sourceGateCount middleGateCount) :
    Wire.Renaming inputCount sourceGateCount targetGateCount where
  gates := outer ∘ inner.gates

@[simp] theorem comp_apply
    (outer : Wire.Renaming inputCount middleGateCount targetGateCount)
    (inner : Wire.Renaming inputCount sourceGateCount middleGateCount)
    (wire : Wire inputCount sourceGateCount) :
    (outer.comp inner) wire = outer (inner wire) := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire <;>
    simp [comp, Function.comp_apply]

/-- Include all wires into a namespace with one additional gate. -/
def castSucc : Wire.Renaming inputCount gateCount (gateCount + 1) where
  gates := fun gate => Wire.gate gate.castSucc

@[simp] theorem castSucc_apply (wire : Wire inputCount gateCount) :
    (castSucc : Wire.Renaming inputCount gateCount (gateCount + 1)) wire = wire.castSucc := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp [castSucc, Fin.castSucc_castAdd]
  · simp [castSucc]

/-- Extend a renaming while replacing the new last gate by an existing wire. -/
def skipLast
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (replacement : Wire inputCount targetGateCount) :
    Wire.Renaming inputCount (sourceGateCount + 1) targetGateCount where
  gates := Fin.lastCases replacement prior.gates

theorem skipLast_gate_last
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (replacement : Wire inputCount targetGateCount) :
    prior.skipLast replacement (Wire.gate (Fin.last sourceGateCount)) = replacement := by
  rw [apply_gate]
  simp [skipLast]

@[simp] theorem skipLast_lastWire
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (replacement : Wire inputCount targetGateCount) :
    prior.skipLast replacement (Fin.last (inputCount + sourceGateCount)) = replacement := by
  rw [← Fin.natAdd_last (n := inputCount) (m := sourceGateCount)]
  exact skipLast_gate_last prior replacement

@[simp] theorem skipLast_castSucc
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (replacement : Wire inputCount targetGateCount)
    (wire : Wire inputCount sourceGateCount) :
    prior.skipLast replacement wire.castSucc = prior wire := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp [Fin.castSucc_castAdd]
  · simp [skipLast]

/-- Extend a renaming and retain the new last gate as a fresh target gate. -/
def appendLast
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount) :
    Wire.Renaming inputCount (sourceGateCount + 1) (targetGateCount + 1) where
  gates := Fin.lastCases (Wire.gate (Fin.last targetGateCount)) fun gate =>
    (prior.gates gate).castSucc

theorem appendLast_gate_last
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount) :
    prior.appendLast (Wire.gate (Fin.last sourceGateCount)) =
      Wire.gate (Fin.last targetGateCount) := by
  rw [apply_gate]
  simp [appendLast]

@[simp] theorem appendLast_lastWire
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount) :
    prior.appendLast (Fin.last (inputCount + sourceGateCount)) =
      Wire.gate (Fin.last targetGateCount) := by
  rw [← Fin.natAdd_last (n := inputCount) (m := sourceGateCount)]
  exact appendLast_gate_last prior

@[simp] theorem appendLast_castSucc
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (wire : Wire inputCount sourceGateCount) :
    prior.appendLast wire.castSucc = (prior wire).castSucc := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp [Fin.castSucc_castAdd]
  · simp [appendLast]

/-- Rename gate wires by a permutation. -/
def ofPermutation (permutation : Equiv.Perm (Fin gateCount)) :
    Wire.Renaming inputCount gateCount gateCount where
  gates := fun gate => Wire.gate (permutation gate)

theorem ofPermutation_gate
    (permutation : Equiv.Perm (Fin gateCount)) (gate : Fin gateCount) :
    (ofPermutation permutation : Wire.Renaming inputCount gateCount gateCount) (Wire.gate gate) =
      Wire.gate (permutation gate) := by
  simp [ofPermutation]

/-- A source and target gate valuation agree along a renaming when they agree
on the image of every source gate. Original inputs agree automatically. -/
theorem value_apply
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (inputs : Fin inputCount → U)
    (oldGates : Fin sourceGateCount → U)
    (newGates : Fin targetGateCount → U)
    (preservesGates : ∀ gate,
      (Fin.addCases inputs newGates : Wire inputCount targetGateCount → U) (ρ.gates gate) =
        oldGates gate)
    (wire : Wire inputCount sourceGateCount) :
    (Fin.addCases inputs newGates : Wire inputCount targetGateCount → U) (ρ wire) =
      (Fin.addCases inputs oldGates : Wire inputCount sourceGateCount → U) wire := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp
  · simpa using preservesGates gate

end Wire.Renaming

end Cslib.Circuits
