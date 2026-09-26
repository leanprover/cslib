/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Init
public import Mathlib.Data.Fintype.Sum

/-!
# Circuit wires and renamings

A `Wire inputCount gateCount` refers to an original input or an internal gate.
A valuation of wires is assembled with `Wire.elim` from values for the inputs and
values for the gates.

`Wire.Renaming` fixes the original inputs and maps each gate to an input or gate
in the target namespace. This file provides identity and composition, extension
by a gate, replacement of the last gate, and renaming by a permutation.
-/

@[expose] public section

namespace Cslib.Circuits

/-- A wire is either an original input or the output of an earlier gate. -/
inductive Wire (inputCount gateCount : Nat) where
  /-- An original input. -/
  | input (input : Fin inputCount)
  /-- The output of an internal gate. -/
  | gate (gate : Fin gateCount)
  deriving DecidableEq

namespace Wire

variable {inputCount gateCount : Nat} {α : Sort*}

/-- Define a function on wires from its values on inputs and on gates. -/
def elim (inputs : Fin inputCount → α) (gates : Fin gateCount → α) :
    Wire inputCount gateCount → α
  | input i => inputs i
  | gate j => gates j

@[simp] theorem elim_input (inputs : Fin inputCount → α) (gates : Fin gateCount → α)
    (i : Fin inputCount) : elim inputs gates (input i) = inputs i := rfl

@[simp] theorem elim_gate (inputs : Fin inputCount → α) (gates : Fin gateCount → α)
    (j : Fin gateCount) : elim inputs gates (gate j) = gates j := rfl

/-- A wire is an input or a gate. -/
def equiv (inputCount gateCount : Nat) :
    Wire inputCount gateCount ≃ Fin inputCount ⊕ Fin gateCount where
  toFun := elim Sum.inl Sum.inr
  invFun := Sum.elim input gate
  left_inv wire := by cases wire <;> rfl
  right_inv wire := by cases wire <;> rfl

instance : Fintype (Wire inputCount gateCount) :=
  Fintype.ofEquiv _ (equiv inputCount gateCount).symm

@[simp] theorem card : Fintype.card (Wire inputCount gateCount) = inputCount + gateCount := by
  simp [Fintype.card_congr (equiv inputCount gateCount)]

/-- Regard a wire as a wire in a namespace with one additional gate. -/
def castSucc : Wire inputCount gateCount → Wire inputCount (gateCount + 1)
  | input i => input i
  | gate j => gate j.castSucc

@[simp] theorem castSucc_input (i : Fin inputCount) :
    (input i : Wire inputCount gateCount).castSucc = input i := rfl

@[simp] theorem castSucc_gate (j : Fin gateCount) :
    (gate j : Wire inputCount gateCount).castSucc = gate j.castSucc := rfl

/-- Regard a wire as a wire of the same program continued by `extra` further gates. -/
def castAdd (extra : Nat) : Wire inputCount gateCount → Wire inputCount (gateCount + extra)
  | input i => input i
  | gate j => gate (j.castAdd extra)

@[simp] theorem castAdd_input (extra : Nat) (i : Fin inputCount) :
    (input i : Wire inputCount gateCount).castAdd extra = input i := rfl

@[simp] theorem castAdd_gate (extra : Nat) (j : Fin gateCount) :
    (gate j : Wire inputCount gateCount).castAdd extra = gate (j.castAdd extra) := rfl

/-- A wire in a namespace with one additional gate is either the new last gate or an
earlier wire. -/
@[elab_as_elim]
def lastCases {motive : Wire inputCount (gateCount + 1) → Sort*}
    (last : motive (gate (Fin.last gateCount)))
    (castSucc : ∀ wire : Wire inputCount gateCount, motive wire.castSucc) :
    ∀ wire, motive wire
  | input i => castSucc (input i)
  | gate j =>
      Fin.lastCases (motive := fun j => motive (gate j)) last (fun j => castSucc (gate j)) j

end Wire

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
  Wire.elim Wire.input ρ.gates

instance : CoeFun (Wire.Renaming inputCount sourceGateCount targetGateCount)
    fun _ => Wire inputCount sourceGateCount → Wire inputCount targetGateCount :=
  ⟨apply⟩

@[simp] theorem apply_input
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount) (input : Fin inputCount) :
    ρ (Wire.input input) = Wire.input input := rfl

@[simp] theorem apply_gate
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount) (gate : Fin sourceGateCount) :
    ρ (Wire.gate gate) = ρ.gates gate := rfl

/-- The identity wire renaming. -/
def id : Wire.Renaming inputCount gateCount gateCount where
  gates := Wire.gate

@[simp] theorem id_apply (wire : Wire inputCount gateCount) :
    (id : Wire.Renaming inputCount gateCount gateCount) wire = wire := by
  cases wire <;> rfl

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
  cases wire <;> rfl

/-- Include all wires into a namespace with one additional gate. -/
def castSucc : Wire.Renaming inputCount gateCount (gateCount + 1) where
  gates := fun gate => Wire.gate gate.castSucc

@[simp] theorem castSucc_apply (wire : Wire inputCount gateCount) :
    (castSucc : Wire.Renaming inputCount gateCount (gateCount + 1)) wire = wire.castSucc := by
  cases wire <;> rfl

/-- Extend a renaming while replacing the new last gate by an existing wire. -/
def skipLast
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (replacement : Wire inputCount targetGateCount) :
    Wire.Renaming inputCount (sourceGateCount + 1) targetGateCount where
  gates := Fin.lastCases replacement prior.gates

@[simp] theorem skipLast_gates_last
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (replacement : Wire inputCount targetGateCount) :
    (prior.skipLast replacement).gates (Fin.last sourceGateCount) = replacement := by
  simp [skipLast]

@[simp] theorem skipLast_castSucc
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (replacement : Wire inputCount targetGateCount)
    (wire : Wire inputCount sourceGateCount) :
    prior.skipLast replacement wire.castSucc = prior wire := by
  cases wire <;> simp [skipLast]

/-- Extend a renaming and retain the new last gate as a fresh target gate. -/
def appendLast
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount) :
    Wire.Renaming inputCount (sourceGateCount + 1) (targetGateCount + 1) where
  gates := Fin.lastCases (Wire.gate (Fin.last targetGateCount)) fun gate =>
    (prior.gates gate).castSucc

@[simp] theorem appendLast_gates_last
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount) :
    prior.appendLast.gates (Fin.last sourceGateCount) = Wire.gate (Fin.last targetGateCount) := by
  simp [appendLast]

@[simp] theorem appendLast_castSucc
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (wire : Wire inputCount sourceGateCount) :
    prior.appendLast wire.castSucc = (prior wire).castSucc := by
  cases wire <;> simp [appendLast]

/-- Rename gate wires by a permutation. -/
def ofPermutation (permutation : Equiv.Perm (Fin gateCount)) :
    Wire.Renaming inputCount gateCount gateCount where
  gates := fun gate => Wire.gate (permutation gate)

theorem ofPermutation_gate
    (permutation : Equiv.Perm (Fin gateCount)) (gate : Fin gateCount) :
    (ofPermutation permutation : Wire.Renaming inputCount gateCount gateCount) (Wire.gate gate) =
      Wire.gate (permutation gate) := rfl

/-- A source and target gate valuation agree along a renaming when they agree
on the image of every source gate. Original inputs agree automatically. -/
theorem value_apply
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (inputs : Fin inputCount → U)
    (oldGates : Fin sourceGateCount → U)
    (newGates : Fin targetGateCount → U)
    (preservesGates : ∀ gate, Wire.elim inputs newGates (ρ.gates gate) = oldGates gate)
    (wire : Wire inputCount sourceGateCount) :
    Wire.elim inputs newGates (ρ wire) = Wire.elim inputs oldGates wire := by
  cases wire with
  | input => rfl
  | gate gate => exact preservesGates gate

end Wire.Renaming

end Cslib.Circuits
