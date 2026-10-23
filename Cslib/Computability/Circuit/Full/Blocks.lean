/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Full.Dictionary

/-!
# Blocked table lookup

An address selects one of `B` blocks and one of `t` cells within that block.
`blockIndicator` marks the selected cell. For a nonzero marker, a prescription
on one block returns the addressed table entry when that block is selected,
and zero otherwise. Summing the prescriptions over all blocks therefore returns
the addressed entry.

These identities justify reading Lupanov's shared block dictionaries by selecting
one prescription per block and summing the results. The address may be any
function of the original inputs.
-/

@[expose] public section

namespace Cslib.Circuits.Full

variable {U : Type*} {n B t : ℕ}

/-- Return `marker` when the address selects cell `(b, i)`, and zero otherwise. -/
def blockIndicator [Zero U] (marker : U)
    (address : (Fin n → U) → Fin B × Fin t) (b : Fin B) (i : Fin t) : (Fin n → U) → U :=
  fun x => if address x = (b, i) then marker else 0

variable [DecidableEq U]

/-- A block prescription returns the addressed table entry on its block, and zero elsewhere. -/
theorem prescription_blockIndicator [Zero U] (marker : U) (hm : marker ≠ 0)
    (address : (Fin n → U) → Fin B × Fin t) (b : Fin B)
    (v : Fin B × Fin t → U) (x : Fin n → U) :
    prescription 0 marker (blockIndicator marker address b) (fun i => v (b, i)) x =
      if (address x).1 = b then v (address x) else 0 := by
  split_ifs with hb
  · simpa [← hb] using
      prescription_eq 0 marker (blockIndicator marker address b) (fun i => v (b, i))
        x (address x).2 (by simp [blockIndicator, ← hb]) (by
          intro j hj
          simp [blockIndicator, Prod.ext_iff, hj.symm, hm.symm])
  · apply prescription_eq_default
    intro i
    simp [blockIndicator, Prod.ext_iff, hb, hm.symm]

/-- Summing one prescription from each block returns the addressed table entry. -/
theorem sum_prescription_blockIndicator [AddCommMonoid U] (marker : U) (hm : marker ≠ 0)
    (address : (Fin n → U) → Fin B × Fin t) (v : Fin B × Fin t → U) (x : Fin n → U) :
    (∑ b, prescription 0 marker (blockIndicator marker address b) (fun i => v (b, i)) x) =
      v (address x) := by
  simp [prescription_blockIndicator marker hm, eq_comm]

end Cslib.Circuits.Full
