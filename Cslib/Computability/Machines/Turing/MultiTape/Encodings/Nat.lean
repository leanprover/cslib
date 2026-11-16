/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.HeadCases

/-!
# Complexity of basic operations on natural numbers

Relative to the binary encoding `Cslib.Encoding.encNat`, which has the least significant bit
first, the successor, halving and the parity are computable in linear time and zero space.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_nat_succ`: the successor.
* `Turing.MultiTapeTM.computableInTimeAndSpace_nat_div_two`: halving.
* `Turing.MultiTapeTM.computableInTimeAndSpace_nat_bodd`: the parity.
* `Turing.MultiTapeTM.computableInTimeAndSpace_nat_decide_eq_zero`: the test for zero.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Encoding

/-- The state records the carry, which propagates in reading order. -/
private def succStep : Bool → Bool → List Bool × Bool
  | true, true => ([false], true)
  | true, false => ([true], false)
  | false, b => ([b], false)

private def succFinal : Bool → List Bool
  | true => [true]
  | false => []

private lemma oneWayOutput_succ_false (w : List Bool) :
    oneWayOutput succStep succFinal false w = w := by
  induction w <;> simp [succStep, succFinal, *]

private lemma oneWayOutput_succ (w : List Bool) :
    oneWayOutput succStep succFinal true w = bitsSucc w := by
  induction w with
  | nil => simp [succFinal]
  | cons a w ih => cases a <;> simp [succStep, ih, oneWayOutput_succ_false]

/-- `bitsSucc` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_bitsSucc :
    ComputableInTimeAndSpace bitsSucc encBits encBits (fun w => 2 * w.length + 2) (fun _ => 0) :=
  (computableInTimeAndSpace_of_oneWayOutput_eq true succStep succFinal oneWayOutput_succ).mono
    (fun w => by have := length_bitsSucc_le w; lia) fun _ => le_rfl

/-- The successor is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_nat_succ :
    ComputableInTimeAndSpace (· + 1) encNat encNat (fun n => 2 * (encNat n).length + 2)
      (fun _ => 0) :=
  computableInTimeAndSpace_bitsSucc.of_realizes bitsSucc_encNat

/-- Halving is computable in linear time and zero space: it drops the least significant bit. -/
theorem computableInTimeAndSpace_nat_div_two :
    ComputableInTimeAndSpace (· / 2) encNat encNat (fun n => 2 * (encNat n).length + 1)
      (fun _ => 0) :=
  ((computableInTimeAndSpace_headCases [] (fun _ => []) fun _ => true).of_realizes fun n => by
    rw [encNat_eq_bits, encNat_eq_bits, ← Nat.div2_val, Nat.div2_bits_eq_tail]
    cases n.bits <;> simp).mono (fun _ => by simp) fun _ => le_rfl

/-- The parity is computable in linear time and zero space: it is the least significant bit. -/
theorem computableInTimeAndSpace_nat_bodd :
    ComputableInTimeAndSpace Nat.bodd encNat encBool (fun n => 2 * (encNat n).length + 2)
      (fun _ => 0) :=
  ((computableInTimeAndSpace_headCases [false] (fun b => [b]) fun _ => false).of_realizes
    fun n => by
      rw [encNat_eq_bits, Nat.bodd_eq_bits_head]
      cases n.bits <;> simp).mono (fun _ => by simp) fun _ => le_rfl

/-- The test for zero is computable in constant time and zero space, since it is constant except
on zero. -/
theorem computableInTimeAndSpace_nat_decide_eq_zero :
    ComputableInTimeAndSpace (fun n : ℕ => decide (n = 0)) encNat encBool
      (fun _ => 4) (fun _ => 0) :=
  (computableInTimeAndSpace_almostConstTime _ {0} [false] fun n hn => by simp_all).mono
    (fun _ => by simp [almostConstTime]) fun _ => le_rfl

end Turing.MultiTapeTM
