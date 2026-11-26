/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.HeadCases
import Mathlib.Data.Nat.Size

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

open Cslib.Encoding Cslib.Automata

/-! ### The successor on codes -/

/-- The successor on binary words, least significant bit first. -/
@[expose]
def bitsSucc : List Bool → List Bool
  | [] => [true]
  | false :: w => true :: w
  | true :: w => false :: bitsSucc w

@[simp] theorem bitsSucc_nil : bitsSucc [] = [true] := rfl

@[simp] theorem bitsSucc_false_cons (w : List Bool) : bitsSucc (false :: w) = true :: w := rfl

@[simp] theorem bitsSucc_true_cons (w : List Bool) :
    bitsSucc (true :: w) = false :: bitsSucc w := rfl

theorem length_bitsSucc_le (w : List Bool) : (bitsSucc w).length ≤ w.length + 1 := by
  fun_induction bitsSucc w <;> grind

/-- Not a `simp` lemma: `encNat n` is the more useful normal form. -/
theorem encNat_eq_bits (n : ℕ) : encNat n = n.bits := rfl

/-- Not a `simp` lemma: `encNat n` is the more useful normal form. -/
theorem length_encNat (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_eq_bits, Nat.size_eq_bits_len]

theorem encNat_two_mul {n : ℕ} (hn : n ≠ 0) : encNat (2 * n) = false :: encNat n := by
  rw [encNat_eq_bits, Nat.bit0_bits n hn, encNat_eq_bits]

theorem encNat_two_mul_add_one (n : ℕ) : encNat (2 * n + 1) = true :: encNat n := by
  rw [encNat_eq_bits, Nat.bit1_bits, encNat_eq_bits]

/-- `bitsSucc` is the successor on codes of natural numbers. -/
theorem bitsSucc_encNat (n : ℕ) : bitsSucc (encNat n) = encNat (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [encNat_eq_bits]
      · rw [encNat_two_mul (by lia), encNat_two_mul_add_one, bitsSucc_false_cons]
    · rw [encNat_two_mul_add_one, show 2 * k + 1 + 1 = 2 * (k + 1) by lia,
        encNat_two_mul (by lia), bitsSucc_true_cons, ih k (by lia)]

/-! ### Machines -/

/-- The state records the carry, which propagates in reading order. -/
private def succStep : Bool → Bool → List Bool × Bool
  | true, true => ([false], true)
  | true, false => ([true], false)
  | false, b => ([b], false)

private def succFinal : Bool → List Bool
  | true => [true]
  | false => []

/-- The successor on codes as a subsequential transducer with the carry as its state. -/
private def succTransducer : SubsequentialTransducer Bool Bool Bool where
  start := true
  tr q a := (succStep q a).2
  emit q a := (succStep q a).1
  finalOut := succFinal

private lemma evalFrom_succTransducer :
    succTransducer.evalFrom = fun q w => if q then bitsSucc w else w := by
  apply SubsequentialTransducer.evalFrom_unique
  · intro q; cases q <;> simp [succTransducer, succFinal, bitsSucc]
  · intro q a w
    cases q <;> cases a <;> simp [succTransducer, succStep, bitsSucc]

private lemma eval_succTransducer (w : List Bool) :
    succTransducer.eval w = bitsSucc w := by
  show succTransducer.evalFrom true w = bitsSucc w
  rw [evalFrom_succTransducer]; simp

/-- `bitsSucc` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_bitsSucc :
    ComputableInTimeAndSpace bitsSucc encBits encBits (fun w => 2 * w.length + 2) (fun _ => 0) :=
  (computableInTimeAndSpace_of_subsequential succTransducer bitsSucc eval_succTransducer).mono
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
