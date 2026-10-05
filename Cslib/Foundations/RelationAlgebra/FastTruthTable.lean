/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles

/-!
# Packed Boolean truth tables

A natural number can store the values of a Boolean expression on every assignment at once.
Bitwise operations then check many cycle tables in parallel inside the kernel. `truthColumn`
constructs the truth table of one variable by repeatedly duplicating its lower half.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Code

/-- The word whose first `n` bits are all set. -/
def truthOnes (n : ℕ) : ℕ := 2 ^ n - 1

theorem bitAt_truthOnes (n mask : ℕ) : bitAt (truthOnes n) mask = decide (mask < n) := by
  simp [truthOnes, bitAt_eq_testBit]

/-- The values of variable `i` on the `2 ^ r` assignments to `r` Boolean variables. -/
def truthColumn : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r + 1, i =>
    if i = r then truthOnes (2 ^ r) <<< (2 ^ r)
    else let lower := truthColumn r i
      lower ||| lower <<< (2 ^ r)

theorem testBit_truthColumn (r i mask : ℕ) :
    (truthColumn r i).testBit mask =
      (decide (mask < 2 ^ r) && decide (i < r) && mask.testBit i) := by
  induction r generalizing mask with
  | zero => simp [truthColumn]
  | succ r ih =>
    have hp : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by omega
    by_cases hi : i = r
    · subst i
      simp only [truthColumn, truthOnes, Nat.lt_add_one, decide_true, Bool.and_true]
      by_cases hm : mask < 2 ^ r
      · rw [Nat.testBit_lt_two_pow hm]
        simp [show ¬mask ≥ 2 ^ r by omega]
      · by_cases hb : mask < 2 ^ (r + 1)
        · rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) hb]
          simp [hb, show mask ≥ 2 ^ r by omega, show mask - 2 ^ r < 2 ^ r by omega]
        · simp [hb, show ¬mask - 2 ^ r < 2 ^ r by omega]
    · simp only [truthColumn, ite_eq_right hi, Nat.testBit_or, Nat.testBit_shiftLeft, ih]
      by_cases hir : i < r
      · have his : i < r + 1 := by omega
        simp only [hir, his, decide_true, Bool.and_true]
        by_cases hm : mask < 2 ^ r
        · simp [hm, show mask < 2 ^ (r + 1) by omega, show ¬mask ≥ 2 ^ r by omega]
        · by_cases hb : mask < 2 ^ (r + 1)
          · have he : mask = 2 ^ r + (mask - 2 ^ r) := by omega
            have ht : (mask - 2 ^ r).testBit i = mask.testBit i := by
              conv_rhs => rw [he]
              exact (Nat.testBit_two_pow_add_gt hir _).symm
            simp [hm, hb, ht, show mask ≥ 2 ^ r by omega,
              show mask - 2 ^ r < 2 ^ r by omega]
          · simp [hm, hb, show ¬mask - 2 ^ r < 2 ^ r by omega]
      · have his : ¬i < r + 1 := by omega
        simp [hir, his]

/-- Read a variable's value from its packed truth table. -/
theorem bitAt_truthColumn {r i mask : ℕ} (hi : i < r) (hm : mask < 2 ^ r) :
    bitAt (truthColumn r i) mask = bitAt mask i := by
  simp [bitAt_eq_testBit, testBit_truthColumn, hi, hm]

end Cslib.RelationAlgebra.Code
