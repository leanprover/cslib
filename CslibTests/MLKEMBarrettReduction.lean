import Cslib.Crypto.Algorithms.BarrettReduction.Signed

namespace CslibTests

section MLKEMExample
open Cslib.Crypto.Algorithms.BarrettReduction.Signed

/-!
Proof of correctness for the signed Barrett reduction
used in the reference implementation of Kyber/ML-KEM
https://github.com/pq-crystals/kyber/blob/main/ref/reduce.c#L25-L42
-/

def M : ℕ := 16    -- 16 bits
def q : ℕ := 3329  -- prime modulus used for MLKEM
def R : ℕ := 2 ^ 26
def k : ℕ := 2

-- This follows closely the original C code, though in ℤ
def mlkemBarrettReduce (a : ℤ) : ℤ :=
  let v := 20159
  let t := (v * a + (1 <<< 25)) >>> (26: ℕ)
  let t := t * 3329
  a - t

lemma mlkemBarrettReduce_correct (a : ℤ) (Ha : |a| ≤ 2 ^ 15) :
    mlkemBarrettReduce a = a.bmod q := by
  rw [← barrettReduce_spec a M R k q]
  · rw [mlkemBarrettReduce, barrettReduce, R, q]; simp only [Nat.cast_ofNat,
    Nat.reduceShiftLeft, Nat.reducePow, sub_right_inj]
    rw [show (round (67108864 / (3329:ℚ))) = 20159 by decide +kernel]
    rw [Int.shiftRight_eq_div_pow, round_eq]
    rw [div_add_div] <;> try decide
    simp only [Nat.reducePow, Nat.cast_ofNat, Int.cast_ofNat, mul_one]
    rw [show ↑a * 20159 * 2 + 67108864 = (20159 * a + 33554432) * (2:ℚ) by linarith]
    rw [mul_div_mul_right _ _ (by simp)]
    rw [show 20159 * ↑a + (33554432:ℚ) = ↑(20159 * a + (33554432:ℤ)) by simp]
    rw [show (67108864:ℚ) = ↑(67108864:ℕ) by simp]
    rw [Rat.floor_intCast_div_natCast]; simp; omega
  · simp [k]
  · decide +kernel
  · use (q/2); decide
  · decide
  · decide
  · transitivity
    · apply Ha
    · decide

-- This is basically the C code translated manually into Lean
def mlkemBarrettReduceImpl (a : Int16) : Int16 :=
  let v: Int16 := 20159
  let t: Int32 := (v.toInt32 * a.toInt32 + ((1: Int32) <<< 25)) >>> 26
  let t: Int16 := t.toInt16 * 3329
  a - t

lemma mlkemBarrettReduceImpl_correct (a : Int16) :
    Int16.toInt (mlkemBarrettReduceImpl a) = (Int16.toInt a).bmod q := by
  rw [← mlkemBarrettReduce_correct]
  · rw [mlkemBarrettReduce, mlkemBarrettReduceImpl]
    rw [Int16.toInt_sub, Int16.toInt_mul]
    simp only [Nat.reduceLeDiff, Int16.toInt32_ofNat, Int32.toInt_toInt16, Nat.reducePow,
      Int16.reduceToInt, Int.bmod_mul_bmod, Int.sub_bmod_bmod, Nat.cast_ofNat, Nat.reduceShiftLeft]
    rw [show ((1:Int32) <<< 25 = 33554432) by decide]
    rw [← Int32.toInt_toBitVec, Int32.toBitVec_shiftRight]
    simp only [Int32.toBitVec_add, Int32.toBitVec_mul, Int32.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
      Int16.toBitVec_toInt32, BitVec.reduceSMod, BitVec.sshiftRight_eq', BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, BitVec.toInt_sshiftRight, BitVec.toInt_add, BitVec.toInt_mul,
      BitVec.reduceToInt, Int.bmod_add_bmod]
    rw [BitVec.toInt_signExtend_of_le] <;> [skip;simp]
    rw [Int16.toInt_toBitVec]
    have Hle := Int16.le_toInt a
    have Hlt := Int16.toInt_lt a
    rw [@Int.bmod_eq_of_le _ 4294967296] <;> [skip; (simp; omega); (simp; omega)]
    rw [show (a.toInt - (20159 * a.toInt + 33554432) >>> 26 * 3329 = mlkemBarrettReduce a.toInt)
      by rw [mlkemBarrettReduce]; simp]
    rw [mlkemBarrettReduce_correct, q]
    · rw [Int.bmod_bmod_eq_of_lt] <;> omega
    · rw [abs_le]; omega
  · rw [abs_le']; split_ands
    · apply Int.le_of_lt
      apply Int16.toInt_lt
    · apply Int.neg_le_of_neg_le
      apply Int16.le_toInt

end MLKEMExample

end CslibTests
