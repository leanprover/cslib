/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.SearchCertificate
public import Cslib.Foundations.RelationAlgebra.FastTruthTable

/-!
# Byte lookup for counting free cycle variables

The specification counts bits individually. The executable counter uses a packed table of
the 256 byte populations and processes eight bits at a time. The table and the implementation
are proved correct in the kernel.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Counting

namespace BitCount

/-- Number of set bits below a specified width. -/
def below (mask : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if Code.bitAt mask i then below mask i + 1 else below mask i

/-- Equal bounded bit sequences have equal populations. -/
theorem below_congr (left right width : ℕ)
    (h : ∀ i < width, Code.bitAt left i = Code.bitAt right i) :
    below left width = below right width := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [below, h width (Nat.lt_succ_self width)]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

/-- Truncation preserves the bits inside its width. -/
theorem below_mod (mask width : ℕ) : below (mask % 2 ^ width) width = below mask width := by
  apply below_congr
  intro i hi
  simp only [Code.bitAt_eq_testBit, Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]

/-- Populations add when a word is split into consecutive blocks. -/
theorem below_add (mask low high : ℕ) :
    below mask (low + high) = below mask low + below (mask >>> low) high := by
  induction high with
  | zero => simp [below]
  | succ high ih =>
    have hb : Code.bitAt (mask >>> low) high = Code.bitAt mask (low + high) := by
      simp only [Code.bitAt_eq_testBit, Nat.testBit_shiftRight]
    change (if Code.bitAt mask (low + high) then below mask (low + high) + 1
      else below mask (low + high)) = below mask low +
        (if Code.bitAt (mask >>> low) high then below (mask >>> low) high + 1
          else below (mask >>> low) high)
    rw [hb, ih]
    split <;> omega

/-- Appending zero bits does not change a population. -/
theorem below_extend (mask low high : ℕ) (hle : low ≤ high)
    (hz : ∀ i, low ≤ i → i < high → Code.bitAt mask i = false) :
    below mask high = below mask low := by
  induction high with
  | zero =>
    have : low = 0 := by omega
    subst low
    rfl
  | succ high ih =>
    by_cases he : low = high + 1
    · rw [he]
    · have hl : low ≤ high := by omega
      simp only [below, hz high hl (Nat.lt_succ_self high), Bool.false_eq_true, ↓reduceIte]
      exact ih hl (fun i hi hib => hz i hi (Nat.lt_succ_of_lt hib))

/-- Packed four-bit populations for all bytes, indexed from the least significant field. -/
def byteTable : ℕ :=
  0x6554544354434332544343324332322154434332433232214332322132212110 +
    (0x7665655465545443655454435443433265545443544343325443433243323221 <<< 256) +
    (0x7665655465545443655454435443433265545443544343325443433243323221 <<< 512) +
    (0x8776766576656554766565546554544376656554655454436554544354434332 <<< 768)

/-- Read the population of a word's least significant byte. -/
def byte (mask : ℕ) : ℕ := Code.field byteTable (4 * (mask % 256)) 4

private theorem byte_table_correct : ∀ mask : Fin 256, byte mask = below mask 8 := by
  decide +kernel

/-- The packed table computes the population of the lowest eight bits. -/
theorem byte_eq (mask : ℕ) : byte mask = below mask 8 := by
  have h := byte_table_correct ⟨mask % 256, Nat.mod_lt _ (by decide)⟩
  have hm : below (mask % 256) 8 = below mask 8 := below_mod mask 8
  simpa only [Fin.val_mk, byte, Nat.mod_mod, hm] using h

/-- Count a specified number of bytes with primitive numeric table lookups. -/
def bytes : ℕ → ℕ → ℕ
  | 0, _ => 0
  | count + 1, mask => byte mask + bytes count (mask >>> 8)

/-- Byte lookup agrees with the individual-bit specification. -/
theorem bytes_eq (count mask : ℕ) : bytes count mask = below mask (8 * count) := by
  induction count generalizing mask with
  | zero => rfl
  | succ count ih =>
    rw [bytes, byte_eq, ih, Nat.mul_succ, Nat.add_comm (8 * count) 8, below_add]

end BitCount

namespace Cube

/-- The bounded mask of still unassigned indices. -/
def freeMask (cube : Cube) (r : ℕ) : ℕ :=
  let full := 2 ^ r - 1
  full ^^^ ((cube.on ||| cube.off) &&& full)

/-- The bounded free mask has precisely the unassigned bits. -/
theorem bitAt_freeMask (cube : Cube) (r i : ℕ) :
    Code.bitAt (cube.freeMask r) i = if i < r then cube.isFree i else false := by
  simp only [freeMask, Code.bitAt_eq_testBit, Nat.testBit_xor, Nat.testBit_and,
    Nat.testBit_or, isFree, Code.bitAt_eq_testBit]
  have h := Code.bitAt_truthOnes r i
  simp only [Code.truthOnes, Code.bitAt_eq_testBit] at h
  rw [h]
  by_cases hi : i < r <;> simp [hi, Bool.not_or]

/-- The population of the free mask is the original free-variable count. -/
theorem below_freeMask (cube : Cube) (r : ℕ) :
    BitCount.below (cube.freeMask r) r = cube.freeVariables r := by
  have h : ∀ n ≤ r, BitCount.below (cube.freeMask r) n = cube.freeVariables n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      change (if Code.bitAt (cube.freeMask r) n then
        BitCount.below (cube.freeMask r) n + 1 else BitCount.below (cube.freeMask r) n) =
        (if cube.isFree n then cube.freeVariables n + 1 else cube.freeVariables n)
      rw [bitAt_freeMask, ite_eq_left (show n < r by omega)]
      rw [ih (by omega)]
  exact h r le_rfl

/-- Count free variables eight bits at a time. -/
def fastFreeVariables (cube : Cube) (r : ℕ) : ℕ :=
  BitCount.bytes ((r + 7) / 8) (cube.freeMask r)

/-- The byte counter has the same meaning as the original free-variable counter. -/
theorem fastFreeVariables_eq (cube : Cube) (r : ℕ) :
    cube.fastFreeVariables r = cube.freeVariables r := by
  rw [fastFreeVariables, BitCount.bytes_eq]
  rw [BitCount.below_extend (cube.freeMask r) r _ (by omega)]
  · exact below_freeMask cube r
  · intro i hi _
    simp [bitAt_freeMask, show ¬i < r by omega]

/-- The exact count of completions, using the proved byte counter. -/
def fastFreeCount (r : ℕ) (cube : Cube) : ℕ := 2 ^ cube.fastFreeVariables r

/-- Fast completion counting preserves the original specification. -/
theorem fastFreeCount_eq (r : ℕ) (cube : Cube) : cube.fastFreeCount r = cube.freeCount r := by
  rw [fastFreeCount, freeCount, fastFreeVariables_eq]

end Cube

end Cslib.RelationAlgebra.Counting
