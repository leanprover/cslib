/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Bounded words with a binary length prefix

A word of length at most `n` is stored in a frame: `Nat.size n` header bits for its length,
followed by `n` data bits. The header is little endian; unused data bits are ignored. A header
larger than the capacity decodes to the entire data area. Encoding truncates words at the
capacity and fills the unused data area with zeroes.

This is a bounded-length specialization of the length-prefixing construction in
[Boaz Barak, *Introduction to Theoretical Computer Science*, Exercise 2.10][Barak2023].
The capacity fixes the header width, so no delimiter for the header is needed. Zero-filling
and the behavior on oversized headers are the conventions chosen here for a total codec.

## References

* [Boaz Barak, *Introduction to Theoretical Computer Science*, Exercise 2.10][Barak2023]
-/

@[expose] public section

namespace Cslib.BitString.Encoding

/-- Number of wires for a word of capacity `n`, including its binary length header. -/
def width (n : ℕ) : ℕ := n.size + n

/-- A fixed-width frame holding a word of length at most `n`. -/
abbrev Frame (n : ℕ) := Fin (width n) → Bool

/-- The length header, interpreted as a little-endian binary natural number. -/
def header {n : ℕ} (x : Frame n) : ℕ :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin n.size => x (i.castAdd n))).toNat

/-- The payload, without consulting the length header. -/
def data {n : ℕ} (x : Frame n) : Fin n → Bool := fun i => x (i.natAdd n.size)

/-- Read the prefix of the payload specified by the length header. -/
def decode {n : ℕ} (x : Frame n) : BitString := (List.ofFn (data x)).take (header x)

/-- Encode a word, truncating at capacity and zero-filling its unused payload. -/
def encode (n : ℕ) (xs : BitString) : Frame n :=
  Fin.append (fun i : Fin n.size => (min xs.length n).testBit i)
    (fun i : Fin n => xs[i.val]?.getD false)

/-- Decoding never exceeds the payload capacity. -/
theorem length_decode_le {n : ℕ} (x : Frame n) : (decode x).length ≤ n := by
  simpa only [decode, List.length_take, List.length_ofFn] using Nat.min_le_right (header x) n

/-- The encoded header stores the length after truncation. -/
@[simp] theorem header_encode (n : ℕ) (xs : BitString) :
    header (encode n xs) = min xs.length n := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (BitVec.ofBoolListLE (List.ofFn fun j : Fin n.size =>
    encode n xs (j.castAdd n))).getLsbD i = _
  by_cases hi : i < n.size
  · rw [BitVec.getLsbD_ofBoolListLE]
    simp [encode, List.getD_eq_getElem?_getD, hi]
  · have hlt : min xs.length n < 2 ^ i :=
      (min_le_right _ _).trans_lt ((Nat.lt_size_self n).trans_le
        (Nat.pow_le_pow_right (by decide) (by lia)))
    simp [List.getD_eq_getElem?_getD,
      hi, Nat.testBit_lt_two_pow hlt]

/-- Decoding an encoding returns the original word truncated at capacity. -/
@[simp] theorem decode_encode (n : ℕ) (xs : BitString) :
    decode (encode n xs) = xs.take n := by
  apply List.ext_getElem
  · simp [decode, Nat.min_comm]
  · intro i hi hj
    have hil : i < xs.length := by simp only [List.length_take] at hj; lia
    simp only [decode, List.getElem_take, List.getElem_ofFn, data, encode,
      Fin.append_right, List.getElem?_eq_getElem hil, Option.getD_some]

/-- The encoding preserves every word that fits in its capacity. -/
theorem decode_encode_of_length_le {n : ℕ} {xs : BitString} (h : xs.length ≤ n) :
    decode (encode n xs) = xs := by simp [List.take_of_length_le h]

/-- The header contributes at most the capacity to the representation size. -/
theorem width_le (n : ℕ) : width n ≤ 2 * n := by
  have : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  dsimp [width]
  lia

end Cslib.BitString.Encoding
