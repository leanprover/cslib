/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Basic
public import Cslib.Foundations.Data.BitVec
public import Mathlib.Data.FinEnum
import Mathlib.Data.LawfulXor.Equiv

/-!
# One-Time Pad

The one-time pad (Vernam cipher) over `BitVec l`
([KatzLindell2020], Construction 2.9).

## Main definitions

- `Cslib.Crypto.Protocols.PerfectSecrecy.otp`: the one-time pad encryption scheme

## Main results

- `Cslib.Crypto.Protocols.PerfectSecrecy.otp_perfectlySecret`:
  the one-time pad is perfectly secret ([KatzLindell2020], Theorem 2.10)

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.PerfectSecrecy

open MeasureTheory ProbabilityTheory Cslib.Probability.Measure

/-- The one-time pad over `l`-bit strings. Encryption and decryption
are XOR ([KatzLindell2020], Construction 2.9). -/
noncomputable def otp (l : ℕ) :
    EncScheme (BitVec l) (BitVec l) (BitVec l) :=
  .ofPure (uniformOfFintype (BitVec l)) (· ^^^ ·) (· ^^^ ·)
    (measurable_of_countable _) (measurable_of_countable _) fun k m => by
      simp [xor_cancel_left]

/-- The ciphertext distribution of the OTP is uniform, regardless of the
message: masking with a uniform key is the permutation `Equiv.xor` of the
uniform distribution. -/
theorem otp_ciphertextDist_eq_uniform (l : ℕ) (m : BitVec l) :
    (otp l).ciphertextDist m = uniformOfFintype (BitVec l) := by
  rw [EncScheme.ciphertextDist_eq_comp]
  change (uniformOfFintype (BitVec l) : Measure (BitVec l)).bind
    (fun key => Measure.dirac (key ^^^ m)) = _
  rw [Measure.bind_dirac_eq_map _ (measurable_of_countable _), xor_right_eq]
  exact uniformOn_univ_map_equiv (Equiv.xor m)

/-- The one-time pad is perfectly secret ([KatzLindell2020], Theorem 2.10). -/
theorem otp_perfectlySecret (l : ℕ) : (otp l).PerfectlySecret :=
  (EncScheme.perfectlySecret_iff_ciphertextIndist _).mpr fun m₀ m₁ =>
    (otp_ciphertextDist_eq_uniform l m₀).trans (otp_ciphertextDist_eq_uniform l m₁).symm

end Cslib.Crypto.Protocols.PerfectSecrecy
