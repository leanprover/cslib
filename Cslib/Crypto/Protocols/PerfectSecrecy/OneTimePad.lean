/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Basic
public import Cslib.Crypto.Protocols.PerfectSecrecy.Internal.OneTimePad
public import Mathlib.Probability.Distributions.Uniform

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

/-- The one-time pad over `l`-bit strings. Encryption and decryption
are XOR ([KatzLindell2020], Construction 2.9). -/
noncomputable def otp (l : ℕ) :
    EncScheme (BitVec l) (BitVec l) (BitVec l) :=
  .ofPure (PMF.uniformOfFintype _) (· ^^^ ·) (· ^^^ ·) fun k m => by
    simp [← BitVec.xor_assoc]

/-- The one-time pad is perfectly secret ([KatzLindell2020], Theorem 2.10). -/
theorem otp_perfectlySecret (l : ℕ) : (otp l).PerfectlySecret :=
  (EncScheme.perfectlySecret_iff_ciphertextIndist _).mpr fun m₀ m₁ => by
    simp only [EncScheme.ciphertextDist, otp]
    exact (OTP.otp_ciphertextDist_eq_uniform l m₀).trans
      (OTP.otp_ciphertextDist_eq_uniform l m₁).symm

end Cslib.Crypto.Protocols.PerfectSecrecy
