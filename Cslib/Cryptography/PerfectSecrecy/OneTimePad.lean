/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.PerfectSecrecy.PerfectSecrecy
public import Cslib.Cryptography.PerfectSecrecy.Internal.OneTimePad
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
# One-Time Pad

The one-time pad (Vernam cipher) over `{0,1}^l`
([KatzLindell2021], Construction 2.9).

## Main definitions

- `Cslib.Cryptography.PerfectSecrecy.otp`: the one-time pad encryption scheme

## Main results

- `Cslib.Cryptography.PerfectSecrecy.otp_perfectlySecret`:
  the one-time pad is perfectly secret ([KatzLindell2021], Theorem 2.10)

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2021]
-/

namespace Cslib.Cryptography.PerfectSecrecy

/-- The one-time pad over `l`-bit strings. Encryption and decryption
are pointwise XOR ([KatzLindell2021], Construction 2.9). -/
noncomputable def otp (l : ℕ) : EncScheme (Fin l → Bool) (Fin l → Bool) (Fin l → Bool) where
  gen := PMF.uniformOfFintype _
  enc := fun k m => PMF.pure (fun i => k i ^^ m i)
  dec := fun k c => fun i => k i ^^ c i
  correct := by intro k _ m c hc; simp at hc; simp [hc]

/-- The one-time pad is perfectly secret ([KatzLindell2021], Theorem 2.10). -/
theorem otp_perfectlySecret (l : ℕ) : (otp l).PerfectlySecret := by
  rw [EncScheme.perfectlySecret_iff_ciphertextIndist]
  intro m₀ m₁
  simp only [EncScheme.ciphertextDist, otp]
  exact (OTP.otp_ciphertextDist_eq_uniform l m₀).trans
    (OTP.otp_ciphertextDist_eq_uniform l m₁).symm

end Cslib.Cryptography.PerfectSecrecy
