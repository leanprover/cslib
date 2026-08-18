/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Basic
public import Mathlib.Data.FinEnum
import Cslib.Probability.PMF
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

open Cslib.Probability.PMF

/-- The one-time pad over `l`-bit strings. Encryption and decryption
are XOR ([KatzLindell2020], Construction 2.9). -/
noncomputable def otp (l : ℕ) :
    EncScheme (BitVec l) (BitVec l) (BitVec l) :=
  .ofPure (PMF.uniformOfFintype _) (· ^^^ ·) (· ^^^ ·) fun k m => by
    simp [xor_cancel_left]

/-- The ciphertext distribution of the OTP is uniform, regardless of the
message: masking with a uniform key is the permutation `Equiv.xor` of the
uniform distribution. -/
theorem otp_ciphertextDist_eq_uniform (l : ℕ) (m : BitVec l) :
    (otp l).ciphertextDist m = PMF.uniformOfFintype (BitVec l) := by
  have h : (fun k : BitVec l => PMF.pure (k ^^^ m)) = (PMF.pure ∘ ⇑(Equiv.xor m)) :=
    congrArg (PMF.pure ∘ ·) xor_right_eq
  change (PMF.uniformOfFintype (BitVec l)).bind (fun k => PMF.pure (k ^^^ m)) = _
  rw [h, PMF.bind_pure_comp, uniformOfFintype_map_equiv]

/-- The one-time pad is perfectly secret ([KatzLindell2020], Theorem 2.10). -/
theorem otp_perfectlySecret (l : ℕ) : (otp l).PerfectlySecret :=
  (EncScheme.perfectlySecret_iff_ciphertextIndist _).mpr fun m₀ m₁ =>
    (otp_ciphertextDist_eq_uniform l m₀).trans (otp_ciphertextDist_eq_uniform l m₁).symm

end Cslib.Crypto.Protocols.PerfectSecrecy
