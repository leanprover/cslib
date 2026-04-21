/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
# One-Time Pad: Internal proofs

The OTP ciphertext distribution is uniform regardless of message.
-/

namespace Cslib.Crypto.Protocols.PerfectSecrecy.OTP

-- TODO: upstream to Mathlib as a FinEnum instance for BitVec.
instance bitVecFintype (n : ℕ) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2 ^ n))
    ⟨BitVec.ofFin, BitVec.toFin, fun x => by simp, fun x => by simp⟩

-- TODO: upstream to Mathlib — general BitVec XOR cancellation lemma.
/-- XOR by a fixed mask is self-inverse on `BitVec`: `c = k ^^^ m ↔ c ^^^ m = k`. -/
lemma eq_xor_iff_xor_eq {l : ℕ} (c m k : BitVec l) :
    (c = k ^^^ m) ↔ (c ^^^ m = k) := by grind

/-- The ciphertext distribution of the OTP is uniform, regardless of the message. -/
theorem otp_ciphertextDist_eq_uniform (l : ℕ) (m : BitVec l) :
    (PMF.uniformOfFintype (BitVec l)).bind
      (fun k => PMF.pure (k ^^^ m)) =
    PMF.uniformOfFintype (BitVec l) := by simp [PMF.ext_iff, eq_xor_iff_xor_eq]

end Cslib.Crypto.Protocols.PerfectSecrecy.OTP
