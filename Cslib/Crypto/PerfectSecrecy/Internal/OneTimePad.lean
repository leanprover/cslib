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

namespace Cslib.Crypto.PerfectSecrecy.OTP

@[reducible] noncomputable def bitVecFintype (n : ℕ) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2 ^ n))
    ⟨BitVec.ofFin, BitVec.toFin, fun x => by simp, fun x => by simp⟩

/-- XOR by a fixed mask is self-inverse on `BitVec`: `c = k ^^^ m ↔ k = c ^^^ m`. -/
lemma xor_right_eq_iff {l : ℕ} (c m k : BitVec l) :
    (c = k ^^^ m) ↔ (k = c ^^^ m) := by
  constructor
  · rintro rfl
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rintro rfl
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The ciphertext distribution of the OTP is uniform, regardless of the message. -/
theorem otp_ciphertextDist_eq_uniform (l : ℕ) (m : BitVec l) :
    haveI := bitVecFintype l
    (PMF.uniformOfFintype (BitVec l)).bind
      (fun k => PMF.pure (k ^^^ m)) =
    PMF.uniformOfFintype (BitVec l) := by
  haveI := bitVecFintype l
  ext c
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, PMF.pure_apply]
  simp_rw [xor_right_eq_iff c m]
  simp

end Cslib.Crypto.PerfectSecrecy.OTP
