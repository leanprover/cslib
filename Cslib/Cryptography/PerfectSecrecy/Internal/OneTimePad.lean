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

namespace Cslib.Cryptography.PerfectSecrecy.OTP

/-- The ciphertext distribution of the OTP is uniform, regardless of the message. -/
theorem otp_ciphertextDist_eq_uniform (l : ℕ) (m : Fin l → Bool) :
    (PMF.uniformOfFintype (Fin l → Bool)).bind
      (fun k => PMF.pure (fun i => k i ^^ m i)) =
    PMF.uniformOfFintype (Fin l → Bool) := by
  ext c
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, PMF.pure_apply]
  have heq : ∀ a : Fin l → Bool,
      (c = fun i => a i ^^ m i) ↔ (a = fun i => c i ^^ m i) :=
    fun a => ⟨fun h => funext fun i => by have := congr_fun h i; simp_all,
              fun h => funext fun i => by have := congr_fun h i; simp_all⟩
  simp_rw [heq]
  simp

end Cslib.Cryptography.PerfectSecrecy.OTP
