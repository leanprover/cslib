/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Basic
public import Cslib.Crypto.Protocols.PerfectSecrecy.Internal.OneTimePad
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Cslib.Foundations.Control.Monad.Free

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

variable (n : Type → Type*) [Monad n] [MonadLiftT n PMF] [LawfulMonadLiftT n PMF]
  [Probability.HasUniformBitVec n]

/-- The one-time pad over `l`-bit strings. Encryption and decryption
are XOR ([KatzLindell2020], Construction 2.9). -/
def otp (l : ℕ) : EncScheme n (BitVec l) (BitVec l) (BitVec l) :=
  let gen : n (BitVec l) := Probability.HasUniformBitVec.uniformBitVec l
  .ofPure gen (· ^^^ ·) (· ^^^ ·)

instance (l : ℕ) : (otp n l).Correct :=
  EncScheme.ofPure.Correct _ _ _ fun k m => by simp [← BitVec.xor_assoc]

/-- The one-time pad is perfectly secret ([KatzLindell2020], Theorem 2.10). -/
theorem otp_perfectlySecret (l : ℕ) : (otp n l).PerfectlySecret :=
  (EncScheme.perfectlySecret_iff_ciphertextIndist _).mpr fun m₀ m₁ => by
    simp only [EncScheme.ciphertextDist, otp, EncScheme.ofPure,
      Probability.HasUniformBitVec.liftM_uniformBitVec, liftM_pure,
      Probability.PMF.monad_pure_eq_pure]
    exact (OTP.otp_ciphertextDist_eq_uniform l m₀).trans
      (OTP.otp_ciphertextDist_eq_uniform l m₁).symm

section executable_otp

/-- Monad to model computations with access to uniform bitvector selection -/
private abbrev UniformBitVecM : Type → Type 1 :=
  FreeM (PFunctor.Obj {A := ℕ, B := BitVec})

/-- Currently this can't be made computable because we use `PMF` for probabilities.
Executing `run_otp -/
private noncomputable instance : MonadLift UniformBitVecM PMF where
  monadLift := FreeM.liftM fun | ⟨n, f⟩ => (PMF.uniformOfFintype (BitVec n)).map f

private instance : LawfulMonadLiftT UniformBitVecM PMF where
  monadLift_pure := FreeM.liftM_pure _
  monadLift_bind := FreeM.liftM_bind _

private instance : Probability.HasUniformBitVec UniformBitVecM where
  uniformBitVec n := FreeM.lift ⟨n, id⟩
  liftM_uniformBitVec n := by
    simp [liftM, monadLift, MonadLift.monadLift, bind, PMF.map_id]; rfl

private instance : MonadLift UniformBitVecM IO where
  monadLift := FreeM.liftM fun | ⟨n, f⟩ => do
    let m ← IO.rand 0 (2 ^ n)
    return f (BitVec.ofNat n m)

private def foo (n : ℕ) : UniformBitVecM (BitVec n) := do
  let x ← Probability.HasUniformBitVec.uniformBitVec n
  return x

private def run_otp (message : BitVec l) :
    UniformBitVecM (BitVec l × BitVec l × BitVec l × BitVec l) := do
  let key ← (otp UniformBitVecM l).gen
  let ciphertext ← (otp UniformBitVecM l).enc key message
  let message' := (otp UniformBitVecM l).dec key ciphertext
  return (message, key, ciphertext, message')

end executable_otp

end Cslib.Crypto.Protocols.PerfectSecrecy
