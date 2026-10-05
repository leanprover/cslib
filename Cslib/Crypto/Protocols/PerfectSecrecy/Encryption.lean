/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.Measure

/-!
# Private-Key Encryption Schemes (Information-Theoretic)

An information-theoretic private-key encryption scheme following
[KatzLindell2020], Definition 2.1. Key generation and encryption are
probability distributions over arbitrary types, with no computational
constraints.

## Main definitions

- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme`:
  a private-key encryption scheme (Gen, Enc, Dec) with correctness

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Cslib.Crypto.Protocols.PerfectSecrecy

/--
A private-key encryption scheme over message space `M`, key space `K`,
and ciphertext space `C` ([KatzLindell2020], Definition 2.1).
-/
structure EncScheme (Message Key Ciphertext : Type*)
    [MeasurableSpace Message] [MeasurableSpace Key] [MeasurableSpace Ciphertext] where
  /-- Probabilistic key generation. -/
  gen : Measure Key
  /-- Key generation has total mass one. -/
  gen_isProbabilityMeasure : IsProbabilityMeasure gen
  /-- Jointly measurable, possibly randomized encryption. -/
  enc : Kernel (Key × Message) Ciphertext
  /-- Encryption has total mass one for every key and message. -/
  enc_isMarkovKernel : IsMarkovKernel enc
  /-- Deterministic decryption. -/
  dec (key : Key) (ciphertext : Ciphertext) : Message
  /-- Decryption is jointly measurable. -/
  dec_measurable : Measurable (Function.uncurry dec)
  /-- Almost every generated key decrypts correctly for every message, almost surely over
  encryption randomness. The exceptional set of keys is independent of the message. -/
  correct : ∀ᵐ key ∂gen, ∀ message, ∀ᵐ ciphertext ∂enc (key, message),
    dec key ciphertext = message

attribute [instance] EncScheme.gen_isProbabilityMeasure EncScheme.enc_isMarkovKernel

/-- Build an encryption scheme from measurable deterministic encryption/decryption
where decryption is a left inverse of encryption for every key. -/
noncomputable def EncScheme.ofPure {Message Key Ciphertext : Type*}
    [MeasurableSpace Message] [MeasurableSpace Key] [MeasurableSpace Ciphertext]
    [MeasurableSingletonClass Message] (gen : Measure Key) [IsProbabilityMeasure gen]
    (enc : Key → Message → Ciphertext) (dec : Key → Ciphertext → Message)
    (henc : Measurable (Function.uncurry enc)) (hdec : Measurable (Function.uncurry dec))
    (h : ∀ key, Function.LeftInverse (dec key) (enc key)) :
    EncScheme Message Key Ciphertext where
  gen := gen
  gen_isProbabilityMeasure := inferInstance
  enc := Kernel.deterministic (Function.uncurry enc) henc
  enc_isMarkovKernel := inferInstance
  dec := dec
  dec_measurable := hdec
  correct := Filter.Eventually.of_forall fun key message => by
    exact (ae_dirac_iff ((hdec.comp measurable_prodMk_left)
      (measurableSet_singleton message))).2 (h key message)

end Cslib.Crypto.Protocols.PerfectSecrecy
