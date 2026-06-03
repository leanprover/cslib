/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.ProbabilityMassFunction.Monad

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

namespace Cslib.Crypto.Protocols.PerfectSecrecy

/--
A private-key encryption scheme over message space `M`, key space `K`,
and ciphertext space `C` ([KatzLindell2020], Definition 2.1).
-/
structure EncScheme (Message Key Ciphertext : Type*) where
  /-- Probabilistic key generation. -/
  gen : PMF Key
  /-- (Possibly randomized) encryption. -/
  enc (key : Key) (message : Message) : PMF Ciphertext
  /-- Deterministic decryption. -/
  dec (key : Key) (ciphertext : Ciphertext) : Message
  /-- Decryption inverts encryption for all keys in the support of `gen`. -/
  correct : ∀ key, key ∈ gen.support → ∀ message ciphertext,
    ciphertext ∈ (enc key message).support → dec key ciphertext = message

/-- Build an encryption scheme from deterministic pure encryption/decryption
where decryption is a left inverse of encryption for every key. -/
noncomputable def EncScheme.ofPure.{u} {Message Key Ciphertext : Type u} (gen : PMF Key)
    (enc : Key → Message → Ciphertext) (dec : Key → Ciphertext → Message)
    (h : ∀ key, Function.LeftInverse (dec key) (enc key)) :
    EncScheme Message Key Ciphertext where
  gen := gen
  enc key message := PMF.pure (enc key message)
  dec := dec
  correct key _ message _ hc := by
    rw [PMF.mem_support_pure_iff] at hc; subst hc; exact h key message

end Cslib.Crypto.Protocols.PerfectSecrecy
