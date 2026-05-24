/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import Cslib.Probability.PMF

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
structure EncScheme (m : Type u → Type*)
    (Message Key Ciphertext : Type u) where
  /-- Probabilistic key generation. -/
  gen : m Key
  /-- (Possibly randomized) encryption. -/
  enc (key : Key) (message : Message) : m Ciphertext
  /-- Deterministic decryption. -/
  dec (key : Key) (ciphertext : Ciphertext) : Message

variable {m : Type u → Type*} [Monad m]

/-- Decryption inverts encryption for all keys in the support of `gen`. -/
class EncScheme.Correct [MonadLiftT m PMF] {Message Key Ciphertext : Type u}
    (scheme : EncScheme m Message Key Ciphertext) : Prop where
  dec_enc : ∀ key, key ∈ PMF.support scheme.gen → ∀ message ciphertext,
    ciphertext ∈ PMF.support (scheme.enc key message) → scheme.dec key ciphertext = message

/-- Build an encryption scheme from deterministic pure encryption/decryption. -/
def EncScheme.ofPure {Message Key Ciphertext : Type u} (gen : m Key)
    (enc : Key → Message → Ciphertext) (dec : Key → Ciphertext → Message) :
    EncScheme m Message Key Ciphertext where
  gen := gen
  enc key message := pure (enc key message)
  dec := dec

/-- `EncScheme.ofPure` is correct if decryption is a left inverse of encryption for every key. -/
lemma EncScheme.ofPure.Correct [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {Message Key Ciphertext : Type u} (gen : m Key)
    (enc : Key → Message → Ciphertext) (dec : Key → Ciphertext → Message)
    (h : ∀ key, Function.LeftInverse (dec key) (enc key)) :
    (EncScheme.ofPure gen enc dec).Correct where
  dec_enc key _ message ciphertext hc := by
    have : ciphertext = enc key message := by simpa [EncScheme.ofPure] using hc
    subst this; exact h key message

end Cslib.Crypto.Protocols.PerfectSecrecy
