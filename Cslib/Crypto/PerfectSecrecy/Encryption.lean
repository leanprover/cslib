/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.ProbabilityMassFunction.Monad

@[expose] public section

/-!
# Private-Key Encryption Schemes (Information-Theoretic)

An information-theoretic private-key encryption scheme following
[KatzLindell2020], Definition 2.1. Key generation and encryption are
probability distributions over arbitrary types, with no computational
constraints.

## Main definitions

- `Cslib.Crypto.PerfectSecrecy.EncScheme`:
  a private-key encryption scheme (Gen, Enc, Dec) with correctness

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

namespace Cslib.Crypto.PerfectSecrecy

/--
A private-key encryption scheme over message space `M`, key space `K`,
and ciphertext space `C` ([KatzLindell2020], Definition 2.1).
-/
structure EncScheme.{u} (M K C : Type u) where
  /-- Probabilistic key generation. -/
  gen : PMF K
  /-- (Possibly randomized) encryption. -/
  enc : K → M → PMF C
  /-- Deterministic decryption. -/
  dec : K → C → M
  /-- Decryption inverts encryption for all keys in the support of `gen`. -/
  correct : ∀ k, k ∈ gen.support → ∀ m c, c ∈ (enc k m).support → dec k c = m

end Cslib.Crypto.PerfectSecrecy
