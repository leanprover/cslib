/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Protocols.SigmaProtocol
public import Cslib.Cryptography.Primitives.Signature

@[expose] public section

/-!
# The Fiat-Shamir Transform

The **Fiat-Shamir transform** converts any Sigma protocol into a
(non-interactive) signature scheme by replacing the verifier's random
challenge with the output of a hash function applied to the message
and the commitment.

## Main Definitions

* `FiatShamirSignature` — generic construction of a signature scheme
  from a Sigma protocol and a hash function
* `FiatShamirSignature.correct` — correctness follows from protocol
  completeness

## Design Notes

The transform is parameterized by:
- A Sigma protocol `P` for a relation `R`
- A hash function `H : Message → Commitment → Challenge`
- Key generation data (witness/statement types with finiteness)

In the random oracle model, the Fiat-Shamir transform preserves
the security of the underlying Sigma protocol: special soundness
implies unforgeability.

## References

* [A. Fiat, A. Shamir, *How to Prove Yourself*][FiatShamir1986]
* Boneh-Shoup, *A Graduate Course in Applied Cryptography*, §19.6.1
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

/-- The **Fiat-Shamir signature scheme** constructed from a Sigma
protocol by deriving the challenge from a hash of the message and
commitment.

- **Key generation**: the secret key is a witness, the public key
  is the corresponding statement
- **Sign**: run the prover with `c = H(m, t)` where `t` is the
  commitment
- **Verify**: compute `c = H(m, t)`, check the Sigma protocol
  verifier accepts -/
noncomputable def FiatShamirSignature
    {R : EffectiveRelation}
    (P : SigmaProtocol R)
    (Message : ℕ → Type)
    [∀ n, DecidableEq (Message n)]
    (H : ∀ n, Message n → P.Commitment n → P.Challenge n)
    [∀ n, Fintype (R.Witness n)]
    [∀ n, Nonempty (R.Witness n)]
    [∀ n, Fintype (R.Statement n)]
    [∀ n, Nonempty (R.Statement n)]
    (kg : R.WithKeyGen) :
    SignatureScheme where
  PublicKey := R.Statement
  SecretKey := R.Witness
  Message := Message
  Signature n := P.Commitment n × P.Response n
  Randomness := P.ProverRandomness
  publicKeyFintype := inferInstance
  secretKeyFintype := inferInstance
  publicKeyNonempty := inferInstance
  secretKeyNonempty := inferInstance
  randomnessFintype := P.proverRandomnessFintype
  randomnessNonempty := P.proverRandomnessNonempty
  KeyGenRandomness := R.Witness
  keyGenRandomnessFintype := inferInstance
  keyGenRandomnessNonempty := inferInstance
  keyGen n w := (kg.keyOf n w, w)
  sign n w m r :=
    let y := kg.keyOf n w
    let t := P.commit n w y r
    let c := H n m t
    let z := P.respond n w y r c
    (t, z)
  verify n y m sig :=
    let (t, z) := sig
    let c := H n m t
    P.verify n y t c z

/-- The Fiat-Shamir signature scheme is **correct** when the key
generation function maps witnesses to statements satisfying the
relation.

This follows directly from the completeness of the underlying
Sigma protocol. -/
theorem FiatShamirSignature.correct
    {R : EffectiveRelation}
    (P : SigmaProtocol R)
    (Message : ℕ → Type)
    [∀ n, DecidableEq (Message n)]
    (H : ∀ n, Message n → P.Commitment n → P.Challenge n)
    [∀ n, Fintype (R.Witness n)]
    [∀ n, Nonempty (R.Witness n)]
    [∀ n, Fintype (R.Statement n)]
    [∀ n, Nonempty (R.Statement n)]
    (kg : R.WithKeyGen) :
    (FiatShamirSignature P Message H kg).Correct := by
  intro n w m r
  simp only [FiatShamirSignature]
  exact P.completeness n _ _ r _ (kg.keyOf_valid n w)

end
