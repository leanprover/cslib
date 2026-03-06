/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.OracleInteraction
public import Cslib.Cryptography.Foundations.SecurityGame

@[expose] public section

/-!
# Digital Signature Schemes

A **digital signature scheme** allows a signer to produce a signature
on a message that can be verified by anyone with the signer's public
key, but cannot be forged without the secret key.

## Main Definitions

* `SignatureScheme` — a digital signature scheme (KeyGen, Sign, Verify)
* `EUF_CMA` — existential unforgeability under chosen-message attack

## Design Notes

We model signature schemes with abstract types for keys, messages,
signatures, and randomness. The security notion EUF-CMA says that
no efficient adversary, even after seeing signatures on chosen messages,
can produce a valid signature on a new message.

## References

* [S. Goldwasser, S. Micali, R. Rivest, *A Digital Signature Scheme
  Secure Against Adaptive Chosen-Message Attacks*][GMR1988]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

/-- A **digital signature scheme** parameterized by the security parameter.

- `PublicKey n` — verification key
- `SecretKey n` — signing key
- `Message n` — message type
- `Signature n` — signature type
-/
structure SignatureScheme where
  /-- Public (verification) key type -/
  PublicKey : ℕ → Type
  /-- Secret (signing) key type -/
  SecretKey : ℕ → Type
  /-- Message type -/
  Message : ℕ → Type
  /-- Signature type -/
  Signature : ℕ → Type
  /-- Randomness for signing -/
  Randomness : ℕ → Type
  /-- Public key type is finite (for sampling) -/
  publicKeyFintype : ∀ n, Fintype (PublicKey n)
  /-- Secret key type is finite (for sampling) -/
  secretKeyFintype : ∀ n, Fintype (SecretKey n)
  /-- Key types are nonempty -/
  publicKeyNonempty : ∀ n, Nonempty (PublicKey n)
  secretKeyNonempty : ∀ n, Nonempty (SecretKey n)
  /-- Signing randomness is finite (for sampling) -/
  randomnessFintype : ∀ n, Fintype (Randomness n)
  /-- Signing randomness is nonempty -/
  randomnessNonempty : ∀ n, Nonempty (Randomness n)
  /-- Key generation randomness type -/
  KeyGenRandomness : ℕ → Type
  /-- Key generation randomness is finite (for sampling) -/
  keyGenRandomnessFintype : ∀ n, Fintype (KeyGenRandomness n)
  /-- Key generation randomness is nonempty -/
  keyGenRandomnessNonempty : ∀ n, Nonempty (KeyGenRandomness n)
  /-- Key generation: produces a correlated (pk, sk) pair from randomness -/
  keyGen : (n : ℕ) → KeyGenRandomness n → PublicKey n × SecretKey n
  /-- Sign a message with the secret key -/
  sign : (n : ℕ) → SecretKey n → Message n → Randomness n →
    Signature n
  /-- Verify a signature with the public key -/
  verify : (n : ℕ) → PublicKey n → Message n → Signature n → Bool

/-! ### Correctness -/

/-- A signature scheme is **correct** if honestly generated signatures
always verify for any key pair produced by `keyGen`. -/
def SignatureScheme.Correct (S : SignatureScheme) : Prop :=
  ∀ (n : ℕ) (kgr : S.KeyGenRandomness n) (m : S.Message n) (r : S.Randomness n),
    let (pk, sk) := S.keyGen n kgr
    S.verify n pk m (S.sign n sk m r) = true

/-! ### EUF-CMA Security -/

/-- An **EUF-CMA adversary** for a signature scheme models adaptive
chosen-message attack via `OracleInteraction`.

The adversary receives the public key and interacts with a signing
oracle by issuing queries of type `S.Message n` and receiving
responses of type `S.Signature n`. The adversary never controls the
signing randomness — the game supplies it. After the interaction,
the adversary outputs a forgery attempt `(message, signature)`.

- `numQueries n` — an upper bound on the number of signing queries
  at security parameter `n` (used as fuel for `OracleInteraction.run`)
- `interact n pk` — the adaptive oracle interaction producing a
  forgery attempt -/
structure EUF_CMA_Adversary (S : SignatureScheme) where
  /-- Upper bound on the number of signing queries -/
  numQueries : ℕ → ℕ
  /-- The adaptive oracle interaction: given a public key, query the
  signing oracle and produce a forgery attempt `(message, signature)` -/
  interact : (n : ℕ) → S.PublicKey n →
    OracleInteraction (S.Message n) (S.Signature n)
      (S.Message n × S.Signature n)

/-- The **EUF-CMA security game** for a signature scheme.

The game samples key generation randomness `kgr` and signing randomness
`rs : Fin q → S.Randomness n` (one per query slot), then derives the
key pair `(pk, sk) = S.keyGen n kgr`. The signing oracle is
`fun i m => S.sign n sk m (rs i)` — the adversary never touches the
randomness. The game runs the interaction, logs all queries, and checks:
1. The forgery message was not among the queried messages
2. The forged signature verifies under the public key

The advantage is
`E_{kgr,rs}[1[interaction succeeds ∧ forgery valid ∧ fresh]]`. -/
noncomputable def SignatureScheme.EUF_CMA_Game (S : SignatureScheme)
    [∀ n, DecidableEq (S.Message n)] :
    SecurityGame (EUF_CMA_Adversary S) where
  advantage A n :=
    let q := A.numQueries n
    letI := S.keyGenRandomnessFintype n; letI := S.keyGenRandomnessNonempty n
    letI := S.randomnessFintype n; letI := S.randomnessNonempty n
    Cslib.Probability.uniformExpect
      (S.KeyGenRandomness n × (Fin q → S.Randomness n))
      (fun ⟨kgr, rs⟩ =>
        let (pk, sk) := S.keyGen n kgr
        let oracle : Fin q → S.Message n → S.Signature n :=
          fun i m => S.sign n sk m (rs i)
        match (A.interact n pk).run q oracle with
        | none => 0
        | some (queries, m, σ) =>
          Cslib.Probability.boolToReal
            (S.verify n pk m σ && !(queries.contains m)))

/-- A signature scheme is **EUF-CMA secure** if the EUF-CMA game
is secure against all adversaries. -/
def SignatureScheme.EUF_CMA (S : SignatureScheme)
    [∀ n, DecidableEq (S.Message n)] : Prop :=
  S.EUF_CMA_Game.Secure

/-- A signature scheme is **EUF-CMA secure against** a class of
adversaries. -/
def SignatureScheme.EUF_CMA_Against (S : SignatureScheme)
    [∀ n, DecidableEq (S.Message n)]
    (Admissible : EUF_CMA_Adversary S → Prop) : Prop :=
  S.EUF_CMA_Game.SecureAgainst Admissible

end
