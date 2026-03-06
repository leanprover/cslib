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
# Encryption Schemes and Security Notions

This file defines **symmetric** and **public-key encryption schemes**
and their standard game-based security notions:

- **IND-CPA** (indistinguishability under chosen-plaintext attack)
- **IND-CCA** (indistinguishability under chosen-ciphertext attack)
- **Semantic security** (simulation-based)

## Main Definitions

* `EncryptionScheme` — a symmetric encryption scheme (KeyGen, Enc, Dec)
* `PKEncryptionScheme` — a public-key encryption scheme
* `IND_CPA` — the IND-CPA security game
* `IND_CCA` — the IND-CCA security game
* `Correctness` — decryption recovers the plaintext

## Design Notes

We parameterize encryption schemes by abstract types for keys,
plaintexts, ciphertexts, and randomness. The security parameter `n : ℕ`
determines the key generation, and all algorithms are indexed by `n`.

Adversaries are modeled with `OracleInteraction` for the encryption
oracle (which is randomized and game-managed) and plain functions for
the decryption oracle (which is deterministic). The advantage
is `|Pr[correct guess] - 1/2|`.

## References

* [S. Goldwasser, S. Micali, *Probabilistic Encryption*][GoldwasserM1984]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

/-- A **symmetric encryption scheme** consists of key generation,
encryption, and decryption algorithms, parameterized by the security
parameter.

- `Key n` — the type of keys at security level `n`
- `Plaintext n` — the type of plaintexts
- `Ciphertext n` — the type of ciphertexts
- `Randomness n` — the type of encryption randomness
-/
structure EncryptionScheme where
  /-- Key type at security level n -/
  Key : ℕ → Type
  /-- Plaintext type at security level n -/
  Plaintext : ℕ → Type
  /-- Ciphertext type at security level n -/
  Ciphertext : ℕ → Type
  /-- Randomness type for encryption -/
  Randomness : ℕ → Type
  /-- Key type is finite (for sampling) -/
  keyFintype : ∀ n, Fintype (Key n)
  /-- Key type is nonempty -/
  keyNonempty : ∀ n, Nonempty (Key n)
  /-- Randomness type is finite (for sampling) -/
  randomnessFintype : ∀ n, Fintype (Randomness n)
  /-- Randomness type is nonempty -/
  randomnessNonempty : ∀ n, Nonempty (Randomness n)
  /-- Deterministic encryption given key, plaintext, and randomness -/
  encrypt : (n : ℕ) → Key n → Plaintext n → Randomness n → Ciphertext n
  /-- Deterministic decryption -/
  decrypt : (n : ℕ) → Key n → Ciphertext n → Option (Plaintext n)

/-- A **public-key encryption scheme** has separate public and secret
keys. Key generation produces a pair; encryption uses the public key;
decryption uses the secret key. -/
structure PKEncryptionScheme where
  /-- Public key type -/
  PublicKey : ℕ → Type
  /-- Secret key type -/
  SecretKey : ℕ → Type
  /-- Plaintext type -/
  Plaintext : ℕ → Type
  /-- Ciphertext type -/
  Ciphertext : ℕ → Type
  /-- Randomness for encryption -/
  Randomness : ℕ → Type
  /-- Key generation randomness type -/
  KeyGenRandomness : ℕ → Type
  /-- Key generation randomness is finite (for sampling) -/
  keyGenRandomnessFintype : ∀ n, Fintype (KeyGenRandomness n)
  /-- Key generation randomness is nonempty -/
  keyGenRandomnessNonempty : ∀ n, Nonempty (KeyGenRandomness n)
  /-- Randomness type is finite (for sampling) -/
  randomnessFintype : ∀ n, Fintype (Randomness n)
  /-- Randomness type is nonempty -/
  randomnessNonempty : ∀ n, Nonempty (Randomness n)
  /-- Key generation: produces a correlated (pk, sk) pair from randomness -/
  keyGen : (n : ℕ) → KeyGenRandomness n → PublicKey n × SecretKey n
  /-- Encrypt with the public key -/
  encrypt : (n : ℕ) → PublicKey n → Plaintext n → Randomness n → Ciphertext n
  /-- Decrypt with the secret key -/
  decrypt : (n : ℕ) → SecretKey n → Ciphertext n → Option (Plaintext n)

/-! ### Correctness -/

/-- An encryption scheme is **correct** if decryption always recovers
the plaintext. -/
def EncryptionScheme.Correct (E : EncryptionScheme) : Prop :=
  ∀ (n : ℕ) (k : E.Key n) (m : E.Plaintext n) (r : E.Randomness n),
    E.decrypt n k (E.encrypt n k m r) = some m

/-- A public-key encryption scheme is **correct** if decryption with
the matching secret key always recovers the plaintext, for any key
pair produced by `keyGen`. -/
def PKEncryptionScheme.Correct (E : PKEncryptionScheme) : Prop :=
  ∀ (n : ℕ) (kgr : E.KeyGenRandomness n) (m : E.Plaintext n)
    (r : E.Randomness n),
    let (pk, sk) := E.keyGen n kgr
    E.decrypt n sk (E.encrypt n pk m r) = some m

/-! ### IND-CPA Security -/

/-- An **IND-CPA adversary** for a symmetric encryption scheme.

The adversary operates in two phases, both with oracle access to
encryption via `OracleInteraction`:
1. `choose` — query the encryption oracle, then produce two challenge
   messages `(m₀, m₁)` and some state `σ`
2. `guess` — given the challenge ciphertext and state, query the
   encryption oracle, then guess which message was encrypted

The adversary never controls the encryption randomness — the game
supplies fresh randomness for each oracle query. -/
structure IND_CPA_Adversary (E : EncryptionScheme) where
  /-- Adversary state type -/
  State : ℕ → Type
  /-- Upper bound on encryption queries in Phase 1 -/
  numQueries1 : ℕ → ℕ
  /-- Upper bound on encryption queries in Phase 2 -/
  numQueries2 : ℕ → ℕ
  /-- Phase 1: query encryption oracle, then choose two challenge messages -/
  choose : (n : ℕ) →
    OracleInteraction (E.Plaintext n) (E.Ciphertext n)
      (E.Plaintext n × E.Plaintext n × State n)
  /-- Phase 2: given challenge ciphertext and state, query encryption
  oracle, then guess which message was encrypted -/
  guess : (n : ℕ) → E.Ciphertext n → State n →
    OracleInteraction (E.Plaintext n) (E.Ciphertext n) Bool

/-- The **IND-CPA security game** for a symmetric encryption scheme.

The coin space is
`Key n × (Fin q1 → Randomness n) × Randomness n × (Fin q2 → Randomness n) × Bool`.
The game pre-samples randomness for each oracle query slot.
On fuel exhaustion (`none` from `.run`), return `0` for the game body
(adversary defaults to losing). -/
noncomputable def IND_CPA_Game (E : EncryptionScheme) :
    SecurityGame (IND_CPA_Adversary E) where
  advantage A n :=
    let q1 := A.numQueries1 n
    let q2 := A.numQueries2 n
    letI := E.keyFintype n; letI := E.keyNonempty n
    letI := E.randomnessFintype n; letI := E.randomnessNonempty n
    |Cslib.Probability.uniformExpect
      (E.Key n × (Fin q1 → E.Randomness n) × E.Randomness n ×
       (Fin q2 → E.Randomness n) × Bool)
      (fun ⟨k, rs1, r_ch, rs2, b⟩ =>
        let encOracle1 : Fin q1 → E.Plaintext n → E.Ciphertext n :=
          fun i m => E.encrypt n k m (rs1 i)
        match (A.choose n).run q1 encOracle1 with
        | none => 0
        | some (_, m₀, m₁, σ) =>
          let challenge := if b then m₁ else m₀
          let ct := E.encrypt n k challenge r_ch
          let encOracle2 : Fin q2 → E.Plaintext n → E.Ciphertext n :=
            fun i m => E.encrypt n k m (rs2 i)
          match (A.guess n ct σ).run q2 encOracle2 with
          | none => 0
          | some (_, b') =>
            Cslib.Probability.boolToReal (b' == b))
     - 1 / 2|

/-! ### IND-CCA Security -/

/-- An **IND-CCA adversary** has access to both an encryption oracle
(via `OracleInteraction`, game-managed randomness) and a decryption
oracle (passed as a plain function, since decryption is deterministic).

Phase 1 and Phase 2 both have oracle access. In Phase 2, the
decryption oracle refuses to decrypt the challenge ciphertext. -/
structure IND_CCA_Adversary (E : EncryptionScheme) where
  /-- Adversary state type -/
  State : ℕ → Type
  /-- Upper bound on encryption queries in Phase 1 -/
  numQueries1 : ℕ → ℕ
  /-- Upper bound on encryption queries in Phase 2 -/
  numQueries2 : ℕ → ℕ
  /-- Phase 1: choose messages with encryption oracle and decryption
  oracle access -/
  choose : (n : ℕ) →
    (E.Ciphertext n → Option (E.Plaintext n)) →
    OracleInteraction (E.Plaintext n) (E.Ciphertext n)
      (E.Plaintext n × E.Plaintext n × State n)
  /-- Phase 2: guess with encryption oracle and restricted decryption
  oracle (cannot query challenge ct) -/
  guess : (n : ℕ) → E.Ciphertext n → State n →
    (E.Ciphertext n → Option (E.Plaintext n)) →
    OracleInteraction (E.Plaintext n) (E.Ciphertext n) Bool

/-- The **IND-CCA security game** for a symmetric encryption scheme.

In Phase 1, the adversary receives encryption and decryption oracles and
produces two challenge messages. In Phase 2, the adversary receives the
challenge ciphertext and a restricted decryption oracle that refuses to
decrypt the challenge ciphertext.

On fuel exhaustion (`none` from `.run`), return `0` for the game body. -/
noncomputable def IND_CCA_Game (E : EncryptionScheme)
    [∀ n, DecidableEq (E.Ciphertext n)] :
    SecurityGame (IND_CCA_Adversary E) where
  advantage A n :=
    let q1 := A.numQueries1 n
    let q2 := A.numQueries2 n
    letI := E.keyFintype n; letI := E.keyNonempty n
    letI := E.randomnessFintype n; letI := E.randomnessNonempty n
    |Cslib.Probability.uniformExpect
      (E.Key n × (Fin q1 → E.Randomness n) × E.Randomness n ×
       (Fin q2 → E.Randomness n) × Bool)
      (fun ⟨k, rs1, r_ch, rs2, b⟩ =>
        let encOracle1 : Fin q1 → E.Plaintext n → E.Ciphertext n :=
          fun i m => E.encrypt n k m (rs1 i)
        let decOracle := E.decrypt n k
        match (A.choose n decOracle).run q1 encOracle1 with
        | none => 0
        | some (_, m₀, m₁, σ) =>
          let challenge := if b then m₁ else m₀
          let ct := E.encrypt n k challenge r_ch
          let decOracle' : E.Ciphertext n → Option (E.Plaintext n) :=
            fun c => if c = ct then none else E.decrypt n k c
          let encOracle2 : Fin q2 → E.Plaintext n → E.Ciphertext n :=
            fun i m => E.encrypt n k m (rs2 i)
          match (A.guess n ct σ decOracle').run q2 encOracle2 with
          | none => 0
          | some (_, b') =>
            Cslib.Probability.boolToReal (b' == b))
     - 1 / 2|

/-- A symmetric encryption scheme is **IND-CCA secure** if the IND-CCA game
is secure against all adversaries. -/
def IND_CCA (E : EncryptionScheme) [∀ n, DecidableEq (E.Ciphertext n)] : Prop :=
  (IND_CCA_Game E).Secure

/-! ### Relationships between security notions -/

/-- Every IND-CPA adversary can be embedded into the IND-CCA setting
by ignoring the decryption oracle. -/
def IND_CPA_to_CCA (E : EncryptionScheme) (A : IND_CPA_Adversary E) :
    IND_CCA_Adversary E where
  State := A.State
  numQueries1 := A.numQueries1
  numQueries2 := A.numQueries2
  choose n _decOracle :=
    A.choose n
  guess n ct σ _decOracle :=
    A.guess n ct σ

/-- Every IND-CCA adversary can be turned into an IND-CPA adversary
by replacing the decryption oracle with one that always returns `none`.

This witnesses the fact that IND-CPA security is a weaker notion than
IND-CCA security. -/
def IND_CCA_to_CPA (E : EncryptionScheme) (A : IND_CCA_Adversary E) :
    IND_CPA_Adversary E where
  State := A.State
  numQueries1 := A.numQueries1
  numQueries2 := A.numQueries2
  choose n :=
    A.choose n (fun _ => none)
  guess n ct σ :=
    A.guess n ct σ (fun _ => none)

/-! ### PKE Security -/

/-- A **PKE IND-CPA adversary** for a public-key encryption scheme.

The adversary receives the public key and can encrypt on its own, so
no encryption oracle is needed (standard definition, KL Def 12.7). -/
structure PKE_IND_CPA_Adversary (E : PKEncryptionScheme) where
  /-- Adversary state type -/
  State : ℕ → Type
  /-- Phase 1: given public key, choose two challenge messages -/
  choose : (n : ℕ) → E.PublicKey n → E.Plaintext n × E.Plaintext n × State n
  /-- Phase 2: given challenge ciphertext and state, guess which
  message was encrypted -/
  guess : (n : ℕ) → E.Ciphertext n → State n → Bool

/-- The **PKE IND-CPA security game** for a public-key encryption scheme.

The coin space is `KeyGenRandomness n × Randomness n × Bool`. -/
noncomputable def PKE_IND_CPA_Game (E : PKEncryptionScheme) :
    SecurityGame (PKE_IND_CPA_Adversary E) where
  advantage A n :=
    letI := E.keyGenRandomnessFintype n; letI := E.keyGenRandomnessNonempty n
    letI := E.randomnessFintype n; letI := E.randomnessNonempty n
    |Cslib.Probability.uniformExpect
      (E.KeyGenRandomness n × E.Randomness n × Bool)
      (fun ⟨kgr, r, b⟩ =>
        let (pk, _sk) := E.keyGen n kgr
        let (m₀, m₁, σ) := A.choose n pk
        let challenge := if b then m₁ else m₀
        let ct := E.encrypt n pk challenge r
        let b' := A.guess n ct σ
        Cslib.Probability.boolToReal (b' == b))
     - 1 / 2|

/-- A **PKE IND-CCA adversary** for a public-key encryption scheme.

The adversary receives the public key (so can encrypt freely) and
a decryption oracle (passed as a plain function). In Phase 2, the
decryption oracle refuses to decrypt the challenge ciphertext. -/
structure PKE_IND_CCA_Adversary (E : PKEncryptionScheme) where
  /-- Adversary state type -/
  State : ℕ → Type
  /-- Phase 1: given public key and decryption oracle, choose two
  challenge messages -/
  choose : (n : ℕ) → E.PublicKey n →
    (E.Ciphertext n → Option (E.Plaintext n)) →
    E.Plaintext n × E.Plaintext n × State n
  /-- Phase 2: given challenge ciphertext, state, and restricted
  decryption oracle, guess which message was encrypted -/
  guess : (n : ℕ) → E.Ciphertext n → State n →
    (E.Ciphertext n → Option (E.Plaintext n)) → Bool

/-- The **PKE IND-CCA security game** for a public-key encryption scheme.

The coin space is `KeyGenRandomness n × Randomness n × Bool`. -/
noncomputable def PKE_IND_CCA_Game (E : PKEncryptionScheme)
    [∀ n, DecidableEq (E.Ciphertext n)] :
    SecurityGame (PKE_IND_CCA_Adversary E) where
  advantage A n :=
    letI := E.keyGenRandomnessFintype n; letI := E.keyGenRandomnessNonempty n
    letI := E.randomnessFintype n; letI := E.randomnessNonempty n
    |Cslib.Probability.uniformExpect
      (E.KeyGenRandomness n × E.Randomness n × Bool)
      (fun ⟨kgr, r, b⟩ =>
        let (pk, sk) := E.keyGen n kgr
        let decOracle := E.decrypt n sk
        let (m₀, m₁, σ) := A.choose n pk decOracle
        let challenge := if b then m₁ else m₀
        let ct := E.encrypt n pk challenge r
        let decOracle' : E.Ciphertext n → Option (E.Plaintext n) :=
          fun c => if c = ct then none else E.decrypt n sk c
        let b' := A.guess n ct σ decOracle'
        Cslib.Probability.boolToReal (b' == b))
     - 1 / 2|

end
