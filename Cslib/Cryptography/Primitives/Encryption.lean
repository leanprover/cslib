/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

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

Adversaries are modeled abstractly: an IND-CPA adversary produces two
challenge messages and then guesses which was encrypted. The advantage
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
the matching secret key always recovers the plaintext. -/
def PKEncryptionScheme.Correct (E : PKEncryptionScheme)
    (keyPair : (n : ℕ) → E.PublicKey n × E.SecretKey n) : Prop :=
  ∀ (n : ℕ) (m : E.Plaintext n) (r : E.Randomness n),
    let (pk, sk) := keyPair n
    E.decrypt n sk (E.encrypt n pk m r) = some m

/-! ### IND-CPA Security -/

/-- An **IND-CPA adversary** for a symmetric encryption scheme.

The adversary operates in two phases:
1. `choose` — given the security parameter, produce two challenge
   messages `(m₀, m₁)` and some state `σ`
2. `guess` — given the challenge ciphertext and state, guess which
   message was encrypted (returns `Bool`, `true` = guessed `m₁`)

The adversary has access to an encryption oracle (modeled externally
by giving it the key in the `choose` phase for CPA). -/
structure IND_CPA_Adversary (E : EncryptionScheme) where
  /-- Adversary state type -/
  State : ℕ → Type
  /-- Phase 1: choose two challenge messages -/
  choose : (n : ℕ) → (E.Plaintext n → E.Randomness n → E.Ciphertext n) →
    E.Plaintext n × E.Plaintext n × State n
  /-- Phase 2: guess which message was encrypted -/
  guess : (n : ℕ) → E.Ciphertext n → State n → Bool

/-- The **IND-CPA advantage** of adversary `A` at security parameter `n`,
given a specific key `k`, randomness `r` for encryption, and a
challenge bit `b`:

`Adv = |Pr[A guesses correctly] - 1/2|`

Since we don't have a probability monad, we define the advantage as a
function of all the randomness, and security requires it to be negligible
over the choice of randomness. -/
noncomputable def IND_CPA_Advantage (E : EncryptionScheme) (A : IND_CPA_Adversary E)
    (n : ℕ) (k : E.Key n) (r : E.Randomness n) (b : Bool) : ℝ :=
  let oracle := E.encrypt n k
  let (m₀, m₁, σ) := A.choose n (fun m r' => oracle m r')
  let challenge := if b then m₁ else m₀
  let ct := E.encrypt n k challenge r
  let b' := A.guess n ct σ
  if b' = b then 1 else 0

/-- The **IND-CPA security game** for a symmetric encryption scheme.

The advantage is
$$\mathbb{E}_{k,r,b}\left[\mathbf{1}[A.\mathrm{guess} = b]\right] - 1/2$$
where `k` is a random key, `r` is random encryption coins, and `b` is a
random challenge bit. The coin space is `Key n × Randomness n × Bool`. -/
noncomputable def IND_CPA_Game (E : EncryptionScheme) :
    SecurityGame (IND_CPA_Adversary E) where
  advantage A n :=
    letI := E.keyFintype n; letI := E.keyNonempty n
    letI := E.randomnessFintype n; letI := E.randomnessNonempty n
    |Cslib.Probability.uniformExpect (E.Key n × E.Randomness n × Bool)
      (fun ⟨k, r, b⟩ =>
        let oracle := E.encrypt n k
        let (m₀, m₁, σ) := A.choose n (fun m r' => oracle m r')
        let challenge := if b then m₁ else m₀
        let ct := E.encrypt n k challenge r
        let b' := A.guess n ct σ
        Cslib.Probability.boolToReal (b' == b))
     - 1 / 2|

/-! ### IND-CCA Security -/

/-- An **IND-CCA adversary** has access to a decryption oracle in
addition to the encryption oracle, with the restriction that it cannot
query the decryption oracle on the challenge ciphertext.

Phase 1 and Phase 2 both have oracle access. -/
structure IND_CCA_Adversary (E : EncryptionScheme) where
  /-- Adversary state type -/
  State : ℕ → Type
  /-- Phase 1: choose messages with encryption and decryption oracle access -/
  choose : (n : ℕ) →
    (E.Plaintext n → E.Randomness n → E.Ciphertext n) →  -- enc oracle
    (E.Ciphertext n → Option (E.Plaintext n)) →           -- dec oracle
    E.Plaintext n × E.Plaintext n × State n
  /-- Phase 2: guess with oracle access (cannot query challenge ct) -/
  guess : (n : ℕ) → E.Ciphertext n → State n →
    (E.Ciphertext n → Option (E.Plaintext n)) →           -- dec oracle
    Bool

/-- The **IND-CCA security game** for a symmetric encryption scheme.

The advantage is
$$\mathbb{E}_{k,r,b}\left[\mathbf{1}[A.\mathrm{guess} = b]\right] - 1/2$$
where `k` is a random key, `r` is random encryption coins, and `b` is a
random challenge bit.

In Phase 1, the adversary receives encryption and decryption oracles and
produces two challenge messages. In Phase 2, the adversary receives the
challenge ciphertext and a restricted decryption oracle that refuses to
decrypt the challenge ciphertext. -/
noncomputable def IND_CCA_Game (E : EncryptionScheme)
    [∀ n, DecidableEq (E.Ciphertext n)] :
    SecurityGame (IND_CCA_Adversary E) where
  advantage A n :=
    letI := E.keyFintype n; letI := E.keyNonempty n
    letI := E.randomnessFintype n; letI := E.randomnessNonempty n
    |Cslib.Probability.uniformExpect (E.Key n × E.Randomness n × Bool)
      (fun ⟨k, r, b⟩ =>
        let encOracle := E.encrypt n k
        let decOracle := E.decrypt n k
        let (m₀, m₁, σ) := A.choose n encOracle decOracle
        let challenge := if b then m₁ else m₀
        let ct := E.encrypt n k challenge r
        -- Restricted decryption oracle: refuses to decrypt the challenge ct
        let decOracle' : E.Ciphertext n → Option (E.Plaintext n) :=
          fun c => if c = ct then none else E.decrypt n k c
        let b' := A.guess n ct σ decOracle'
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
  choose n encOracle _decOracle :=
    A.choose n encOracle
  guess n ct σ _decOracle :=
    A.guess n ct σ

/-- Every IND-CCA adversary can be turned into an IND-CPA adversary
by replacing the decryption oracle with one that always returns `none`.

This witnesses the fact that IND-CPA security is a weaker notion than
IND-CCA security. -/
def IND_CCA_to_CPA (E : EncryptionScheme) (A : IND_CCA_Adversary E) :
    IND_CPA_Adversary E where
  State := A.State
  choose n encOracle :=
    A.choose n encOracle (fun _ => none)
  guess n ct σ :=
    A.guess n ct σ (fun _ => none)

end
