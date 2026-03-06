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
# Message Authentication Codes

A **message authentication code (MAC)** allows a party to produce a
short tag on a message such that anyone sharing the secret key can
verify the tag, but no one without the key can forge a valid tag on
a new message.

## Main Definitions

* `MACScheme` — a MAC scheme (Tag, Verify)
* `MACScheme.EUF_CMA_Adversary` — existential unforgeability adversary
* `MACScheme.EUF_CMA_Game` — the EUF-CMA security game
* `MACScheme.EUF_CMA_Secure` — security predicate

## Design Notes

The adversary adaptively queries a tagging oracle via
`OracleInteraction` and must forge a valid tag on a message it
never queried. The game logs all queries and checks freshness.

The EUF-CMA game is a **search game** (baseline 0, not 1/2).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014], §4.3
* [M. Bellare, J. Kilian, P. Rogaway, *The Security of the Cipher
  Block Chaining Message Authentication Code*][BKR2000]
-/

/-- A **message authentication code scheme** parameterized by the
security parameter.

- `Key n` — the type of secret keys at security level `n`
- `Message n` — the type of messages
- `Tag n` — the type of authentication tags
-/
structure MACScheme where
  /-- Key type at security level n -/
  Key : ℕ → Type
  /-- Message type -/
  Message : ℕ → Type
  /-- Tag type -/
  Tag : ℕ → Type
  /-- Key type is finite (for sampling) -/
  keyFintype : ∀ n, Fintype (Key n)
  /-- Key type is nonempty -/
  keyNonempty : ∀ n, Nonempty (Key n)
  /-- The tagging function -/
  tag : (n : ℕ) → Key n → Message n → Tag n
  /-- The verification function -/
  verify : (n : ℕ) → Key n → Message n → Tag n → Bool

/-! ### Correctness -/

/-- A MAC scheme is **correct** if verification always accepts honestly
generated tags. -/
def MACScheme.Correct (M : MACScheme) : Prop :=
  ∀ (n : ℕ) (k : M.Key n) (m : M.Message n),
    M.verify n k m (M.tag n k m) = true

/-! ### EUF-CMA Security -/

/-- An **EUF-CMA adversary** for a MAC scheme models adaptive
chosen-message attack via `OracleInteraction`.

The adversary interacts with a tagging oracle by issuing queries of
type `M.Message n` and receiving responses of type `M.Tag n`. After
the interaction, the adversary outputs a forgery attempt
`(message, tag)`. The game logs all queries and checks freshness —
the adversary never self-reports which messages it queried.

- `numQueries n` — an upper bound on the number of tagging queries
  at security parameter `n` (used as fuel for `OracleInteraction.run`)
- `interact n` — the adaptive oracle interaction producing a forgery
  attempt -/
structure MACScheme.EUF_CMA_Adversary (M : MACScheme) where
  /-- Upper bound on the number of tagging queries -/
  numQueries : ℕ → ℕ
  /-- The adaptive oracle interaction: query the tagging oracle and
  produce a forgery attempt `(message, tag)` -/
  interact : (n : ℕ) →
    OracleInteraction (M.Message n) (M.Tag n)
      (M.Message n × M.Tag n)

/-- The **EUF-CMA security game** for a MAC scheme.

The game samples a key `k` and runs the adversary's oracle
interaction with oracle `fun _i m => M.tag n k m` (MACs are
deterministic, so the query index is unused). The game logs all
queries and checks:
1. The forgery message was not among the queried messages
2. The forged tag verifies under the key

The advantage is `E_k[1[interaction succeeds ∧ forgery valid ∧ fresh]]`.
This is a **search game** with baseline 0. -/
noncomputable def MACScheme.EUF_CMA_Game (M : MACScheme)
    [∀ n, DecidableEq (M.Message n)] :
    SecurityGame (MACScheme.EUF_CMA_Adversary M) where
  advantage A n :=
    let q := A.numQueries n
    letI := M.keyFintype n; letI := M.keyNonempty n
    Cslib.Probability.uniformExpect (M.Key n) (fun k =>
      let oracle : Fin q → M.Message n → M.Tag n :=
        fun _i m => M.tag n k m
      match (A.interact n).run q oracle with
      | none => 0
      | some (queries, m_forge, t_forge) =>
        Cslib.Probability.boolToReal
          (M.verify n k m_forge t_forge && !(queries.contains m_forge)))

/-- A MAC scheme is **EUF-CMA secure** if the EUF-CMA game is secure
against all adversaries. -/
def MACScheme.EUF_CMA_Secure (M : MACScheme)
    [∀ n, DecidableEq (M.Message n)] : Prop :=
  M.EUF_CMA_Game.Secure

/-- A MAC scheme is **EUF-CMA secure against** a class of adversaries. -/
def MACScheme.EUF_CMA_SecureAgainst (M : MACScheme)
    [∀ n, DecidableEq (M.Message n)]
    (Admissible : MACScheme.EUF_CMA_Adversary M → Prop) : Prop :=
  M.EUF_CMA_Game.SecureAgainst Admissible

end
