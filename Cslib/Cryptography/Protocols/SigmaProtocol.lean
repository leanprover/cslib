/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.SecurityGame

@[expose] public section

/-!
# Sigma Protocols

A **Sigma protocol** (Σ-protocol) is a three-move interactive proof
system between a prover and a verifier. The prover sends a commitment,
the verifier responds with a random challenge, and the prover sends
a response. The verifier then accepts or rejects.

Sigma protocols are the key abstraction for honest-verifier
zero-knowledge proofs and form the basis for Schnorr signatures,
the Fiat-Shamir heuristic, and many advanced protocols.

## Main Definitions

* `EffectiveRelation` — a relation between witnesses and statements
* `SigmaProtocol` — a three-move proof system for an `EffectiveRelation`
* `SigmaProtocol.SpecialSoundness` — from two accepting conversations
  with the same commitment but different challenges, one can extract
  a witness (Def 19.4 in Boneh-Shoup)
* `SigmaProtocol.SpecialHVZK` — a simulator can produce transcripts
  indistinguishable from real conversations (Def 19.5 in Boneh-Shoup)

## References

* Boneh-Shoup, *A Graduate Course in Applied Cryptography*, Ch. 19
* [O. Goldreich, *Foundations of Cryptography, Vol. 1*][Goldreich2001]
-/

/-- An **effective relation** between witnesses and statements, indexed
by the security parameter. This captures the NP relation underlying
a proof system: `relation n w y` means `w` is a valid witness for
statement `y` at security level `n`. -/
structure EffectiveRelation where
  /-- Witness type at security level `n` -/
  Witness : ℕ → Type
  /-- Statement type at security level `n` -/
  Statement : ℕ → Type
  /-- The relation: `relation n w y` holds when `w` is a valid
  witness for statement `y` -/
  relation : ∀ n, Witness n → Statement n → Prop

/-- A **key generation** for an effective relation bundles a key
derivation function (`keyOf`) that maps a witness (secret key) to
its canonical statement (public key), together with a proof that
the derived statement always satisfies the relation.

Not every relation admits a natural key generation — for example,
OR relations receive both statements externally. Use this wrapper
when the relation supports key derivation (e.g., discrete log). -/
structure EffectiveRelation.WithKeyGen (R : EffectiveRelation) where
  /-- Key derivation: maps a witness (secret key) to its canonical
  statement (public key) -/
  keyOf : ∀ n, R.Witness n → R.Statement n
  /-- The derived statement always satisfies the relation -/
  keyOf_valid : ∀ n w, R.relation n w (keyOf n w)

/-- A **Sigma protocol** for an effective relation `R`. The protocol
is a three-move proof of knowledge:

1. **Commit**: The prover sends a commitment `t`
2. **Challenge**: The verifier sends a random challenge `c`
3. **Respond**: The prover sends a response `z`
4. **Verify**: The verifier accepts or rejects based on `(y, t, c, z)` -/
structure SigmaProtocol (R : EffectiveRelation) where
  /-- Commitment type -/
  Commitment : ℕ → Type
  /-- Challenge type -/
  Challenge : ℕ → Type
  /-- Response type -/
  Response : ℕ → Type
  /-- Prover's randomness type -/
  ProverRandomness : ℕ → Type
  /-- Commitments form a finite type -/
  commitmentFintype : ∀ n, Fintype (Commitment n)
  /-- Commitments are nonempty -/
  commitmentNonempty : ∀ n, Nonempty (Commitment n)
  /-- Commitments have decidable equality -/
  commitmentDecEq : ∀ n, DecidableEq (Commitment n)
  /-- Challenges form a finite type -/
  challengeFintype : ∀ n, Fintype (Challenge n)
  /-- Challenges are nonempty -/
  challengeNonempty : ∀ n, Nonempty (Challenge n)
  /-- Challenges have decidable equality -/
  challengeDecEq : ∀ n, DecidableEq (Challenge n)
  /-- Responses form a finite type -/
  responseFintype : ∀ n, Fintype (Response n)
  /-- Responses are nonempty -/
  responseNonempty : ∀ n, Nonempty (Response n)
  /-- Prover randomness forms a finite type -/
  proverRandomnessFintype : ∀ n, Fintype (ProverRandomness n)
  /-- Prover randomness is nonempty -/
  proverRandomnessNonempty : ∀ n, Nonempty (ProverRandomness n)
  /-- Prover's commitment function: given witness, statement, and
  randomness, produce a commitment -/
  commit : ∀ n, R.Witness n → R.Statement n →
    ProverRandomness n → Commitment n
  /-- Prover's response function: given witness, statement,
  randomness, and challenge, produce a response -/
  respond : ∀ n, R.Witness n → R.Statement n →
    ProverRandomness n → Challenge n → Response n
  /-- Verifier's decision function: given statement, commitment,
  challenge, and response, accept or reject -/
  verify : ∀ n, R.Statement n → Commitment n →
    Challenge n → Response n → Bool
  /-- **Completeness**: an honest prover with a valid witness is
  always accepted. For any `(w, y) ∈ R`, any randomness `r`, and
  any challenge `c`, the honest transcript is accepted. -/
  completeness : ∀ n (w : R.Witness n) (y : R.Statement n)
    (r : ProverRandomness n) (c : Challenge n),
    R.relation n w y →
    verify n y (commit n w y r) c (respond n w y r c) = true

attribute [instance] SigmaProtocol.commitmentFintype
  SigmaProtocol.commitmentNonempty SigmaProtocol.commitmentDecEq
  SigmaProtocol.challengeFintype SigmaProtocol.challengeNonempty
  SigmaProtocol.challengeDecEq SigmaProtocol.responseFintype
  SigmaProtocol.responseNonempty
  SigmaProtocol.proverRandomnessFintype
  SigmaProtocol.proverRandomnessNonempty

/-- **δ-unpredictable commitments** (Def 19.7, Boneh-Shoup): for any
valid witness-statement pair and any target commitment `t₀`, the
probability over prover randomness that `commit` produces `t₀` is `≤ δ(n)`. -/
def SigmaProtocol.UnpredictableCommitments {R : EffectiveRelation}
    (P : SigmaProtocol R) (δ : ℕ → ℝ) : Prop :=
  ∀ n (w : R.Witness n) (y : R.Statement n) (t₀ : P.Commitment n),
    R.relation n w y →
    Cslib.Probability.uniformExpect (P.ProverRandomness n)
      (fun r => if P.commit n w y r = t₀ then (1 : ℝ) else 0) ≤ δ n

/-- **Special soundness** (Def 19.4 in Boneh-Shoup): from two
accepting conversations `(t, c, z)` and `(t, c', z')` sharing the
same commitment `t` but with distinct challenges `c ≠ c'`, an
extractor can recover a valid witness. -/
structure SigmaProtocol.SpecialSoundness {R : EffectiveRelation}
    (P : SigmaProtocol R) where
  /-- The witness extractor -/
  extract : ∀ n, R.Statement n → P.Commitment n →
    P.Challenge n → P.Response n →
    P.Challenge n → P.Response n → R.Witness n
  /-- If both conversations accept and challenges differ, the
  extracted witness satisfies the relation -/
  soundness : ∀ n (y : R.Statement n) (t : P.Commitment n)
    (c : P.Challenge n) (z : P.Response n)
    (c' : P.Challenge n) (z' : P.Response n),
    c ≠ c' →
    P.verify n y t c z = true →
    P.verify n y t c' z' = true →
    R.relation n (extract n y t c z c' z') y

/-- **Special honest-verifier zero-knowledge** (Def 19.5 in
Boneh-Shoup): there exists a simulator that, given a statement `y`
and a challenge `c`, produces a commitment-response pair `(t, z)`
such that `(t, c, z)` is accepting and has the same distribution
as a real transcript. -/
structure SigmaProtocol.SpecialHVZK {R : EffectiveRelation}
    (P : SigmaProtocol R) where
  /-- Simulator randomness type -/
  SimRandomness : ℕ → Type
  /-- Simulator randomness is finite -/
  simRandomnessFintype : ∀ n, Fintype (SimRandomness n)
  /-- Simulator randomness is nonempty -/
  simRandomnessNonempty : ∀ n, Nonempty (SimRandomness n)
  /-- The simulator: given statement and challenge, produce
  commitment and response -/
  simulate : ∀ n, R.Statement n → P.Challenge n →
    SimRandomness n → P.Commitment n × P.Response n
  /-- Simulated transcripts are always accepting -/
  sim_accepting : ∀ n (y : R.Statement n) (c : P.Challenge n)
    (s : SimRandomness n),
    let (t, z) := simulate n y c s
    P.verify n y t c z = true
  /-- The simulated distribution equals the real distribution:
  for any `(w, y) ∈ R` and any function `f` on transcripts,
  `E_r[f(commit(w,y,r), respond(w,y,r,c))]
    = E_s[f(simulate(y,c,s))]`.

  This captures that the two distributions are identical. -/
  sim_distribution : ∀ n (w : R.Witness n) (y : R.Statement n)
    (c : P.Challenge n),
    R.relation n w y →
    ∀ (f : P.Commitment n × P.Response n → ℝ),
    Cslib.Probability.uniformExpect (P.ProverRandomness n)
      (fun r => f (P.commit n w y r, P.respond n w y r c)) =
    Cslib.Probability.uniformExpect (SimRandomness n)
      (fun s => f (simulate n y c s))

end
