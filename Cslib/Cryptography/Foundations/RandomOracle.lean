/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Protocols.SigmaProtocol
public import Cslib.Cryptography.Foundations.OracleInteraction

@[expose] public section

/-!
# ROM EUF-CMA Security Games for Fiat-Shamir Signatures

This file defines the **security games** used to state and prove the
ROM (Random Oracle Model) security of Fiat-Shamir signature schemes
derived from Sigma protocols. It provides the game definitions; the
security reduction is in `Cslib.Cryptography.Reductions.FiatShamirROM`.

## Main Definitions

* `assocLookup` — association-list lookup, used for Map-based ROM
  simulations throughout the game-hop chain
* `ROM_EUF_CMA_Adversary` — an adversary that adaptively queries a
  signing oracle and a hash oracle (modeled via a sum-type
  `OracleInteraction`), then outputs a forgery `(m★, t★, z★)`
* `romCmaOracle` — the stateful oracle that handles signing and hash
  queries in the real ROM game, using lazy sampling with an association
  list for consistency
* `romCmaWinCondition` — the win-condition predicate: the forgery
  verifies, the message is fresh, and `(m★, t★)` was explicitly
  hash-queried
* `ROM_EUF_CMA_Game` — the full ROM EUF-CMA security game, as a
  `SecurityGame` instance
* `RelationSolver` — an adversary that, given a statement, attempts to
  find a valid witness
* `RelationGame` — the relation-hardness game (natural-keygen variant):
  sample `w` uniformly, give `keyOf w` to the solver, check the output

## Design Notes

**Two-oracle model via sum types.** The adversary issues queries of type
`Msg ⊕ (Msg × Commitment)`:
- `Sum.inl m` — signing query for message `m`, answered with `(t, z)`
- `Sum.inr (m, t)` — hash query for `(m, t)`, answered with challenge `c`

**Lazy-sampling ROM.** The random oracle is implemented by threading an
association list `List ((Msg × Commitment) × Challenge)` as state: fresh
keys receive a uniformly sampled challenge; repeated keys are answered
consistently from the list.

**Explicit-query requirement.** Following the proof-friendly setup in
Boneh-Shoup §19.2.2 / §19.6 (Theorem 19.7), the win condition requires
`(m★, t★)` to appear among the adversary's explicit hash queries
(`Sum.inr`). This is a standard simplification that loses nothing
asymptotically.

**Single query bound.** We use one total query count `q = A.numQueries n`
covering both hash and signing queries. In the book notation this
corresponds to the combined budget `Qs + Qro`.

## References

* Boneh-Shoup, *A Graduate Course in Applied Cryptography*, §19.6
* [M. Bellare, P. Rogaway, *Random Oracles are Practical*][BellareR1993]
-/

open Cslib.Probability

/-- Association-list lookup for map-style ROM simulations. -/
noncomputable def assocLookup {α β : Type} [DecidableEq α]
    (key : α) : List (α × β) → Option β
  | [] => none
  | (k, v) :: rest => if k = key then some v else assocLookup key rest

/-- A **ROM EUF-CMA adversary** for a Fiat-Shamir signature scheme.

The adversary receives the public key (statement) and adaptively
queries either:
- `Sum.inl m` — request a signature on message `m`
- `Sum.inr (m, t)` — request the hash of `(m, t)`

The responses are:
- `Sum.inl (t, z)` — a signature (commitment, response)
- `Sum.inr c` — a hash value (challenge)

The adversary eventually outputs a forgery `(m★, t★, z★)`. -/
structure ROM_EUF_CMA_Adversary {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) where
  /-- Upper bound on the total number of queries (hash + sign) -/
  numQueries : ℕ → ℕ
  /-- The adaptive oracle interaction -/
  interact : (n : ℕ) → R.Statement n →
    OracleInteraction
      (Msg n ⊕ (Msg n × P.Commitment n))
      ((P.Commitment n × P.Response n) ⊕ P.Challenge n)
      (Msg n × P.Commitment n × P.Response n)

/-- The **stateful oracle** for the ROM EUF-CMA game.

The oracle handles two kinds of queries via a sum type:

- **Signing queries** (`Sum.inl m`): commit using `rs i`, look up or lazily
  sample the challenge for `(m, t)`, then respond — returning the signature
  `(t, z)` and updating the association list.
- **Hash queries** (`Sum.inr (m, t)`): look up or lazily sample the challenge
  for `(m, t)`, returning it and updating the association list. -/
noncomputable def romCmaOracle {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (Hs : Fin q → (Msg n × P.Commitment n → P.Challenge n))
    [DecidableEq (P.Commitment n)] :
    Fin q →
    List ((Msg n × P.Commitment n) × P.Challenge n) →
    (Msg n ⊕ (Msg n × P.Commitment n)) →
    ((P.Commitment n × P.Response n) ⊕ P.Challenge n) ×
      List ((Msg n × P.Commitment n) × P.Challenge n) :=
  fun i map qry =>
    match qry with
    | .inl m =>
      let t := P.commit n w y (rs i)
      match assocLookup (m, t) map with
      | some c => (.inl (t, P.respond n w y (rs i) c), map)
      | none =>
        let c := Hs i (m, t)
        (.inl (t, P.respond n w y (rs i) c), ((m, t), c) :: map)
    | .inr (m, t) =>
      match assocLookup (m, t) map with
      | some c => (.inr c, map)
      | none =>
        let c := Hs i (m, t)
        (.inr c, ((m, t), c) :: map)

/-- The **win condition** for the ROM EUF-CMA game.

Given the result of running the adversary's oracle interaction, returns `1`
if the adversary wins and `0` otherwise. The adversary wins when all three
conditions hold:

1. **Forgery verifies**: `P.verify y t★ c z★ = true` where `c` is the
   challenge recorded for `(m★, t★)` in the hash table.
2. **Message is fresh**: `m★` was not previously submitted as a signing query.
3. **Explicit hash query**: `(m★, t★)` appears among the adversary's queries
   as an explicit hash query (`Sum.inr (m★, t★)`). -/
noncomputable def romCmaWinCondition {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ) (y : R.Statement n)
    [DecidableEq (P.Commitment n)] :
    Option (List (Msg n ⊕ (Msg n × P.Commitment n)) ×
      (Msg n × P.Commitment n × P.Response n) ×
      List ((Msg n × P.Commitment n) × P.Challenge n)) → ℝ
  | none => 0
  | some (queries, (mf, tf, zf), finalMap) =>
    let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
    if _hj : j < q then
      let signMsgs := queries.filterMap (fun q => match q with
        | .inl m => some m | .inr _ => none)
      match assocLookup (mf, tf) finalMap with
      | some c =>
        boolToReal (P.verify n y tf c zf && !(signMsgs.contains mf))
      | none => 0
    else
      0

/-- The **ROM EUF-CMA security game** for a Fiat-Shamir signature scheme.

The game (proof-friendly ROM-EUF-CMA variant):
1. Samples a witness `w` uniformly
2. Samples lazy-sampling coins for random-oracle replies
3. Samples signing randomness `rs : Fin q → ProverRandomness`
4. Gives the adversary the statement `y = keyOf w`
5. Answers signing queries using honest Fiat-Shamir signing
6. Answers hash queries consistently via lazy sampling
7. Accepts only if:
   - the forgery verifies,
   - the message is fresh (not signed before), and
   - `(m★, t★)` was explicitly hash-queried -/
noncomputable def ROM_EUF_CMA_Game {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen) :
    SecurityGame (ROM_EUF_CMA_Adversary P Msg) where
  advantage A n :=
    let q := A.numQueries n
    uniformExpect
      ((R.Witness n × (Fin q → P.ProverRandomness n)) ×
        (Fin q → (Msg n × P.Commitment n → P.Challenge n)))
      (fun ⟨⟨w, rs⟩, Hs⟩ =>
        let y := kg.keyOf n w
        letI := P.commitmentDecEq n
        romCmaWinCondition P Msg n q y
          ((A.interact n y).runWithState q (romCmaOracle P Msg n w y rs Hs) []))

/-- A **relation solver** is an adversary that attempts to find a
witness given a statement. -/
structure RelationSolver (R : EffectiveRelation) where
  /-- Given a statement, attempt to find a witness. -/
  find : (n : ℕ) → R.Statement n → R.Witness n

/-- The **relation hardness game**: the challenger samples a witness `w`
uniformly, computes the statement `y = keyOf w`, and gives `y` to the
solver. The solver wins if it outputs a valid witness for `y`.

This is the natural-keygen specialization of Boneh-Shoup Attack
Game 19.2 where key generation is `w ←$ Witness; pk := keyOf w`. -/
noncomputable def RelationGame (R : EffectiveRelation)
    (kg : R.WithKeyGen)
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)] :
    SecurityGame (RelationSolver R) where
  advantage B n := uniformExpect (R.Witness n) (fun w =>
    boolToReal (decide (R.relation n (B.find n (kg.keyOf n w)) (kg.keyOf n w))))

end
