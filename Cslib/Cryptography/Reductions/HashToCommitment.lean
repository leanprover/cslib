/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Primitives.HashFunction
public import Cslib.Cryptography.Primitives.Commitment

@[expose] public section

/-!
# Hash Function → Keyed Commitment Scheme Reduction

This file constructs a keyed commitment scheme from any keyed hash
function family and proves that collision resistance of the hash
function implies the binding property of the commitment scheme.

## Construction

Given a hash family `H`, the keyed commitment scheme is:
- `CommitKey n = H.Key n` (hash function key, sampled by challenger)
- `commit(ck, m) = (H(ck, m), m)` — commitment is the hash
- `verify(ck, c, m, _) = (H(ck, m) == c)` — verify by re-hashing

## Main Results

* `HashFamily.toKeyedCommitmentScheme` — the construction
* `HashFamily.toKeyedCommitmentScheme_correct` — correctness
* `HashFamily.collisionResistant_imp_keyedBinding` — CR → Binding

## Key insight

The binding game advantage equals the collision game advantage by
construction — a binding adversary that opens a commitment to two
different messages directly yields a collision.

## References

* [O. Goldreich, *Foundations of Cryptography, Vol. 1*][Goldreich2001]
-/

open Cslib.Probability

/-- The hash-based keyed commitment scheme: `commit(ck, m) = (H(ck, m), m)`.

The hash key `ck` is the commitment key, sampled by the challenger and
given to both the committer and verifier. -/
def HashFamily.toKeyedCommitmentScheme (H : HashFamily)
    [∀ n, DecidableEq (H.Output n)]
    : KeyedCommitmentScheme where
  CommitKey := H.Key
  Message := H.Input
  Commitment := H.Output
  Opening := H.Input
  Randomness := fun _ => Unit
  commitKeyFintype := H.keyFintype
  commitKeyNonempty := H.keyNonempty
  randomnessFintype := fun _ => inferInstance
  randomnessNonempty := fun _ => inferInstance
  commit n ck m _ := (H.hash n ck m, m)
  verify n ck c m _opening := decide (H.hash n ck m = c)

/-- The hash-based keyed commitment scheme is correct. -/
theorem HashFamily.toKeyedCommitmentScheme_correct (H : HashFamily)
    [∀ n, DecidableEq (H.Output n)] :
    H.toKeyedCommitmentScheme.Correct := by
  intro n ck m r
  simp [toKeyedCommitmentScheme]

/-- **Collision resistance implies keyed binding** for the hash-based
commitment scheme.

A keyed binding adversary receives a random key `ck` and produces
`(c, m₁, o₁, m₂, o₂)` with `m₁ ≠ m₂` and both verify. Since
verification checks `H(ck, m) = c`, both messages hash to the same
value — directly yielding a collision for key `ck`. -/
theorem HashFamily.collisionResistant_imp_keyedBinding (H : HashFamily)
    [instDI : ∀ n, DecidableEq (H.Input n)]
    [∀ n, DecidableEq (H.Output n)] :
    H.CollisionResistant →
    (@KeyedCommitmentScheme.Binding H.toKeyedCommitmentScheme instDI) := by
  intro hCR A
  -- Build a collision-finding adversary from the binding adversary
  let B : HashFamily.CollisionAdversary H :=
    ⟨fun n k =>
      let (_, m₁, _, m₂, _) := A.forge n k
      (m₁, m₂)⟩
  apply Negligible.mono (hCR B)
  refine ⟨0, fun n _ => ?_⟩
  letI := H.keyFintype n; letI := H.keyNonempty n
  -- Show: binding advantage ≤ |collision advantage|
  -- Both advantages are expectations over H.Key n
  simp only [KeyedCommitmentScheme.BindingGame, HashFamily.CollisionGame,
    toKeyedCommitmentScheme]
  rw [abs_of_nonneg (uniformExpect_nonneg _ fun _ => boolToReal_nonneg _),
      abs_of_nonneg (uniformExpect_nonneg _ fun _ => boolToReal_nonneg _)]
  -- Pointwise: binding indicator ≤ collision indicator
  unfold uniformExpect
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  -- For each k: if binding succeeds, then collision succeeds
  -- binding indicator: m₁ ≠ m₂ ∧ H(k,m₁)=c ∧ H(k,m₂)=c
  -- collision indicator: m₁ ≠ m₂ ∧ H(k,m₁) = H(k,m₂)
  simp only [B, boolToReal, Bool.and_eq_true, decide_eq_true_eq]
  split
  · rename_i hbind
    split
    · norm_num
    · rename_i hcoll; exfalso; apply hcoll
      exact ⟨hbind.1.1, hbind.1.2.trans hbind.2.symm⟩
  · split <;> norm_num

end
