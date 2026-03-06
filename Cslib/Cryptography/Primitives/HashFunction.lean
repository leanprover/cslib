/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.SecurityGame

@[expose] public section

/-!
# Cryptographic Hash Functions

This file defines **collision-resistant hash function families** and
their security notions.

## Main Definitions

* `HashFamily` — a keyed hash function family
* `HashFamily.CollisionResistant` — collision resistance
* `HashFamily.SecondPreimageResistant` — second preimage resistance

## Design Notes

We follow the standard keyed hash function model where a public key
(hash function description) is sampled and given to the adversary.
The adversary wins if it finds a collision.

## References

* [I. Damgård, *Collision Free Hash Functions and Public Key
  Signature Schemes*][Damgard1987]
* [P. Rogaway, T. Shrimpton, *Cryptographic Hash-Function
  Basics*][RogawayS2004]
-/

/-- A **keyed hash function family** parameterized by security level.

At each security level `n`, a key selects a specific hash function
from the family. -/
structure HashFamily where
  /-- Key (hash function description) type -/
  Key : ℕ → Type
  /-- Input (preimage) type -/
  Input : ℕ → Type
  /-- Output (digest) type -/
  Output : ℕ → Type
  /-- Key type is finite (for sampling) -/
  keyFintype : ∀ n, Fintype (Key n)
  /-- Key type is nonempty -/
  keyNonempty : ∀ n, Nonempty (Key n)
  /-- The hash function -/
  hash : (n : ℕ) → Key n → Input n → Output n

/-! ### Collision Resistance -/

/-- A **collision-finding adversary** attempts to find two distinct
inputs that hash to the same output under a given key. -/
structure HashFamily.CollisionAdversary (H : HashFamily) where
  /-- Given a key, find two inputs. The adversary wins if they are
  distinct and hash to the same value. -/
  findCollision : (n : ℕ) → H.Key n → H.Input n × H.Input n

/-- The **collision resistance game**: the adversary wins if it finds
two distinct inputs `(x₁, x₂)` with `H(k, x₁) = H(k, x₂)`.

The advantage is `E_k[1[A finds collision under key k]]`. -/
noncomputable def HashFamily.CollisionGame (H : HashFamily)
    [∀ n, DecidableEq (H.Input n)]
    [∀ n, DecidableEq (H.Output n)] :
    SecurityGame (HashFamily.CollisionAdversary H) where
  advantage A n :=
    letI := H.keyFintype n; letI := H.keyNonempty n
    Cslib.Probability.uniformExpect (H.Key n) (fun k =>
      let (x₁, x₂) := A.findCollision n k
      Cslib.Probability.boolToReal
        (decide (x₁ ≠ x₂) && decide (H.hash n k x₁ = H.hash n k x₂)))

/-- A hash family is **collision resistant** if the collision game
is secure against all adversaries. -/
def HashFamily.CollisionResistant (H : HashFamily)
    [∀ n, DecidableEq (H.Input n)]
    [∀ n, DecidableEq (H.Output n)] : Prop :=
  H.CollisionGame.Secure

/-- A hash family is **collision resistant against** a class of
adversaries. -/
def HashFamily.CollisionResistantAgainst (H : HashFamily)
    [∀ n, DecidableEq (H.Input n)]
    [∀ n, DecidableEq (H.Output n)]
    (Admissible : HashFamily.CollisionAdversary H → Prop) : Prop :=
  H.CollisionGame.SecureAgainst Admissible

/-! ### Second Preimage Resistance -/

/-- A **second-preimage adversary** is given a key and an input `x₁`,
and must find a different input `x₂` with the same hash value. -/
structure HashFamily.SecondPreimageAdversary (H : HashFamily) where
  /-- Given a key and an input, find another input with the same hash -/
  findSecondPreimage : (n : ℕ) → H.Key n → H.Input n → H.Input n

/-- The **second preimage resistance game**: the adversary is given a
random key `k` and a random input `x₁`, and must find `x₂ ≠ x₁` with
`H(k, x₁) = H(k, x₂)`.

The advantage is `E_{k,x₁}[1[x₁ ≠ x₂ ∧ H(k,x₁) = H(k,x₂)]]`. -/
noncomputable def HashFamily.SecondPreimageGame (H : HashFamily)
    [∀ n, Fintype (H.Input n)] [∀ n, Nonempty (H.Input n)]
    [∀ n, DecidableEq (H.Input n)]
    [∀ n, DecidableEq (H.Output n)] :
    SecurityGame (HashFamily.SecondPreimageAdversary H) where
  advantage A n :=
    letI := H.keyFintype n; letI := H.keyNonempty n
    Cslib.Probability.uniformExpect (H.Key n × H.Input n) (fun ⟨k, x₁⟩ =>
      let x₂ := A.findSecondPreimage n k x₁
      Cslib.Probability.boolToReal
        (decide (x₁ ≠ x₂) && decide (H.hash n k x₁ = H.hash n k x₂)))

/-- A hash family is **second preimage resistant** if the second preimage
game is secure against all adversaries. -/
def HashFamily.SecondPreimageResistant (H : HashFamily)
    [∀ n, Fintype (H.Input n)] [∀ n, Nonempty (H.Input n)]
    [∀ n, DecidableEq (H.Input n)]
    [∀ n, DecidableEq (H.Output n)] : Prop :=
  H.SecondPreimageGame.Secure

/-- A hash family is **second preimage resistant against** a class of
adversaries. -/
def HashFamily.SecondPreimageResistantAgainst (H : HashFamily)
    [∀ n, Fintype (H.Input n)] [∀ n, Nonempty (H.Input n)]
    [∀ n, DecidableEq (H.Input n)]
    [∀ n, DecidableEq (H.Output n)]
    (Admissible : HashFamily.SecondPreimageAdversary H → Prop) : Prop :=
  H.SecondPreimageGame.SecureAgainst Admissible

/-! ### Collision Resistance implies Second Preimage Resistance -/

open Cslib.Probability in
/-- **Collision resistance implies second preimage resistance.**

Given a second-preimage adversary `A`, we construct a collision-finding
adversary `B` such that `B(k) = (x₁*(k), A(k, x₁*(k)))` where
`x₁*(k)` is the input that maximizes `A`'s success probability for
key `k`.

By the averaging principle (`uniformExpect_le_exists`), the CR
advantage of `B` is at least the SPR advantage of `A`. -/
theorem HashFamily.collisionResistant_imp_secondPreimageResistant
    (H : HashFamily)
    [∀ n, Fintype (H.Input n)] [∀ n, Nonempty (H.Input n)]
    [∀ n, DecidableEq (H.Input n)]
    [∀ n, DecidableEq (H.Output n)]
    (hCR : H.CollisionResistant) :
    H.SecondPreimageResistant := by
  intro A
  -- SPR indicator function
  let ind (n : ℕ) (k : H.Key n) (x₁ : H.Input n) : ℝ :=
    boolToReal (decide (x₁ ≠ A.findSecondPreimage n k x₁) &&
      decide (H.hash n k x₁ = H.hash n k (A.findSecondPreimage n k x₁)))
  -- For each (n, k), averaging gives us the best x₁
  have h_avg : ∀ n (k : H.Key n), ∃ x₁ : H.Input n,
      uniformExpect (H.Input n) (ind n k) ≤ ind n k x₁ :=
    fun n k => uniformExpect_le_exists (H.Input n) (ind n k)
  -- Build collision adversary: for each (n,k), use the best x₁
  let B : HashFamily.CollisionAdversary H :=
    ⟨fun n k =>
      let x₁ := (h_avg n k).choose
      (x₁, A.findSecondPreimage n k x₁)⟩
  -- CR gives negligibility of B's advantage
  apply Negligible.mono (hCR B)
  refine ⟨0, fun n _ => ?_⟩
  letI := H.keyFintype n; letI := H.keyNonempty n
  -- Both advantages are nonneg
  have h_spr_nonneg : 0 ≤ H.SecondPreimageGame.advantage A n := by
    simp only [SecondPreimageGame]
    exact uniformExpect_nonneg _ fun _ => boolToReal_nonneg _
  have h_cr_nonneg : 0 ≤ H.CollisionGame.advantage B n := by
    simp only [CollisionGame]
    exact uniformExpect_nonneg _ fun _ => boolToReal_nonneg _
  rw [abs_of_nonneg h_spr_nonneg, abs_of_nonneg h_cr_nonneg]
  -- SPR adv = E_{k,x₁}[ind] = E_k[E_{x₁}[ind]] ≤ E_k[ind(k,x₁*(k))] = CR adv
  simp only [SecondPreimageGame, CollisionGame]
  rw [uniformExpect_prod]
  -- Pointwise monotonicity
  unfold uniformExpect
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  -- B.findCollision unfolds to (x₁_best, A(k, x₁_best))
  change uniformExpect (H.Input n) (ind n k) ≤
    ind n k (h_avg n k).choose
  exact (h_avg n k).choose_spec

end
