/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.Negligible
public import Cslib.Probability.Discrete

@[expose] public section

/-!
# Security Games

This file provides the abstract framework for **game-based security
definitions**, the dominant paradigm in modern cryptography.

A security game formalizes the interaction between a **challenger** (the
cryptographic scheme) and an **adversary** (the attacker). The adversary's
goal is to win the game; the scheme is secure if every efficient adversary
wins with probability negligibly close to some baseline (often 1/2).

## Main Definitions

* `SecurityGame` — an abstract security game parameterized by adversary type
* `Secure` — a scheme is secure if every adversary has negligible advantage
* `SecurityReduction` — a reduction from one game to another

## Design Notes

We parametrize games by an abstract adversary type `Adv` and define
the advantage function `ℕ → ℝ` mapping security parameter to winning
probability minus baseline. This allows both:
- **Decision games** (e.g., IND-CPA): adversary tries to distinguish,
  baseline is 1/2
- **Search games** (e.g., OWF inversion): adversary tries to find a
  value, baseline is 0

## References

* [M. Bellare, P. Rogaway, *The Security of Triple Encryption and a
  Framework for Code-Based Game-Playing Proofs*][BellareR2006]
* [V. Shoup, *Sequences of Games: A Tool for Taming Complexity in
  Security Proofs*][Shoup2004]
-/

/-- A **security game** captures the interaction between a cryptographic
scheme and an adversary. The game is parameterized by:
- `Adv` — the type of adversaries
- `advantage` — maps (adversary, security parameter) to the adversary's advantage,
  i.e., `|Pr[adversary wins] - baseline|` -/
structure SecurityGame (Adv : Type*) where
  /-- The advantage of adversary `A` at security parameter `n`. -/
  advantage : Adv → ℕ → ℝ

open Cslib.Probability in
/-- Construct a `SecurityGame` from a **coin-passing game**.

The advantage of adversary `A` at security parameter `n` is the expected
value of `play A n c` when `c` is drawn uniformly from `Coins n`.

This captures the standard pattern for search games (e.g., OWF inversion)
where a single uniform sample is drawn and the adversary's success
probability is the expectation over that sample. -/
noncomputable def SecurityGame.ofCoinGame
    {Adv : Type*}
    (Coins : ℕ → Type) [∀ n, Fintype (Coins n)] [∀ n, Nonempty (Coins n)]
    (play : Adv → (n : ℕ) → Coins n → ℝ) :
    SecurityGame Adv where
  advantage A n := uniformExpect (Coins n) (play A n)

/-- A security game is **(information-theoretically) secure** if every
adversary has negligible advantage.

This is the strongest notion: it quantifies over *all* adversaries,
including computationally unbounded ones. For computational security
(the standard cryptographic notion), use `SecureAgainst` with an
efficiency predicate. -/
def SecurityGame.Secure (G : SecurityGame Adv) : Prop :=
  ∀ A : Adv, Negligible (G.advantage A)

/-- A security game is **secure against** a class of adversaries defined
by the predicate `Admissible` if every admissible adversary has negligible
advantage.

This is the standard cryptographic notion: no *efficient* adversary can
win the game with non-negligible probability beyond the baseline.

Instantiations:
- `G.SecureAgainst (fun _ => True)` — information-theoretic security (= `G.Secure`)
- `G.SecureAgainst IsEfficient` — computational security against poly-time adversaries -/
def SecurityGame.SecureAgainst (G : SecurityGame Adv)
    (Admissible : Adv → Prop) : Prop :=
  ∀ A : Adv, Admissible A → Negligible (G.advantage A)

/-- A **security reduction** from game `G₁` to game `G₂` is a
transformation of adversaries such that any adversary against `G₁`
can be turned into an adversary against `G₂` with comparable advantage.

Specifically, `R A` is the reduction of adversary `A`, and the advantage
of `A` against `G₁` is bounded by a polynomial factor times the
advantage of `R A` against `G₂`. -/
structure SecurityReduction (G₁ : SecurityGame Adv₁)
    (G₂ : SecurityGame Adv₂) where
  /-- The reduction maps adversaries for `G₁` to adversaries for `G₂`. -/
  reduce : Adv₁ → Adv₂
  /-- The advantage of `A` against `G₁` is bounded by the advantage
  of `reduce A` against `G₂` plus a negligible term. -/
  advantage_bound : ∀ A,
    Negligible (fun n => G₁.advantage A n - G₂.advantage (reduce A) n)

end

/-! ### Security reductions transfer security -/

/-- If there is a security reduction from `G₁` to `G₂` and `G₂` is
secure, then `G₁` is secure.

This is the fundamental theorem of game-based cryptography: security
of the target game transfers through the reduction. -/
theorem SecurityReduction.secure_transfer
    {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    (R : SecurityReduction G₁ G₂)
    (h : G₂.Secure) :
    G₁.Secure := by
  intro A
  have hbound := R.advantage_bound A
  have hG₂ := h (R.reduce A)
  -- G₁.advantage A n
  --   = (G₁.adv - G₂.adv) + G₂.adv; both terms are negligible
  have : Negligible (fun n =>
      (G₁.advantage A n - G₂.advantage (R.reduce A) n) +
      G₂.advantage (R.reduce A) n) :=
    Negligible.add hbound hG₂
  intro c hc
  obtain ⟨N, hN⟩ := this c hc
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  simp only [sub_add_cancel] at this
  exact this

/-- `Secure` implies `SecureAgainst` for any admissibility predicate. -/
theorem SecurityGame.Secure.secureAgainst
    {G : SecurityGame Adv} (h : G.Secure)
    (Admissible : Adv → Prop) :
    G.SecureAgainst Admissible := by
  intro A _
  exact h A

/-- A reduction from `G₁` to `G₂` transfers `SecureAgainst` when the
reduction maps admissible adversaries to admissible adversaries. -/
theorem SecurityReduction.secure_against_transfer
    {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    (R : SecurityReduction G₁ G₂)
    {P₁ : Adv₁ → Prop} {P₂ : Adv₂ → Prop}
    (hP : ∀ A, P₁ A → P₂ (R.reduce A))
    (h : G₂.SecureAgainst P₂) :
    G₁.SecureAgainst P₁ := by
  intro A hA
  have hbound := R.advantage_bound A
  have hG₂ := h (R.reduce A) (hP A hA)
  have : Negligible (fun n =>
      (G₁.advantage A n - G₂.advantage (R.reduce A) n) +
      G₂.advantage (R.reduce A) n) :=
    Negligible.add hbound hG₂
  intro c hc
  obtain ⟨N, hN⟩ := this c hc
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  simp only [sub_add_cancel] at this
  exact this

/-! ### Game composition -/

/-- The **trivial game** where every adversary has zero advantage. -/
def SecurityGame.trivial : SecurityGame Adv where
  advantage _ _ := 0

/-- The trivial game is secure. -/
theorem SecurityGame.trivial_secure : (SecurityGame.trivial : SecurityGame Adv).Secure := by
  intro A
  exact Negligible.zero
