/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.SecurityGame

@[expose] public section

/-!
# One-Way Functions

This file defines **one-way functions (OWFs)** — the minimal
cryptographic assumption from which most of modern cryptography can
be built.

A function is one-way if it is:
1. **Efficiently computable** — can be evaluated in polynomial time
2. **Hard to invert** — no efficient algorithm can find a preimage
   with non-negligible probability

## Main Definitions

* `OWF` — a one-way function family
* `OWF.Secure` — information-theoretic security (all adversaries)
* `OWF.SecureAgainst` — computational security (efficient adversaries only)
* `OWP` — a one-way permutation (bijective OWF)

## Design Notes

We model one-way functions as families indexed by the security parameter,
following the standard asymptotic treatment. The inversion game is a
search game where the adversary's advantage is `Pr[A inverts f on
random input]`.

## References

* [O. Goldreich, *Foundations of Cryptography, Vol. 1*][Goldreich2001]
* [S. Goldwasser, S. Micali, *Probabilistic Encryption*][GoldwasserM1984]
-/

/-- A **one-way function family** indexed by the security parameter.

At each security level `n`, `f n` maps `Domain n` to `Range n`.
The function should be hard to invert (captured by `Secure` /
`SecureAgainst`). -/
structure OWF where
  /-- Input domain at security level n -/
  Domain : ℕ → Type
  /-- Output range at security level n -/
  Range : ℕ → Type
  /-- Domain is finite (for sampling) -/
  domainFintype : ∀ n, Fintype (Domain n)
  /-- Domain is nonempty (for sampling) -/
  domainNonempty : ∀ n, Nonempty (Domain n)
  /-- Range has decidable equality (for checking inversion) -/
  rangeDecEq : ∀ n, DecidableEq (Range n)
  /-- The one-way function -/
  f : (n : ℕ) → Domain n → Range n

/-- An **inversion adversary** for a one-way function: given the security
parameter and a value `y` in the range, attempts to find `x` such that
`f(x) = y`. -/
structure OWF.InversionAdversary (F : OWF) where
  /-- The inversion algorithm: given n and y = f(x), find some x'. -/
  invert : (n : ℕ) → F.Range n → F.Domain n

/-- A one-way function is **secure** if for every inversion adversary,
the probability of successful inversion is negligible.

The advantage is `Pr_{x ← Domain n}[f(A.invert(f(x))) = f(x)]`, computed
as a uniform expectation over the domain using the coin-passing style. -/
noncomputable def OWF.InversionGame (F : OWF) : SecurityGame (OWF.InversionAdversary F) :=
  letI (n : ℕ) := F.domainFintype n
  letI (n : ℕ) := F.domainNonempty n
  letI (n : ℕ) := F.rangeDecEq n
  SecurityGame.ofCoinGame F.Domain
    (fun A n x => Cslib.Probability.boolToReal (decide (F.f n (A.invert n (F.f n x)) = F.f n x)))

/-- A one-way function is **(information-theoretically) secure** if the
inversion game is secure against all adversaries. -/
def OWF.Secure (F : OWF) : Prop := F.InversionGame.Secure

/-- A one-way function is **computationally secure** against a class of
adversaries defined by `Admissible`. The standard instantiation uses
poly-time adversaries. -/
def OWF.SecureAgainst (F : OWF)
    (Admissible : OWF.InversionAdversary F → Prop) : Prop :=
  F.InversionGame.SecureAgainst Admissible

/-- A **one-way permutation** is a one-way function that is a bijection
at every security level. -/
structure OWP extends OWF where
  /-- The function is a bijection at every security level -/
  bij : ∀ n, Function.Bijective (toOWF.f n)

end

/-! ### Basic properties -/

/-- A one-way permutation is a one-way function. -/
def OWP.toSecure (P : OWP) (h : P.toOWF.Secure) : P.toOWF.Secure := h

/-- Information-theoretic security implies computational security
against any class of adversaries. -/
theorem OWF.Secure.toSecureAgainst {F : OWF} (h : F.Secure)
    (Admissible : OWF.InversionAdversary F → Prop) :
    F.SecureAgainst Admissible := by
  intro A _
  exact h A
