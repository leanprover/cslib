/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Primitives.PRG.Basic
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
public import Mathlib.Data.FinEnum

/-!
# Asymptotic pseudorandom generator security

Security for families of generators means negligible advantage for each admissible
adversary family, following [BonehShoup2023], Definition 3.1. Negligibility uses Mathlib's
`Asymptotics.SuperpolynomialDecay`. Admissibility is a predicate on the whole adversary
family, so a downstream computational model can express a uniform resource restriction.
This model has a natural-number security parameter and no sampled public system parameters.
Efficiency of generation and sampling is not asserted by these semantic definitions.

`SecureWithError` bounds every admissible family's advantage at parameter `n` by `ε n`.
A negligible bound implies `Secure`.

A non-negligible lower bound on the fraction of outputs outside the image rules out security
when the range-test family is admissible. In particular, a bitstring family that eventually
stretches by at least one bit is insecure against any class admitting its range test.
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open Filter
open scoped NNReal Topology

/-- A security-parameter-indexed collection of deterministic generators. -/
abbrev Family (Seed Output : ℕ → Type*) := ∀ n, Generator (Seed n) (Output n)

namespace Family

variable {Seed Output : ℕ → Type*}
variable [∀ n, Fintype (Seed n)] [∀ n, Nonempty (Seed n)]
variable [∀ n, Fintype (Output n)] [∀ n, Nonempty (Output n)]

/-- Every admissible adversary family has negligible distinguishing advantage.
The predicate can encode computational restrictions; `fun _ => True` permits all families. -/
def Secure (G : Family Seed Output)
    (Admissible : (∀ n, Adversary (Output n)) → Prop) : Prop :=
  ∀ adversary_family, Admissible adversary_family →
    Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ))
      (fun n => (G n).advantage (adversary_family n))

/-- Restricting the admissible adversary families preserves asymptotic security. -/
theorem Secure.of_admissible {G : Family Seed Output}
    {Admissible Restricted : (∀ n, Adversary (Output n)) → Prop}
    (h : G.Secure Admissible)
    (hsub : ∀ adversary_family, Restricted adversary_family → Admissible adversary_family) :
    G.Secure Restricted := fun adversary_family ha =>
      h adversary_family (hsub adversary_family ha)

/-- Every admissible adversary family has advantage at most `ε n` at each parameter `n`. -/
def SecureWithError (G : Family Seed Output)
    (Admissible : (∀ n, Adversary (Output n)) → Prop) (ε : ℕ → ℝ≥0) : Prop :=
  ∀ adversary_family, Admissible adversary_family →
    ∀ n, (G n).advantage (adversary_family n) ≤ ε n

/-- A negligible error bound implies asymptotic security. -/
theorem SecureWithError.secure {G : Family Seed Output}
    {Admissible : (∀ n, Adversary (Output n)) → Prop} {ε : ℕ → ℝ≥0}
    (h : G.SecureWithError Admissible ε)
    (hε : Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ))
      (fun n => (ε n : ℝ))) : G.Secure Admissible := by
  intro adversary_family ha
  apply hε.trans_abs_le
  intro n
  simpa only [abs_of_nonneg ((G n).advantage_nonneg (adversary_family n)),
    abs_of_nonneg (ε n).coe_nonneg] using h adversary_family ha n

section RangeTests

variable [∀ n, DecidableEq (Output n)]

/-- A non-negligible lower bound on the fraction of outputs outside the image rules out
security whenever exhaustive range testing is admissible. -/
theorem not_secure_of_rangeAdversary (G : Family Seed Output)
    {Admissible : (∀ n, Adversary (Output n)) → Prop}
    (ha : Admissible (fun n => (G n).rangeAdversary)) {δ : ℕ → ℝ≥0}
    (hδ : ¬ Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ))
      (fun n => (δ n : ℝ)))
    (hgap : ∀ᶠ n in atTop,
      (δ n : ℝ) ≤ 1 - Nat.card (Set.range (G n)) / (Fintype.card (Output n) : ℝ)) :
    ¬ G.Secure Admissible := by
  intro h
  apply hδ
  apply (h _ ha).trans_eventually_abs_le
  filter_upwards [hgap] with n hn
  change |(δ n : ℝ)| ≤ |(G n).advantage (G n).rangeAdversary|
  rw [abs_of_nonneg (δ n).coe_nonneg, abs_of_nonneg ((G n).advantage_nonneg _),
    Generator.advantage_rangeAdversary]
  exact hn

/-- If outputs eventually outnumber seeds by a factor of two, admissibility of exhaustive
seed enumeration and output comparison suffices to rule out security. -/
theorem not_secure_of_two_mul_card_le (G : Family Seed Output)
    {Admissible : (∀ n, Adversary (Output n)) → Prop}
    (ha : Admissible (fun n => (G n).rangeAdversary))
    (hsize : ∀ᶠ n in atTop, 2 * Fintype.card (Seed n) ≤ Fintype.card (Output n)) :
    ¬ G.Secure Admissible := by
  apply G.not_secure_of_rangeAdversary ha (δ := fun _ => 1 / 2)
  · intro h
    have hlim := h 0
    norm_num at hlim
  · filter_upwards [hsize] with n hn
    have hpos : (0 : ℝ) < Fintype.card (Output n) := by exact_mod_cast Fintype.card_pos
    have hcard : 2 * (Fintype.card (Seed n) : ℝ) ≤ Fintype.card (Output n) := by
      exact_mod_cast hn
    have hratio : Fintype.card (Seed n) / (Fintype.card (Output n) : ℝ) ≤ 1 / 2 :=
      (div_le_iff₀ hpos).mpr (by linarith)
    have hgap : (1 : ℝ) / 2 ≤ 1 - Fintype.card (Seed n) / (Fintype.card (Output n) : ℝ) :=
      by linarith
    exact hgap.trans (by simpa only [Generator.advantage_rangeAdversary] using
      (G n).one_sub_card_div_le_advantage_rangeAdversary)

end RangeTests

/-- A bitstring generator that eventually stretches by at least one bit is insecure
against any class admitting its range-test family. -/
theorem not_secure_of_bitstring_stretch {seedLength outputLength : ℕ → ℕ}
    (G : Family (fun n => Fin (seedLength n) → Bool) (fun n => Fin (outputLength n) → Bool))
    {Admissible : (∀ n, Adversary (Fin (outputLength n) → Bool)) → Prop}
    (ha : Admissible (fun n => (G n).rangeAdversary))
    (hstretch : ∀ᶠ n in atTop, seedLength n < outputLength n) :
    ¬ G.Secure Admissible := by
  apply G.not_secure_of_two_mul_card_le ha
  filter_upwards [hstretch] with n hn
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  calc
    2 * 2 ^ seedLength n = 2 ^ (seedLength n + 1) := by rw [pow_succ, mul_comm]
    _ ≤ 2 ^ outputLength n := Nat.pow_le_pow_right (by decide) hn

/-- No bitstring generator family that eventually stretches by at least one bit is secure
against all adversary families. -/
theorem not_exists_secure_bitstring_stretch {seedLength outputLength : ℕ → ℕ}
    (hstretch : ∀ᶠ n in atTop, seedLength n < outputLength n) :
    ¬ ∃ G : Family (fun n => Fin (seedLength n) → Bool)
      (fun n => Fin (outputLength n) → Bool), G.Secure (fun _ => True) := by
  rintro ⟨G, hG⟩
  exact G.not_secure_of_bitstring_stretch trivial hstretch hG

/-- A `BitVec` generator that eventually stretches by at least one bit is insecure
against any class admitting its range-test family. -/
theorem not_secure_of_bitVec_stretch {seedLength outputLength : ℕ → ℕ}
    (G : Family (fun n => BitVec (seedLength n)) (fun n => BitVec (outputLength n)))
    {Admissible : (∀ n, Adversary (BitVec (outputLength n))) → Prop}
    (ha : Admissible (fun n => (G n).rangeAdversary))
    (hstretch : ∀ᶠ n in atTop, seedLength n < outputLength n) :
    ¬ G.Secure Admissible := by
  apply G.not_secure_of_two_mul_card_le ha
  filter_upwards [hstretch] with n hn
  simp only [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  calc
    2 * 2 ^ seedLength n = 2 ^ (seedLength n + 1) := by rw [pow_succ, mul_comm]
    _ ≤ 2 ^ outputLength n := Nat.pow_le_pow_right (by decide) hn

/-- No `BitVec` generator family that eventually stretches by at least one bit is secure
against all adversary families. -/
theorem not_exists_secure_bitVec_stretch {seedLength outputLength : ℕ → ℕ}
    (hstretch : ∀ᶠ n in atTop, seedLength n < outputLength n) :
    ¬ ∃ G : Family (fun n => BitVec (seedLength n)) (fun n => BitVec (outputLength n)),
      G.Secure (fun _ => True) := by
  rintro ⟨G, hG⟩
  exact G.not_secure_of_bitVec_stretch trivial hstretch hG

end Family
end Cslib.Crypto.PRG
