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

If the range test is admissible and the seed space is eventually at most half the output
space, security is impossible: the advantage is eventually at least one half. In particular,
no family stretching bitstrings by at least one bit is secure against arbitrary adversaries.
Mere strict cardinality expansion for arbitrary finite spaces would not give this constant
gap, which is why the asymptotic theorem states the quantitative hypothesis explicitly.
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open Filter
open scoped Topology

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
  ∀ adversary, Admissible adversary →
    Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ))
      (fun n => (G n).advantage (adversary n))

/-- Restricting the admissible adversary families preserves asymptotic security. -/
theorem Secure.of_admissible {G : Family Seed Output}
    {Admissible Restricted : (∀ n, Adversary (Output n)) → Prop}
    (h : G.Secure Admissible) (hsub : ∀ adversary, Restricted adversary → Admissible adversary) :
    G.Secure Restricted := fun adversary ha => h adversary (hsub adversary ha)

/-- A constant positive lower bound on the range test's advantage rules out security. -/
theorem not_secure_of_rangeAdversary (G : Family Seed Output)
    {Admissible : (∀ n, Adversary (Output n)) → Prop}
    (ha : Admissible (fun n => (G n).rangeAdversary))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᶠ n in atTop,
      δ ≤ 1 - Fintype.card (Seed n) / (Fintype.card (Output n) : ℝ)) :
    ¬ G.Secure Admissible := by
  intro h
  have hlim : Tendsto (fun n => (G n).advantage (G n).rangeAdversary) atTop (𝓝 0) := by
    simpa using h _ ha 0
  have hle : δ ≤ 0 := ge_of_tendsto hlim (hgap.mono fun n hn =>
    hn.trans (G n).one_sub_card_div_le_advantage_rangeAdversary)
  exact hδ.not_ge hle

/-- If the output space is eventually at least twice as large as the seed space,
then security against arbitrary adversaries is impossible. -/
theorem not_secure_of_two_mul_card_le (G : Family Seed Output)
    (hsize : ∀ᶠ n in atTop, 2 * Fintype.card (Seed n) ≤ Fintype.card (Output n)) :
    ¬ G.Secure (fun _ => True) := by
  apply G.not_secure_of_rangeAdversary trivial (δ := 1 / 2) (by norm_num)
  filter_upwards [hsize] with n hn
  have hpos : (0 : ℝ) < Fintype.card (Output n) := by exact_mod_cast Fintype.card_pos
  have hcard : 2 * (Fintype.card (Seed n) : ℝ) ≤ Fintype.card (Output n) := by
    exact_mod_cast hn
  have hratio : Fintype.card (Seed n) / (Fintype.card (Output n) : ℝ) ≤ 1 / 2 :=
    (div_le_iff₀ hpos).mpr (by linarith)
  linarith

/-- No bitstring generator family stretching by at least one bit is secure against
arbitrary adversaries, even when stretching is only required eventually. -/
theorem not_secure_of_bitstring_stretch {seedLength outputLength : ℕ → ℕ}
    (G : Family (fun n => Fin (seedLength n) → Bool) (fun n => Fin (outputLength n) → Bool))
    (hstretch : ∀ᶠ n in atTop, seedLength n < outputLength n) :
    ¬ G.Secure (fun _ => True) := by
  apply G.not_secure_of_two_mul_card_le
  filter_upwards [hstretch] with n hn
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  calc
    2 * 2 ^ seedLength n = 2 ^ (seedLength n + 1) := by rw [pow_succ, mul_comm]
    _ ≤ 2 ^ outputLength n := Nat.pow_le_pow_right (by decide) hn

/-- No family that eventually stretches bitstrings is secure against arbitrary adversaries. -/
theorem not_exists_secure_bitstring_stretch {seedLength outputLength : ℕ → ℕ}
    (hstretch : ∀ᶠ n in atTop, seedLength n < outputLength n) :
    ¬ ∃ G : Family (fun n => Fin (seedLength n) → Bool)
      (fun n => Fin (outputLength n) → Bool), G.Secure (fun _ => True) := by
  rintro ⟨G, hG⟩
  exact G.not_secure_of_bitstring_stretch hstretch hG

/-- The impossibility of stretching against arbitrary adversaries, using `BitVec`. -/
theorem not_secure_of_bitVec_stretch {seedLength outputLength : ℕ → ℕ}
    (G : Family (fun n => BitVec (seedLength n)) (fun n => BitVec (outputLength n)))
    (hstretch : ∀ᶠ n in atTop, seedLength n < outputLength n) :
    ¬ G.Secure (fun _ => True) := by
  apply G.not_secure_of_two_mul_card_le
  filter_upwards [hstretch] with n hn
  simp only [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  calc
    2 * 2 ^ seedLength n = 2 ^ (seedLength n + 1) := by rw [pow_succ, mul_comm]
    _ ≤ 2 ^ outputLength n := Nat.pow_le_pow_right (by decide) hn

/-- There is no secure expanding `BitVec` generator family against arbitrary adversaries. -/
theorem not_exists_secure_bitVec_stretch {seedLength outputLength : ℕ → ℕ}
    (hstretch : ∀ᶠ n in atTop, seedLength n < outputLength n) :
    ¬ ∃ G : Family (fun n => BitVec (seedLength n)) (fun n => BitVec (outputLength n)),
      G.Secure (fun _ => True) := by
  rintro ⟨G, hG⟩
  exact G.not_secure_of_bitVec_stretch hstretch hG

end Family
end Cslib.Crypto.PRG
