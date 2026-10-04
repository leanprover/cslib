/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Negligible
public import Cslib.Probability.PMF

/-!
# Security of Boolean experiments

A `Game` is the distribution of a Boolean experiment. Its acceptance probability, distinguishing
advantage, and asymptotic security are independent of the language used to write the experiment.
`Game.Secure` restricts whole adversaries, which may themselves be families of tests. Finite
cryptographic primitives instantiate these definitions directly, and computational definitions
over infinite sample spaces can reuse them.

The advantage convention is the absolute difference of acceptance probabilities, as in
[BonehShoup2023], Section 3.1. Negligibility is Mathlib's superpolynomial decay.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal

/-- The distribution of the Boolean result of a security experiment. -/
abbrev Game := PMF Bool

namespace Game

/-- The probability that an experiment accepts. -/
noncomputable abbrev winProbability (game : Game) : ℝ := (game true).toReal

/-- The absolute difference of two experiments' acceptance probabilities. -/
noncomputable abbrev advantage (real ideal : Game) : ℝ :=
  |real.winProbability - ideal.winProbability|

/-- Distinguishing advantage is nonnegative. -/
theorem advantage_nonneg (real ideal : Game) : 0 ≤ advantage real ideal := abs_nonneg _

/-- Equal experiments have zero advantage. -/
@[simp] theorem advantage_self (game : Game) : advantage game game = 0 := by
  simp

/-- Swapping the experiments preserves advantage. -/
theorem advantage_comm (real ideal : Game) : advantage real ideal = advantage ideal real :=
  abs_sub_comm _ _

/-- Complementing a game's answer exchanges acceptance and rejection. -/
@[simp] theorem winProbability_not (game : Game) :
    winProbability (game.map Bool.not) = 1 - winProbability game := by
  rw [eq_sub_iff_add_eq', ← Probability.PMF.sum_toReal game, Fintype.sum_bool]
  simp [winProbability]

/-- Complementing both answers preserves advantage. -/
@[simp] theorem advantage_not (real ideal : Game) :
    advantage (real.map Bool.not) (ideal.map Bool.not) = advantage real ideal := by
  rw [advantage, advantage, winProbability_not, winProbability_not, sub_sub_sub_cancel_left,
    abs_sub_comm]

/-- The elementary game-hopping inequality. -/
theorem advantage_triangle (first middle last : Game) :
    advantage first last ≤ advantage first middle + advantage middle last := abs_sub_le _ _ _

/-- Distinguishing advantage is at most one. -/
theorem advantage_le_one (real ideal : Game) : advantage real ideal ≤ 1 := by
  have hle (game : Game) : winProbability game ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one game true)
  exact abs_sub_le_of_nonneg_of_le ENNReal.toReal_nonneg (hle real) ENNReal.toReal_nonneg
    (hle ideal)

/-- Comparing with certain rejection measures the probability of winning. -/
@[simp] theorem advantage_pure_false (game : Game) :
    advantage game (PMF.pure false) = winProbability game := by
  simp [advantage, winProbability]

/-- Comparing with a fair coin measures absolute prediction bias. -/
@[simp] theorem advantage_uniform_bool (game : Game) :
    advantage game (PMF.uniformOfFintype Bool) = |winProbability game - 1 / 2| := by
  simp [advantage, winProbability]

/-- Each admissible adversary has negligible advantage. The admissibility predicate applies to
the whole adversary before the security parameter is supplied, so it can constrain the adversary
across all parameters at once. -/
def Secure {Adversary : Type*} (real ideal : Adversary → ℕ → Game)
    (Admissible : Adversary → Prop) : Prop :=
  ∀ adversary, Admissible adversary →
    Negligible (fun n => advantage (real adversary n) (ideal adversary n))

/-- A common bound on the advantage of all admissible adversaries at each parameter. -/
def SecureWithError {Adversary : Type*} (real ideal : Adversary → ℕ → Game)
    (Admissible : Adversary → Prop) (ε : ℕ → ℝ≥0) : Prop :=
  ∀ adversary, Admissible adversary →
    ∀ n, advantage (real adversary n) (ideal adversary n) ≤ ε n

/-- Restricting admissibility preserves a concrete security bound. -/
theorem SecureWithError.of_admissible {Adversary : Type*}
    {real ideal : Adversary → ℕ → Game} {Admissible Restricted : Adversary → Prop}
    {ε : ℕ → ℝ≥0} (h : SecureWithError real ideal Admissible ε)
    (hsub : ∀ adversary, Restricted adversary → Admissible adversary) :
    SecureWithError real ideal Restricted ε := fun adversary ha => h adversary (hsub adversary ha)

/-- Enlarging an error budget preserves its security guarantee. -/
theorem SecureWithError.mono {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε δ : ℕ → ℝ≥0}
    (h : SecureWithError real ideal Admissible ε) (hle : ∀ n, ε n ≤ δ n) :
    SecureWithError real ideal Admissible δ :=
  fun adversary ha n => (h adversary ha n).trans (by exact_mod_cast hle n)

/-- Swapping the experiments preserves the same concrete error. -/
theorem SecureWithError.symm {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε : ℕ → ℝ≥0}
    (h : SecureWithError real ideal Admissible ε) : SecureWithError ideal real Admissible ε :=
  fun adversary ha n => (advantage_comm _ _).trans_le (h adversary ha n)

/-- Concrete security bounds add across a game hop. -/
theorem SecureWithError.trans {Adversary : Type*} {first middle last : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε δ : ℕ → ℝ≥0}
    (hfirst : SecureWithError first middle Admissible ε)
    (hlast : SecureWithError middle last Admissible δ) :
    SecureWithError first last Admissible (fun n => ε n + δ n) := fun adversary ha n =>
  (advantage_triangle _ _ _).trans (add_le_add (hfirst adversary ha n) (hlast adversary ha n))

/-- Restricting the admissible adversaries preserves security. -/
theorem Secure.of_admissible {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible Restricted : Adversary → Prop} (h : Secure real ideal Admissible)
    (hsub : ∀ adversary, Restricted adversary → Admissible adversary) :
    Secure real ideal Restricted := fun adversary ha => h adversary (hsub adversary ha)

/-- An experiment is secure relative to itself. -/
theorem Secure.refl {Adversary : Type*} (game : Adversary → ℕ → Game)
    (Admissible : Adversary → Prop) : Secure game game Admissible :=
  fun _ _ => by simp

/-- Swapping the experiments preserves security. -/
theorem Secure.symm {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} (h : Secure real ideal Admissible) :
    Secure ideal real Admissible :=
  fun adversary ha => (h adversary ha).congr fun _ => advantage_comm _ _

/-- Security composes through an intermediate experiment. -/
theorem Secure.trans {Adversary : Type*} {first middle last : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} (hfirst : Secure first middle Admissible)
    (hlast : Secure middle last Admissible) : Secure first last Admissible := fun adversary ha =>
  negligible_of_le ((hfirst adversary ha).add (hlast adversary ha))
    (fun _ => advantage_nonneg _ _) (fun _ => advantage_triangle _ _ _)

/-- A reduction preserves security when it preserves admissibility and bounds advantage. -/
theorem Secure.of_reduction {Source Target : Type*}
    {sourceReal sourceIdeal : Source → ℕ → Game} {targetReal targetIdeal : Target → ℕ → Game}
    {SourceAdmissible : Source → Prop} {TargetAdmissible : Target → Prop}
    (h : Secure sourceReal sourceIdeal SourceAdmissible) (reduce : Target → Source)
    (hadmissible : ∀ adversary, TargetAdmissible adversary → SourceAdmissible (reduce adversary))
    (hbound : ∀ adversary, TargetAdmissible adversary → ∀ n,
      advantage (targetReal adversary n) (targetIdeal adversary n) ≤
        advantage (sourceReal (reduce adversary) n) (sourceIdeal (reduce adversary) n)) :
    Secure targetReal targetIdeal TargetAdmissible := fun adversary ha =>
  negligible_of_le (h _ (hadmissible adversary ha)) (fun _ => advantage_nonneg _ _)
    (hbound adversary ha)

/-- A negligible common error bound implies asymptotic security. -/
theorem SecureWithError.secure {Adversary : Type*} {real ideal : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε : ℕ → ℝ≥0}
    (h : SecureWithError real ideal Admissible ε)
    (hε : Negligible (fun n => (ε n : ℝ))) : Secure real ideal Admissible := fun adversary ha =>
  negligible_of_le hε (fun _ => advantage_nonneg _ _) (h adversary ha)

end Game
end Cslib.Crypto
