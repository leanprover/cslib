/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.Negligible
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
# Computational and Statistical Indistinguishability

This file defines the core notions of indistinguishability that underpin
cryptographic security: **statistical distance** and **computational
indistinguishability** of probability ensembles.

An ensemble is a family of distributions indexed by the security parameter,
where the outcome type may depend on the parameter (`α : ℕ → Type*`).
Two ensembles are computationally indistinguishable if no admissible bounded
distinguisher can tell them apart with non-negligible advantage.

## Main Definitions

* `Ensemble` — a family of distributions indexed by security parameter
* `Distinguisher` — a family of distinguishing functions
* `Distinguisher.IsBounded` — distinguisher outputs in `[0, 1]`
* `DistinguishingAdvantage` — the advantage of a distinguisher
* `CompIndistinguishable` — computational indistinguishability (parametric in admissibility)
* `StatIndistinguishable` — statistical indistinguishability
* `PerfectlyIndistinguishable` — perfect indistinguishability

## Design Notes

The outcome type `α : ℕ → Type*` depends on the security parameter. This is
essential for poly-time restrictions to be meaningful: with a fixed finite type,
every function is trivially computable by lookup table.

`CompIndistinguishable` takes an `Admissible : Distinguisher α → Prop` parameter:
- `fun _ => True` recovers the information-theoretic setting (all bounded D)
- `IsPolyTimeDistinguisher` (defined in `PolyTimeDistinguisher.lean`) gives PPT

## References

* [O. Goldreich, *Foundations of Cryptography, Vol. 1*][Goldreich2001]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

/-- A **probability ensemble** over a parameter-dependent type `α` is a family
of probability distributions indexed by the security parameter `n : ℕ`.

For each `n`, `ens n a` gives the probability of outcome `a : α n`. -/
def Ensemble (α : ℕ → Type*) := (n : ℕ) → α n → ℝ

/-- A **distinguisher** for ensembles over `α` is a (possibly randomized)
algorithm that, given the security parameter and a sample, outputs a
decision bit. We model the distinguishing probability as a real-valued
function: `D n a` is the probability that `D` outputs 1 on input
`(n, a)`. -/
def Distinguisher (α : ℕ → Type*) := (n : ℕ) → α n → ℝ

variable {α : ℕ → Type*}

/-- A distinguisher is **bounded** if its output is in `[0, 1]` for all
inputs. This models the probability of outputting 1, and implies
`|D n a| ≤ 1`. -/
def Distinguisher.IsBounded (D : Distinguisher α) : Prop :=
  ∀ n (a : α n), 0 ≤ D n a ∧ D n a ≤ 1

/-- The **distinguishing advantage** of distinguisher `D` between
ensembles `X` and `Y` at security parameter `n`:
$$\mathsf{Adv}(D, n) = \left| \sum_a X(n, a) \cdot D(n, a) -
  \sum_a Y(n, a) \cdot D(n, a) \right|$$

In the standard formulation, this is
`|Pr[D(X_n) = 1] - Pr[D(Y_n) = 1]|`. -/
noncomputable def DistinguishingAdvantage
    [∀ n, Fintype (α n)] (D : Distinguisher α) (X Y : Ensemble α) (n : ℕ) : ℝ :=
  |∑ a : α n, X n a * D n a - ∑ a : α n, Y n a * D n a|

/-- Two ensembles `X` and `Y` are **computationally indistinguishable**
with respect to an admissibility predicate `Admissible` if no bounded,
admissible distinguisher has non-negligible advantage.

Instantiations:
- `CompIndistinguishable (fun _ => True) X Y` — all bounded distinguishers
- `CompIndistinguishable IsPolyTimeDistinguisher X Y` — PPT distinguishers -/
def CompIndistinguishable
    [∀ n, Fintype (α n)]
    (Admissible : Distinguisher α → Prop)
    (X Y : Ensemble α) : Prop :=
  ∀ D : Distinguisher α, D.IsBounded → Admissible D →
    Negligible (fun n => DistinguishingAdvantage D X Y n)

/-- Two ensembles are **statistically indistinguishable** if the
statistical distance between them is negligible. -/
noncomputable def StatisticalDistance
    [∀ n, Fintype (α n)] (X Y : Ensemble α) (n : ℕ) : ℝ :=
  (1 / 2) * ∑ a : α n, |X n a - Y n a|

def StatIndistinguishable
    [∀ n, Fintype (α n)] (X Y : Ensemble α) : Prop :=
  Negligible (fun n => StatisticalDistance X Y n)

/-- Two ensembles are **perfectly indistinguishable** if they are
identical for all security parameters. -/
def PerfectlyIndistinguishable
    (X Y : Ensemble α) : Prop :=
  ∀ n (a : α n), X n a = Y n a

end

variable {α : ℕ → Type*} [∀ n, Fintype (α n)]

/-! ### Basic relationships -/

/-- Perfect indistinguishability implies statistical indistinguishability. -/
theorem PerfectlyIndistinguishable.stat
    {X Y : Ensemble α}
    (h : PerfectlyIndistinguishable X Y) :
    StatIndistinguishable X Y := by
  unfold StatIndistinguishable
  suffices h0 : (fun n => StatisticalDistance X Y n) = fun _ => 0 by
    rw [h0]; exact Negligible.zero
  ext n
  unfold StatisticalDistance
  have : ∀ a : α n, X n a - Y n a = 0 := fun a => sub_eq_zero.mpr (h n a)
  simp only [this, abs_zero, Finset.sum_const_zero, mul_zero]

/-- Statistical indistinguishability implies computational
indistinguishability for any admissibility predicate.

The standard proof bounds `|∑(X-Y)·D| ≤ ∑|X-Y|·|D| ≤ ∑|X-Y|`
when `D` is bounded (outputs in `[0,1]`), giving
`Adv(D) ≤ 2 · StatisticalDistance`. -/
theorem StatIndistinguishable.comp
    {X Y : Ensemble α}
    (h : StatIndistinguishable X Y)
    (Admissible : Distinguisher α → Prop) :
    CompIndistinguishable Admissible X Y := by
  intro D hBound _
  -- Key lemma: Adv(D, n) ≤ ∑ |X - Y| for bounded D
  have h_adv_le : ∀ n, DistinguishingAdvantage D X Y n ≤
      ∑ a : α n, |X n a - Y n a| := by
    intro n
    unfold DistinguishingAdvantage
    rw [← Finset.sum_sub_distrib]
    calc |∑ a : α n, (X n a * D n a - Y n a * D n a)|
        ≤ ∑ a : α n, |X n a * D n a - Y n a * D n a| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a : α n, |X n a - Y n a| * |D n a| := by
          congr 1; ext a; rw [← sub_mul, abs_mul]
      _ ≤ ∑ a : α n, |X n a - Y n a| * 1 := by
          apply Finset.sum_le_sum; intro a _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_le]; exact ⟨by linarith [(hBound n a).1], (hBound n a).2⟩
      _ = ∑ a : α n, |X n a - Y n a| := by simp [mul_one]
  -- ∑ |X - Y| = 2 · SD = SD + SD
  have h_sum_eq : ∀ n, ∑ a : α n, |X n a - Y n a| =
      StatisticalDistance X Y n + StatisticalDistance X Y n := by
    intro n; unfold StatisticalDistance; ring
  -- SD + SD is negligible
  apply Negligible.mono (Negligible.add h h)
  refine ⟨0, fun n _ => ?_⟩
  -- |Adv(D,n)| = Adv(D,n) since Adv is already an absolute value
  have h_adv_nn : 0 ≤ DistinguishingAdvantage D X Y n := by
    unfold DistinguishingAdvantage; exact abs_nonneg _
  rw [abs_of_nonneg h_adv_nn]
  -- |SD + SD| = SD + SD since SD is non-negative
  have h_sd_nn : 0 ≤ StatisticalDistance X Y n := by
    unfold StatisticalDistance
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun a _ => abs_nonneg _))
  rw [abs_of_nonneg (by linarith)]
  calc DistinguishingAdvantage D X Y n
      ≤ ∑ a : α n, |X n a - Y n a| := h_adv_le n
    _ = StatisticalDistance X Y n + StatisticalDistance X Y n := h_sum_eq n

/-! ### Transitivity -/

/-- Computational indistinguishability is reflexive. -/
theorem CompIndistinguishable.refl
    (Admissible : Distinguisher α → Prop)
    (X : Ensemble α) :
    CompIndistinguishable Admissible X X := by
  intro D _ _
  suffices h : (fun n => DistinguishingAdvantage D X X n) = fun _ => 0 by
    rw [h]; exact Negligible.zero
  ext n
  simp [DistinguishingAdvantage]

/-- Computational indistinguishability is symmetric. -/
theorem CompIndistinguishable.symm
    {Admissible : Distinguisher α → Prop}
    {X Y : Ensemble α}
    (h : CompIndistinguishable Admissible X Y) :
    CompIndistinguishable Admissible Y X := by
  intro D hB hA
  have hD := h D hB hA
  intro c hc
  obtain ⟨N, hN⟩ := hD c hc
  refine ⟨N, fun n hn => ?_⟩
  have h' := hN n hn
  dsimp only [] at h' ⊢
  simp only [DistinguishingAdvantage, abs_abs] at h' ⊢
  rwa [abs_sub_comm]

/-- Computational indistinguishability is transitive (the **hybrid
argument**).

If `X ≈_c Y` and `Y ≈_c Z`, then for any distinguisher `D`, the
advantages against `(X, Y)` and `(Y, Z)` are both negligible, and the
advantage against `(X, Z)` is bounded by their sum, hence negligible. -/
theorem CompIndistinguishable.trans
    {Admissible : Distinguisher α → Prop}
    {X Y Z : Ensemble α}
    (hXY : CompIndistinguishable Admissible X Y)
    (hYZ : CompIndistinguishable Admissible Y Z) :
    CompIndistinguishable Admissible X Z := by
  intro D hB hA
  have hXY' := hXY D hB hA
  have hYZ' := hYZ D hB hA
  -- Sum of negligible advantages is negligible
  have hsum := Negligible.add hXY' hYZ'
  intro c hc
  obtain ⟨N, hN⟩ := hsum c hc
  refine ⟨N, fun n hn => ?_⟩
  have h_bound := hN n hn
  dsimp only [] at h_bound ⊢
  -- Triangle inequality: Adv(D,X,Z) ≤ Adv(D,X,Y) + Adv(D,Y,Z)
  have h_tri : DistinguishingAdvantage D X Z n ≤
      DistinguishingAdvantage D X Y n +
      DistinguishingAdvantage D Y Z n := by
    unfold DistinguishingAdvantage
    have : ∑ a : α n, X n a * D n a - ∑ a : α n, Z n a * D n a =
        (∑ a : α n, X n a * D n a - ∑ a : α n, Y n a * D n a) +
        (∑ a : α n, Y n a * D n a - ∑ a : α n, Z n a * D n a) := by
      ring
    rw [this]; exact abs_add_le _ _
  -- Adv is non-negative (it's an absolute value)
  have h_nn : 0 ≤ DistinguishingAdvantage D X Z n := by
    unfold DistinguishingAdvantage; exact abs_nonneg _
  rw [abs_of_nonneg h_nn]
  exact lt_of_le_of_lt
    (le_trans h_tri (le_abs_self _)) h_bound

/-! ### PMF-backed ensembles -/

/-- A **PMF ensemble** is a family of probability mass functions indexed by
the security parameter. Unlike `Ensemble` (which is just `ℕ → α n → ℝ`),
a `PMFEnsemble` carries Mathlib's `PMF` structure guaranteeing that
probabilities are non-negative and sum to 1.

This type bridges Mathlib's probability library to the cryptographic
indistinguishability framework. -/
def PMFEnsemble (α : ℕ → Type*) := (n : ℕ) → PMF (α n)

variable {α : ℕ → Type*}

/-- Convert a `PMFEnsemble` to an `Ensemble` by extracting real-valued
probabilities via `ENNReal.toReal`. -/
noncomputable def PMFEnsemble.toEnsemble (E : PMFEnsemble α) : Ensemble α :=
  fun n a => (E n a).toReal

/-- The **uniform PMF ensemble**: at each security parameter, the
distribution is uniform over the finite type. -/
noncomputable def PMFEnsemble.uniform
    [∀ n, Fintype (α n)] [∀ n, Nonempty (α n)] : PMFEnsemble α :=
  fun n => PMF.uniformOfFintype (α n)

/-- The ensemble derived from a PMF ensemble has non-negative values. -/
theorem PMFEnsemble.toEnsemble_nonneg (E : PMFEnsemble α) :
    ∀ n (a : α n), 0 ≤ E.toEnsemble n a := by
  intro n a
  exact ENNReal.toReal_nonneg
