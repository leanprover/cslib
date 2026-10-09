/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Primitives.PRG.Defs
public import Cslib.Probability.PMF

/-!
# Pseudorandom generators against arbitrary adversaries

The range-membership test accepts every generated output, whereas it accepts a uniform
output with probability `|range G| / |Output|`. Its advantage is therefore at least
`1 - |Seed| / |Output|`. This proves that an expanding generator cannot have zero
advantage against arbitrary adversaries, and gives a quantitative obstruction for
every smaller error bound. No injectivity assumption on the generator is needed.
-/

@[expose] public section

namespace Cslib.Crypto.PRG.Generator

open Cslib.Probability.PMF
open scoped NNReal

variable {Seed Output : Type*}

variable [Fintype Seed] [Nonempty Seed] [Fintype Output] [Nonempty Output]

/-- Advantage is nonnegative. -/
theorem advantage_nonneg (G : Generator Seed Output) (adversary : Adversary Output) :
    0 ≤ G.advantage adversary := abs_nonneg _

/-- Advantage is at most one, with the normalization of Attack Game 3.1. -/
theorem advantage_le_one (G : Generator Seed Output) (adversary : Adversary Output) :
    G.advantage adversary ≤ 1 := by
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top
    (PMF.coe_le_one (G.realExperiment adversary) true)
  have hideal := ENNReal.toReal_mono ENNReal.one_ne_top
    (PMF.coe_le_one (idealExperiment adversary) true)
  simp only [ENNReal.toReal_one] at hreal hideal
  apply abs_sub_le_iff.mpr
  constructor
  · linarith [@ENNReal.toReal_nonneg (idealExperiment adversary true)]
  · linarith [@ENNReal.toReal_nonneg (G.realExperiment adversary true)]

/-- Error one imposes no restriction on a generator. -/
theorem secure_one (G : Generator Seed Output) (Admissible : Adversary Output → Prop) :
    G.Secure Admissible 1 := fun adversary _ => G.advantage_le_one adversary

/-- A test whose output distribution is independent of its input has zero advantage. -/
@[simp]
theorem advantage_const (G : Generator Seed Output) (p : PMF Bool) :
    G.advantage (fun _ => p) = 0 := by
  simp [advantage, realExperiment, idealExperiment, PMF.bind_const]

/-- A generator with exactly uniform output is secure with zero error against any tests. -/
theorem secure_zero_of_outputDist_eq (G : Generator Seed Output)
    (hG : G.outputDist = uniformOfFintype Output)
    (Admissible : Adversary Output → Prop) : G.Secure Admissible 0 := by
  intro adversary _
  simp [advantage, realExperiment, idealExperiment, hG]

/-- Zero-error security against arbitrary tests is equivalent to exactly uniform output. -/
theorem secure_zero_iff_outputDist_eq_uniform (G : Generator Seed Output) :
    G.Secure (fun _ => True) 0 ↔ G.outputDist = uniformOfFintype Output := by
  classical
  refine ⟨fun h => ?_, fun h => G.secure_zero_of_outputDist_eq h _⟩
  ext output
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simpa [advantage, realExperiment, idealExperiment, PMF.bind_apply, PMF.pure_apply,
    sub_eq_zero] using h (fun x => PMF.pure (decide (x = output))) trivial

/-- Enlarging the allowed advantage preserves security. -/
theorem Secure.mono {G : Generator Seed Output} {Admissible : Adversary Output → Prop} :
    Monotone (G.Secure Admissible) :=
  fun _ _ hεδ h adversary ha => (h adversary ha).trans (by exact_mod_cast hεδ)

/-- Security against a larger class of adversaries implies security against a smaller class. -/
theorem Secure.of_admissible {G : Generator Seed Output}
    {Admissible Restricted : Adversary Output → Prop} {ε : ℝ≥0}
    (h : G.Secure Admissible ε) (hsub : ∀ adversary, Restricted adversary → Admissible adversary) :
    G.Secure Restricted ε := fun adversary ha => h adversary (hsub adversary ha)

section RangeTests

variable [DecidableEq Output]

omit [Nonempty Seed] [Fintype Output] [Nonempty Output] in
/-- Decide range membership by finite seed enumeration and output comparison. -/
def rangeTest (G : Generator Seed Output) (output : Output) : Bool :=
  decide (∃ seed, G seed = output)

omit [Nonempty Seed] [Fintype Output] [Nonempty Output] in
/-- The deterministic adversary that tests membership in the generator's range. -/
noncomputable def rangeAdversary (G : Generator Seed Output) : Adversary Output :=
  fun output => PMF.pure (G.rangeTest output)

omit [Fintype Output] [Nonempty Output] in
/-- The range test always accepts a generated output. -/
@[simp]
theorem realExperiment_rangeAdversary (G : Generator Seed Output) :
    G.realExperiment G.rangeAdversary = PMF.pure true := by
  simp [realExperiment, outputDist, PMF.bind_map, rangeAdversary, rangeTest, Function.comp_def,
    PMF.bind_const]

omit [Nonempty Seed] in
/-- The range test's acceptance probability under uniform sampling is the fraction
of outputs in the range. -/
theorem idealExperiment_rangeAdversary (G : Generator Seed Output) :
    (idealExperiment G.rangeAdversary true).toReal =
      Nat.card (Set.range G) / (Fintype.card Output : ℝ) := by
  simp only [idealExperiment, rangeAdversary, rangeTest, PMF.bind_apply, PMF.pure_apply,
    uniformOfFintype_apply, tsum_fintype]
  simp only [mul_ite, mul_one, mul_zero, eq_comm (a := true), decide_eq_true_eq]
  rw [← Finset.sum_filter]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, div_eq_mul_inv]

/-- The exact advantage of the range-membership adversary. -/
theorem advantage_rangeAdversary (G : Generator Seed Output) :
    G.advantage G.rangeAdversary =
      1 - Nat.card (Set.range G) / (Fintype.card Output : ℝ) := by
  have hprob : (idealExperiment G.rangeAdversary true).toReal ≤ 1 :=
    (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) ENNReal.one_ne_top).mpr
      (PMF.coe_le_one _ _)
  rw [advantage, realExperiment_rangeAdversary]
  simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one]
  rw [abs_of_nonneg (sub_nonneg.mpr hprob), idealExperiment_rangeAdversary]

/-- Every generator has an unbounded distinguisher with advantage at least
`1 - |Seed| / |Output|`. Collisions can only improve this attack. -/
theorem one_sub_card_div_le_advantage_rangeAdversary (G : Generator Seed Output) :
    1 - Fintype.card Seed / (Fintype.card Output : ℝ) ≤
      G.advantage G.rangeAdversary := by
  rw [advantage_rangeAdversary]
  have hcard : Nat.card (Set.range G) ≤ Fintype.card Seed := by
    simpa using Finite.card_range_le G
  gcongr

/-- Security is impossible below the range-test bound whenever that test is admissible. -/
theorem not_secure_of_rangeAdversary (G : Generator Seed Output)
    {Admissible : Adversary Output → Prop} {ε : ℝ≥0}
    (ha : Admissible G.rangeAdversary)
    (hε : (ε : ℝ) < 1 - Fintype.card Seed / (Fintype.card Output : ℝ)) :
    ¬ G.Secure Admissible ε := by
  intro h
  exact (hε.trans_le G.one_sub_card_div_le_advantage_rangeAdversary).not_ge (h _ ha)

end RangeTests

/-- An expanding generator cannot be perfectly secure against arbitrary adversaries. -/
theorem not_secure_zero_of_isExpanding (G : Generator Seed Output) (hG : G.IsExpanding) :
    ¬ G.Secure (fun _ => True) 0 := by
  classical
  apply G.not_secure_of_rangeAdversary trivial
  have hpos : (0 : ℝ) < Fintype.card Output := by exact_mod_cast Fintype.card_pos
  have hlt : (Fintype.card Seed : ℝ) < Fintype.card Output := by exact_mod_cast hG
  simpa using sub_pos.mpr ((div_lt_one hpos).mpr hlt)

/-- There is no expanding, perfectly secure generator against arbitrary adversaries. -/
theorem not_exists_isExpanding_secure_zero :
    ¬ ∃ G : Generator Seed Output, G.IsExpanding ∧ G.Secure (fun _ => True) 0 := by
  rintro ⟨G, hG, hsecure⟩
  exact G.not_secure_zero_of_isExpanding hG hsecure

section ParallelComposition

omit [Fintype Seed] [Nonempty Seed] [Fintype Output] [Nonempty Output] in
/-- Apply `G` separately to each component of a pair of seeds. -/
def prod (G : Generator Seed Output) : Generator (Seed × Seed) (Output × Output) :=
  ⟨fun x => (G x.1, G x.2)⟩

omit [Fintype Output] [Nonempty Output] in
/-- The output distribution of `G.prod` is two independent draws from `G.outputDist`. -/
theorem outputDist_prod (G : Generator Seed Output) :
    G.prod.outputDist =
      G.outputDist.bind fun y₁ => G.outputDist.map fun y₂ => (y₁, y₂) := by
  simp_rw [outputDist, prod, coe_mk,
    ← Probability.PMF.uniformOfFintype_prod Seed Seed,
    PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

omit [Fintype Output] [Nonempty Output] in
/-- First hybrid distinguisher: given `y₁`, sample `y₂ ← G.outputDist` and run `A (y₁, y₂)`. -/
noncomputable def leftReduction (G : Generator Seed Output)
    (A : Adversary (Output × Output)) : Adversary Output :=
  fun y₁ => G.outputDist.bind fun y₂ => A (y₁, y₂)

/-- Second hybrid distinguisher: given `y₂`, sample `u₁ ←$ Output` and run `A (u₁, y₂)`. -/
noncomputable def rightReduction
    (A : Adversary (Output × Output)) : Adversary Output :=
  fun y₂ => (uniformOfFintype Output).bind fun u₁ => A (u₁, y₂)

omit [Fintype Output] [Nonempty Output] in
/-- Real experiment for `G.prod` equals the real experiment for `G` against
`leftReduction`. -/
theorem realExperiment_prod (G : Generator Seed Output)
    (A : Adversary (Output × Output)) :
    G.prod.realExperiment A = G.realExperiment (G.leftReduction A) := by
  rw [realExperiment, realExperiment, outputDist_prod, PMF.bind_bind]
  congr 1
  ext y₂
  rw [leftReduction, PMF.bind_map]
  rfl

/-- Ideal experiment against `leftReduction` equals the real experiment against
`rightReduction` (both equal the hybrid distribution `(u₁, G(x₂))`). -/
theorem idealExperiment_leftReduction (G : Generator Seed Output)
    (A : Adversary (Output × Output)) :
    idealExperiment (G.leftReduction A) = G.realExperiment (rightReduction A) := by
  dsimp only [idealExperiment, realExperiment, leftReduction, rightReduction]
  exact PMF.bind_comm (uniformOfFintype Output) G.outputDist (fun u₁ y₂ => A (u₁, y₂))

/-- Ideal experiment against `rightReduction` equals the ideal experiment for `G.prod`. -/
theorem idealExperiment_rightReduction (A : Adversary (Output × Output)) :
    idealExperiment (rightReduction A) = idealExperiment A := by
  simp only [idealExperiment, ← Probability.PMF.uniformOfFintype_prod Output Output,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  exact PMF.bind_comm (uniformOfFintype Output) (uniformOfFintype Output)
    (fun u₂ u₁ => A (u₁, u₂))

/-- Hybrid advantage bound: `Adv(G.prod, A) ≤ Adv(G, leftReduction) + Adv(G, rightReduction)`. -/
theorem advantage_prod_le (G : Generator Seed Output)
    (A : Adversary (Output × Output)) :
    G.prod.advantage A ≤
      G.advantage (G.leftReduction A) + G.advantage (rightReduction A) := by
  rw [advantage, advantage, advantage,
    realExperiment_prod,
    idealExperiment_leftReduction,
    ← idealExperiment_rightReduction]
  exact abs_sub_le _ _ _

/-- Concrete security of `H(x₁, x₂) = (G(x₁), G(x₂))` via a two-step hybrid argument. -/
theorem Secure.prod {G : Generator Seed Output}
    {Admissible₁ : Adversary Output → Prop}
    {Admissible₂ : Adversary (Output × Output) → Prop}
    {ε : ℝ≥0}
    (hG : G.Secure Admissible₁ ε)
    (hLeft : ∀ A, Admissible₂ A → Admissible₁ (G.leftReduction A))
    (hRight : ∀ A, Admissible₂ A → Admissible₁ (rightReduction A)) :
    G.prod.Secure Admissible₂ (2 * ε) := by
  intro A hA
  have hle := G.advantage_prod_le A
  have h₁ := hG (G.leftReduction A) (hLeft A hA)
  have h₂ := hG (rightReduction A) (hRight A hA)
  push_cast
  linarith

end ParallelComposition

end Cslib.Crypto.PRG.Generator
