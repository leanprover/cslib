/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Primitives.PRG.Defs

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

open MeasureTheory ProbabilityTheory Cslib.Probability.Measure
open scoped NNReal

variable {Seed Output : Type*}

variable [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
variable [MeasurableSpace Output] [MeasurableSingletonClass Output]
variable [Fintype Seed] [Nonempty Seed] [Fintype Output] [Nonempty Output]

omit [MeasurableSingletonClass Seed] [MeasurableSingletonClass Output] in
/-- Advantage is nonnegative. -/
theorem advantage_nonneg (G : Generator Seed Output) (adversary : Adversary Output) :
    0 ≤ G.advantage adversary := abs_nonneg _

/-- Advantage is at most one, with the normalization of Attack Game 3.1. -/
theorem advantage_le_one (G : Generator Seed Output) (adversary : Adversary Output) :
    G.advantage adversary ≤ 1 := by
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top
    (prob_le_one (μ := G.realExperiment adversary) (s := {true}))
  have hideal := ENNReal.toReal_mono ENNReal.one_ne_top
    (prob_le_one (μ := idealExperiment adversary) (s := {true}))
  simp only [ENNReal.toReal_one] at hreal hideal
  apply abs_sub_le_iff.mpr
  constructor
  · linarith [@ENNReal.toReal_nonneg (idealExperiment adversary {true})]
  · linarith [@ENNReal.toReal_nonneg (G.realExperiment adversary {true})]

/-- Error one imposes no restriction on a generator. -/
theorem secure_one (G : Generator Seed Output) (Admissible : Adversary Output → Prop) :
    G.Secure Admissible 1 := fun adversary _ => G.advantage_le_one adversary

omit [MeasurableSingletonClass Output] in
/-- A test whose output distribution is independent of its input has zero advantage. -/
@[simp]
theorem advantage_const (G : Generator Seed Output) (p : ProbabilityMeasure Bool) :
    G.advantage (fun _ => p) = 0 := by
  simp [advantage, realExperiment, idealExperiment, Measure.bind_const]

omit [MeasurableSingletonClass Seed] [MeasurableSingletonClass Output] in
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
  apply Measure.ext_of_singleton
  intro output
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  simpa [advantage, realExperiment, idealExperiment, Adversary.ofPure,
    Measure.bind_dirac_eq_map _ (measurable_of_countable _),
    Measure.map_apply (measurable_of_countable _), Set.preimage, sub_eq_zero] using
    h (Adversary.ofPure (fun x => decide (x = output))) trivial

omit [MeasurableSingletonClass Seed] [MeasurableSingletonClass Output] in
/-- Enlarging the allowed advantage preserves security. -/
theorem Secure.mono {G : Generator Seed Output} {Admissible : Adversary Output → Prop} :
    Monotone (G.Secure Admissible) :=
  fun _ _ hεδ h adversary ha => (h adversary ha).trans (by exact_mod_cast hεδ)

omit [MeasurableSingletonClass Seed] [MeasurableSingletonClass Output] in
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
  Adversary.ofPure G.rangeTest

omit [Fintype Output] [Nonempty Output] in
/-- The range test always accepts a generated output. -/
@[simp]
theorem realExperiment_rangeAdversary (G : Generator Seed Output) :
    G.realExperiment G.rangeAdversary = Measure.dirac true := by
  have htest : Measurable G.rangeTest := by
    change Measurable (fun output => decide (∃ seed, G seed = output))
    simpa using
      (measurable_const.ite (Set.finite_range G).measurableSet measurable_const :
        Measurable (fun output => if output ∈ Set.range G then true else false))
  simp only [realExperiment, outputDist, rangeAdversary, Adversary.ofPure,
    Measure.coe_toProbabilityMeasure]
  rw [Measure.bind_dirac_eq_map _ htest, Measure.map_map htest (measurable_of_countable G)]
  have h : (G.rangeTest ∘ G) = fun _ => true := by
    funext seed
    simp [rangeTest]
  simp [h]

omit [Nonempty Seed] [MeasurableSpace Seed] [MeasurableSingletonClass Seed] in
/-- The range test's acceptance probability under uniform sampling is the fraction
of outputs in the range. -/
theorem idealExperiment_rangeAdversary (G : Generator Seed Output) :
    (idealExperiment G.rangeAdversary {true}).toReal =
      Nat.card (Set.range G) / (Fintype.card Output : ℝ) := by
  classical
  simp only [idealExperiment, rangeAdversary, Adversary.ofPure,
    Measure.coe_toProbabilityMeasure]
  rw [Measure.bind_dirac_eq_map _ (measurable_of_countable _),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton true)]
  simp [uniformOn_univ, Measure.count_apply_finite _ (Set.toFinite _),
    rangeTest, Set.preimage,
    Fintype.card_subtype, Nat.card_eq_fintype_card, ENNReal.toReal_div]

/-- The exact advantage of the range-membership adversary. -/
theorem advantage_rangeAdversary (G : Generator Seed Output) :
    G.advantage G.rangeAdversary =
      1 - Nat.card (Set.range G) / (Fintype.card Output : ℝ) := by
  have hprob : (idealExperiment G.rangeAdversary {true}).toReal ≤ 1 := by
    exact_mod_cast ENNReal.toReal_mono ENNReal.one_ne_top
      (prob_le_one (μ := idealExperiment G.rangeAdversary) (s := {true}))
  rw [advantage, realExperiment_rangeAdversary]
  simp only [Measure.dirac_apply_of_mem (Set.mem_singleton true), ENNReal.toReal_one]
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

end Cslib.Crypto.PRG.Generator
