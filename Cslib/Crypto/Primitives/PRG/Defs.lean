/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Game
-- The default-argument tactics use this import at their call sites.
public import Cslib.Probability.PMF -- shake: keep

/-!
# Pseudorandom generators: games and concrete security

Attack Game 3.1 of [BonehShoup2023] compares a deterministic generator applied to a
uniform seed with a uniform output. The experiments also accept explicit seed and ideal
distributions, so the same definitions apply to infinite sample spaces and to intermediate
distributions in reductions. Omitted distributions default to uniform sampling from the
respective finite types. Adversaries are randomized Boolean tests. Security
is relative to a caller-supplied predicate `Admissible`, with an explicit advantage bound.
No computational model or efficiency assumption is built into the generator or the tests.

`Generator.IsExpanding` records the cardinality condition separately from security.
In particular, a generator need not expand, and an expanding generator need not be secure.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 3.1.
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open scoped NNReal

/-- A deterministic generator with seed space `Seed` and output space `Output`.
Efficiency, expansion, and security are separate properties. -/
@[ext]
structure Generator (Seed Output : Type*) where
  /-- Generate an output from a seed. -/
  toFun : Seed → Output

/-- A randomized statistical test on the output space. -/
abbrev Adversary (Output : Type*) := Output → PMF Bool

namespace Generator

variable {Seed Output : Type*}

instance : FunLike (Generator Seed Output) Seed Output where
  coe G := G.toFun
  coe_injective _ _ h := Generator.ext h

@[simp]
theorem coe_mk (f : Seed → Output) : ⇑(Generator.mk f) = f := rfl

/-- A generator expands when its output space is strictly larger than its seed space. -/
def IsExpanding [Fintype Seed] [Fintype Output] (_G : Generator Seed Output) : Prop :=
  Fintype.card Seed < Fintype.card Output

/-- Apply the generator to a seed distribution, uniform by default on finite seed types. -/
noncomputable def outputDist (G : Generator Seed Output)
    (seed : PMF Seed := by exact Cslib.Probability.PMF.uniformOfFintype _) : PMF Output :=
  seed.map G

/-- Experiment 0 of Attack Game 3.1: generate from a seed, uniform by default. -/
noncomputable def realExperiment (G : Generator Seed Output)
    (adversary : Adversary Output)
    (seed : PMF Seed := by exact Cslib.Probability.PMF.uniformOfFintype _) : Game :=
  (G.outputDist (seed := seed)).bind adversary

/-- Experiment 1 of Attack Game 3.1: give the adversary an ideal sample, uniform by default. -/
noncomputable def idealExperiment (adversary : Adversary Output)
    (ideal : PMF Output := by exact Cslib.Probability.PMF.uniformOfFintype _) : Game :=
  ideal.bind adversary

/-- The absolute difference of the probabilities of outputting `true` in the two
experiments, as in Attack Game 3.1 of [BonehShoup2023]. -/
noncomputable def advantage (G : Generator Seed Output) (adversary : Adversary Output)
    (seed : PMF Seed := by exact Cslib.Probability.PMF.uniformOfFintype _)
    (ideal : PMF Output := by exact Cslib.Probability.PMF.uniformOfFintype _) : ℝ :=
  Game.advantage (G.realExperiment adversary (seed := seed))
    (idealExperiment adversary (ideal := ideal))

/-- Concrete security against admissible adversaries. The predicate is supplied by the
caller, for example to restrict tests to a chosen computational resource bound.
Taking `Admissible := fun _ => True` allows arbitrary adversaries. -/
def Secure (G : Generator Seed Output) (Admissible : Adversary Output → Prop)
    (ε : ℝ≥0) (seed : PMF Seed := by exact Cslib.Probability.PMF.uniformOfFintype _)
    (ideal : PMF Output := by exact Cslib.Probability.PMF.uniformOfFintype _) : Prop :=
  ∀ adversary, Admissible adversary → G.advantage adversary (seed := seed) (ideal := ideal) ≤ ε

end Generator
end Cslib.Crypto.PRG
