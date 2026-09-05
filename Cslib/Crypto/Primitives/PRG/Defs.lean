/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Pseudorandom generators: games and concrete security

Attack Game 3.1 of [BonehShoup2023] compares a deterministic generator applied to a
uniform seed with a uniform output. Adversaries are randomized Boolean tests. Security
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

variable [Fintype Seed] [Nonempty Seed] [Fintype Output] [Nonempty Output]

/-- The distribution obtained by applying the generator to a uniform seed. -/
noncomputable def outputDist (G : Generator Seed Output) : PMF Output :=
  (PMF.uniformOfFintype Seed).map G

/-- Experiment 0 of Attack Game 3.1: give the adversary a generated output. -/
noncomputable def realExperiment (G : Generator Seed Output)
    (adversary : Adversary Output) : PMF Bool :=
  G.outputDist.bind adversary

/-- Experiment 1 of Attack Game 3.1: give the adversary a uniform output. -/
noncomputable def idealExperiment (adversary : Adversary Output) : PMF Bool :=
  (PMF.uniformOfFintype Output).bind adversary

/-- The absolute difference of the probabilities of outputting `true` in the two
experiments, as in Attack Game 3.1 of [BonehShoup2023]. -/
noncomputable def advantage (G : Generator Seed Output) (adversary : Adversary Output) : ℝ :=
  |(G.realExperiment adversary true).toReal - (idealExperiment adversary true).toReal|

/-- Concrete security against admissible adversaries. The predicate is supplied by the
caller, for example to restrict tests to a chosen computational resource bound.
Taking `Admissible := fun _ => True` allows arbitrary adversaries. -/
def Secure (G : Generator Seed Output) (Admissible : Adversary Output → Prop)
    (ε : ℝ≥0) : Prop :=
  ∀ adversary, Admissible adversary → G.advantage adversary ≤ ε

end Generator
end Cslib.Crypto.PRG
