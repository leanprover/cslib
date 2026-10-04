/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Primitives.PRG.Asymptotic
public import Cslib.Crypto.Game.Statistical

/-!
# Statistical bounds for pseudorandom-generator games

The same statistical-distance bound controls every randomized test, on finite or infinite
sample types. The family theorem is a direct instance of the common semantic game calculus.
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open Probability.PMF
open scoped NNReal

/-- Every test's advantage is bounded by the statistical distance of generated and ideal samples. -/
theorem Generator.advantage_le_dist {Seed Output : Type*} (G : Generator Seed Output)
    (adversary : Adversary Output) (seed : PMF Seed) (ideal : PMF Output) :
    G.advantage adversary seed ideal ≤ dist (G.outputDist seed) ideal :=
  Game.advantage_bind_le_dist _ _ _

/-- A statistical bound gives concrete security for any chosen class of adversaries. -/
theorem Generator.secure_of_statisticallyClose {Seed Output : Type*} (G : Generator Seed Output)
    {seed : PMF Seed} {ideal : PMF Output} {ε : ℝ≥0}
    (h : StatisticallyClose (G.outputDist seed) ideal ε) (Admissible : Adversary Output → Prop) :
    G.Secure Admissible ε seed ideal :=
  fun adversary _ => (G.advantage_le_dist adversary seed ideal).trans h

/-- Negligible statistical distance implies asymptotic security for every test family. -/
theorem Family.secure_of_statisticallyIndistinguishable {Seed Output : ℕ → Type*}
    (G : Family Seed Output) {seed : ∀ n, PMF (Seed n)} {ideal : ∀ n, PMF (Output n)}
    (h : StatisticallyIndistinguishable (fun n => (G n).outputDist (seed n)) ideal)
    (Admissible : (∀ n, Adversary (Output n)) → Prop) :
    G.Secure Admissible seed ideal :=
  h.secure (fun adversary => adversary) Admissible

end Cslib.Crypto.PRG
