/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Crypto.Experiment.Hybrid

open Cslib.Crypto
open scoped NNReal

namespace CslibTests.Experiment

-- A zero-hop chain needs no positivity assumption on its length.
example (experiment : Experiment) : Experiment.advantage experiment experiment ≤ 0 :=
  Experiment.advantage_hybrid_le_sum_fin (hops := 0) (fun _ => experiment)

-- With no hops, both padded mixtures reject regardless of the sole experiment.
example (experiment : Experiment) (samplingRange : ℕ) [NeZero samplingRange] :
    Experiment.advantage experiment experiment = samplingRange *
      Experiment.advantage (PMF.pure false) (PMF.pure false) := by
  simpa only [Nat.not_lt_zero, dite_false, PMF.bind_const] using
    Experiment.advantage_hybrid_average_fin (hops := 0)
    (fun _ => experiment) samplingRange (Nat.zero_le _)

-- Two hops have exactly three games, with no extension beyond their finite domain.
example (games : Fin 3 → Experiment) :
    Experiment.advantage (games 0) (games 2) ≤
      Experiment.advantage (games 0) (games 1) +
        Experiment.advantage (games 1) (games 2) := by
  simpa [Fin.sum_univ_succ] using (Experiment.advantage_hybrid_le_sum_fin games)

-- Of four sampling indices, only the third real hop accepts; the unused fourth index rejects.
example : Experiment.succProbability
    ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).bind
      (fun i => if i.val < 3 then PMF.pure (decide (3 ≤ i.val + 1)) else PMF.pure false)) =
      1 / 4 := by
  rw [Experiment.succProbability_uniform]
  norm_num [Fin.sum_univ_succ, Experiment.succProbability, PMF.pure_apply]

-- Three alternating hops cancel to one endpoint gap; sampling four indices loses a factor four.
example :
    let games : Fin 4 → Experiment := fun i => PMF.pure (decide (i.val % 2 = 0))
    Experiment.advantage
      ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).bind
        (fun i => if hi : i.val < 3 then games (i.castLT hi).castSucc else PMF.pure false))
      ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).bind
        (fun i => if hi : i.val < 3 then games (i.castLT hi).succ else PMF.pure false)) =
      1 / 4 := by
  dsimp only
  have h := Experiment.advantage_hybrid_average_fin
    (hops := 3) (fun i => PMF.pure (decide (i.val % 2 = 0))) 4 (by decide)
  have hend : Experiment.advantage
      (PMF.pure (decide ((0 : Fin 4).val % 2 = 0)))
      (PMF.pure (decide ((Fin.last 3).val % 2 = 0))) = 1 := by
    norm_num [Experiment.advantage, Experiment.succProbability, NNReal.nndist_eq, PMF.pure_apply]
  rw [hend] at h
  apply (eq_div_iff (by norm_num : (4 : ℝ≥0) ≠ 0)).mpr
  exact (mul_comm _ _).trans h.symm

-- A reversed single-hop reduction has signed loss -1, even with a non-dyadic sampling range.
example :
    let games : Fin 2 → Experiment := fun i => PMF.pure (decide (i.val = 0))
    let first : Fin 1 → Experiment := fun _ => PMF.pure false
    let second : Fin 1 → Experiment := fun _ => PMF.pure true
    (Experiment.succProbability (games 0) : ℝ) -
      Experiment.succProbability (games (Fin.last 1)) = (3 : ℝ) * (-1) *
        (Experiment.succProbability ((Cslib.Probability.PMF.uniformOfFintype (Fin 3)).bind
          (fun i => if hi : i.val < 1 then first (i.castLT hi) else PMF.pure false)) -
        Experiment.succProbability ((Cslib.Probability.PMF.uniformOfFintype (Fin 3)).bind
          (fun i => if hi : i.val < 1 then second (i.castLT hi) else PMF.pure false))) := by
  refine Experiment.succProbability_hybrid_reduction_fin
    (fun i => PMF.pure (decide (i.val = 0)))
    (fun _ => PMF.pure false) (fun _ => PMF.pure true) 3 (by decide) (-1) ?_
  intro i
  have hi : i.val = 0 := by lia
  norm_num [hi, Experiment.succProbability, PMF.pure_apply]

-- A staged family uses its natural prefix directly; padded selection still has exact loss four.
example :
    let games : ℕ → Experiment := fun stage => PMF.pure (decide (stage = 0))
    Experiment.advantage
      ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).bind
        (fun i => if i.val < 3 then games i.val else PMF.pure false))
      ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).bind
        (fun i => if i.val < 3 then games (i.val + 1) else PMF.pure false)) = 1 / 4 := by
  dsimp only
  have h := Experiment.advantage_hybrid_average
    (fun stage => PMF.pure (decide (stage = 0))) 3 4 (by decide)
  have hend : Experiment.advantage (PMF.pure true) (PMF.pure false) = 1 := by
    norm_num [Experiment.advantage, Experiment.succProbability, NNReal.nndist_eq, PMF.pure_apply]
  change Experiment.advantage (PMF.pure true) (PMF.pure false) = _ at h
  rw [hend] at h
  apply (eq_div_iff (by norm_num : (4 : ℝ≥0) ≠ 0)).mpr
  exact (mul_comm _ _).trans h.symm

end CslibTests.Experiment
