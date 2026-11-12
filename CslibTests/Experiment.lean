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

end CslibTests.Experiment
