/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Game
public import Cslib.Probability.StatisticalDistance

/-!
# Statistical security and Boolean games

For Boolean experiments, distinguishing advantage is exactly statistical distance. A randomized
test cannot increase this distance, even on an infinite sample type. Consequently statistically
indistinguishable ensembles are secure against every family of tests, with no efficiency assumption.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability.PMF
open scoped NNReal

/-- The absolute difference of success probabilities is precisely statistical distance
for Boolean experiments. -/
theorem Game.advantage_eq_nndist (game1 game2 : Game) :
    advantage game1 game2 = nndist game1 game2 := by
  have hfalse (p : PMF Bool) : (p false).toReal = 1 - (p true).toReal := by
    rw [← sum_toReal p, Fintype.sum_bool, add_sub_cancel_left]
  apply NNReal.eq
  rw [coe_advantage, coe_nndist, dist_eq, Fintype.sum_bool]
  simp only [succProbability, ENNReal.coe_toNNReal_eq_toReal]
  rw [hfalse, hfalse, sub_sub_sub_cancel_left, abs_sub_comm (game2 true).toReal,
    add_self_div_two]

/-- No randomized Boolean test distinguishes better than the statistical distance. -/
theorem Game.advantage_bind_le_nndist {α : Type*} (p q : PMF α) (test : α → Game) :
    advantage (p.bind test) (q.bind test) ≤ nndist p q :=
  (advantage_eq_nndist _ _).trans_le (nndist_bind_le p q test)

/-- A statistical-closeness bound is an advantage bound for every randomized test. -/
theorem Game.advantage_le_of_statisticallyClose {α : Type*} {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) (test : α → Game) :
    advantage (p.bind test) (q.bind test) ≤ ε :=
  (advantage_bind_le_nndist p q test).trans (by rw [← NNReal.coe_le_coe, coe_nndist]; exact h)

/-- Two discrete ensembles are statistically indistinguishable when their statistical distance
is negligible. Neither their ambient type nor their supports need be finite. -/
def StatisticallyIndistinguishable {α : ℕ → Type*} (X Y : ∀ n, PMF (α n)) : Prop :=
  Negligible (fun n => nndist (X n) (Y n))

namespace StatisticallyIndistinguishable

variable {α β : ℕ → Type*} {X Y Z : ∀ n, PMF (α n)}

/-- An ensemble is statistically indistinguishable from itself. -/
theorem refl (X : ∀ n, PMF (α n)) : StatisticallyIndistinguishable X X := by
  simp [StatisticallyIndistinguishable]

/-- Statistical indistinguishability is symmetric. -/
theorem symm (h : StatisticallyIndistinguishable X Y) : StatisticallyIndistinguishable Y X := by
  simpa [StatisticallyIndistinguishable, nndist_comm] using h

/-- Statistical errors add across a game hop. -/
theorem trans (hXY : StatisticallyIndistinguishable X Y)
    (hYZ : StatisticallyIndistinguishable Y Z) : StatisticallyIndistinguishable X Z :=
  negligible_of_le (hXY.add hYZ) fun _ => nndist_triangle _ _ _

/-- Arbitrary randomized postprocessing preserves statistical indistinguishability. -/
theorem bind (h : StatisticallyIndistinguishable X Y) (kernel : ∀ n, α n → PMF (β n)) :
    StatisticallyIndistinguishable (fun n => (X n).bind (kernel n))
      (fun n => (Y n).bind (kernel n)) :=
  negligible_of_le h fun _ => nndist_bind_le _ _ _

/-- Deterministic postprocessing preserves statistical indistinguishability. -/
theorem map (h : StatisticallyIndistinguishable X Y) (f : ∀ n, α n → β n) :
    StatisticallyIndistinguishable (fun n => (X n).map (f n)) (fun n => (Y n).map (f n)) :=
  negligible_of_le h fun _ => nndist_map_le _ _ _

/-- Statistical indistinguishability implies indistinguishability for any chosen class of
tests. The test may depend arbitrarily on the security parameter. -/
theorem indistinguishable (h : StatisticallyIndistinguishable X Y) {Adversary : Type*}
    (test : Adversary → (n : ℕ) → α n → Game) (Admissible : Adversary → Prop) :
    Game.Indistinguishable (fun adversary n => (X n).bind (test adversary n))
      (fun adversary n => (Y n).bind (test adversary n)) Admissible := fun _ _ =>
  negligible_of_le h fun _ => Game.advantage_bind_le_nndist _ _ _

end StatisticallyIndistinguishable
end Cslib.Crypto
