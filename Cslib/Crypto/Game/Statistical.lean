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

/-- The absolute difference of acceptance probabilities is precisely statistical distance
for Boolean experiments. -/
theorem Game.advantage_eq_dist (real ideal : Game) : advantage real ideal = dist real ideal := by
  have hfalse (p : PMF Bool) : (p false).toReal = 1 - (p true).toReal := by
    rw [← sum_toReal p, Fintype.sum_bool, add_sub_cancel_left]
  rw [dist_eq, Fintype.sum_bool, hfalse, hfalse, sub_sub_sub_cancel_left,
    abs_sub_comm (ideal true).toReal, add_self_div_two]

/-- No randomized Boolean test distinguishes better than the statistical distance. -/
theorem Game.advantage_bind_le_dist {α : Type*} (real ideal : PMF α) (test : α → Game) :
    advantage (real.bind test) (ideal.bind test) ≤ dist real ideal :=
  (advantage_eq_dist _ _).trans_le (dist_bind_le real ideal test)

/-- A statistical-closeness bound is an advantage bound for every randomized test. -/
theorem Game.advantage_le_of_statisticallyClose {α : Type*} {real ideal : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose real ideal ε) (test : α → Game) :
    advantage (real.bind test) (ideal.bind test) ≤ ε :=
  (advantage_bind_le_dist real ideal test).trans h

/-- Two discrete ensembles are statistically indistinguishable when their statistical distance
is negligible. Neither their ambient type nor their supports need be finite. -/
def StatisticallyIndistinguishable {α : ℕ → Type*} (X Y : ∀ n, PMF (α n)) : Prop :=
  Negligible (fun n => dist (X n) (Y n))

namespace StatisticallyIndistinguishable

variable {α β : ℕ → Type*} {X Y Z : ∀ n, PMF (α n)}

/-- An ensemble is statistically indistinguishable from itself. -/
theorem refl (X : ∀ n, PMF (α n)) : StatisticallyIndistinguishable X X := by
  simp [StatisticallyIndistinguishable]

/-- Statistical indistinguishability is symmetric. -/
theorem symm (h : StatisticallyIndistinguishable X Y) : StatisticallyIndistinguishable Y X := by
  simpa only [StatisticallyIndistinguishable, dist_comm] using h

/-- Statistical errors add across a game hop. -/
theorem trans (hXY : StatisticallyIndistinguishable X Y)
    (hYZ : StatisticallyIndistinguishable Y Z) : StatisticallyIndistinguishable X Z :=
  negligible_of_le (hXY.add hYZ) (fun _ => dist_nonneg) (fun _ => dist_triangle _ _ _)

/-- Arbitrary randomized postprocessing preserves statistical indistinguishability. -/
theorem bind (h : StatisticallyIndistinguishable X Y) (kernel : ∀ n, α n → PMF (β n)) :
    StatisticallyIndistinguishable (fun n => (X n).bind (kernel n))
      (fun n => (Y n).bind (kernel n)) :=
  negligible_of_le h (fun _ => dist_nonneg) (fun _ => dist_bind_le _ _ _)

/-- Deterministic postprocessing preserves statistical indistinguishability. -/
theorem map (h : StatisticallyIndistinguishable X Y) (f : ∀ n, α n → β n) :
    StatisticallyIndistinguishable (fun n => (X n).map (f n)) (fun n => (Y n).map (f n)) :=
  negligible_of_le h (fun _ => dist_nonneg) (fun _ => dist_map_le _ _ _)

/-- Statistical indistinguishability implies security against any chosen class of tests.
The test may depend arbitrarily on the security parameter. -/
theorem secure (h : StatisticallyIndistinguishable X Y) {Adversary : Type*}
    (test : Adversary → (n : ℕ) → α n → Game) (Admissible : Adversary → Prop) :
    Game.Secure (fun adversary n => (X n).bind (test adversary n))
      (fun adversary n => (Y n).bind (test adversary n)) Admissible := fun _ _ =>
  negligible_of_le h (fun _ => Game.advantage_nonneg _ _)
    (fun _ => Game.advantage_bind_le_dist _ _ _)

end StatisticallyIndistinguishable
end Cslib.Crypto
