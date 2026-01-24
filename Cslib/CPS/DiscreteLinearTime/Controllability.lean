/-
Copyright (c) 2026 Bashar Hamade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bashar Hamade
-/

import Cslib.Init
import Cslib.CPS.DiscreteLinearTime.Basic
import Cslib.CPS.DiscreteLinearTime.Reachability
import Cslib.CPS.DiscreteLinearTime.Cayley

universe u v

variable {σ : Type u} {ι : Type v}
variable [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι]
variable [Inhabited ι]
variable {sys : DiscreteLinearSystemState σ ι}

open BigOperators Finset DiscreteLinearSystemState
/-!
# Controllability Analysis

This module analyzes the controllability of discrete-time linear systems.
It introduces the controllability matrix, the controllability column space,
and connects these concepts to reachability.
The main result is the Kalman Controllability Rank Condition.

## Main Definitions
* `controllabilityColumn`: The i-th term `A^i B`.
* `controllabilityMatrix`: The matrix formed by columns `[B, AB, ..., A^(n-1)B]`.
* `controllabilityColumnSpace`: The subspace spanned by the columns of the controllability matrix.
* `totalReachableSubmodule`: The join of all reachable subspaces.

## Main Theorems
* `evolution_eq_matrix_form`: Expresses the state after `k` steps using the controllability matrix.
* `controllabilityColumnSpace_stabilizes`: The span of the controllability matrix stabilizes
after `n` steps (where `n` is the dimension of the state space), due to Cayley-Hamilton.
* `full_finrank_equivalent_to_reachability`: A system is reachable if and only
if the controllability matrix has full rank.
-/


/-- The i-th column block of the controllability matrix: Aⁱ B -/
def controllabilityColumn (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (i : ℕ) : ι →L[ℂ] σ :=
  (a ^ i).comp B

/-- The controllability matrix up to step `n`, viewed as a function
from index `i` to the operator `A^i B`. -/
def controllabilityMatrix (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) : Fin n → (ι →L[ℂ] σ) :=
  fun i => (a ^ (i : ℕ)).comp B

/-- The subspace spanned by the columns of the controllability matrix up to step `k`.
    It represents the set of states reachable in `k` steps. -/
def controllabilityColumnSpace (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (k : ℕ) : Submodule ℂ σ :=
  Submodule.span ℂ (⋃ i : Fin k, Set.range (fun v => (a ^ i.val) (B v)))

/-- Helper theorem: Expands the state evolution from zero initial state as a sum. -/
theorem evolve_from_zero_eq_sum
(s : DiscreteLinearSystemState σ ι) (u : ℕ → ι)  (k : ℕ) :
   s.evolve_from_zero u k =
     ∑ j ∈ Finset.range k, (s.a ^ (k - 1 - j)) (s.B (u j)) := by
    induction k with
    | zero =>
      simp [DiscreteLinearSystemState.evolve_from_zero]
    | succ k ih =>
      simp [DiscreteLinearSystemState.evolve_from_zero]
      rw [ih]
      simp
      rw [Finset.sum_range_succ]
      simp
      apply Finset.sum_congr rfl
      intro x hx
      have : s.a.comp (s.a ^ (k - 1 - x)) = s.a ^ (k -  x ) := by
        rw [← system_power_multiplication_flopped]
        congr
        have : x < k := Finset.mem_range.mp hx
        omega
      rw [<-ContinuousLinearMap.comp_apply]
      rw [this]

/-- Matrix form of evolution equation -/
theorem evolution_eq_matrix_form (s : DiscreteLinearSystemState σ ι) (kf : ℕ) (u : ℕ → ι)  :
    s.evolve_from_zero u kf =
    ∑ i : Fin kf, (controllabilityMatrix s.a s.B kf i) (u (kf - 1 - (i : ℕ))) := by
    rw [evolve_from_zero_eq_sum]
    simp only [controllabilityMatrix]
    rw [← Finset.sum_attach]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    refine Finset.sum_bij'
      (fun j _ => ⟨kf - 1 - j.val, ?_⟩)
      (fun i _ => ⟨kf - 1 - i.val, ?_⟩)
      ?_ ?_ ?_ ?_ ?_
    · obtain ⟨j, hj⟩ := j; simp at hj ⊢; omega
    · simp; omega
    · intros; simp
    · intros; simp
    · intro ⟨j, hj⟩ _; ext; simp at hj ⊢; omega
    · intro i _; ext; simp; omega
    · intro ⟨j, hj⟩ _; simp at hj ⊢; (congr; omega)


/-- The set of reachable states in `k` steps exactly equals
the controllability column space of order `k`. -/
theorem reachable_set_eq_controllability_range
(s : DiscreteLinearSystemState σ ι) (k : ℕ) (hk : k > 0) :
    reachableSetInKSteps s k = controllabilityColumnSpace s.a s.B k := by
  ext x
  simp only [SetLike.mem_coe]
  constructor
  · intro h_reach
    obtain ⟨u, h_reach⟩ := h_reach
    rw [evolution_eq_matrix_form s k] at h_reach
    rw [← h_reach]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.subset_span
    simp only [Set.mem_iUnion, Set.mem_range]
    use i
    use u (k - 1 - ↑i)
    simp [controllabilityMatrix]
  · intro h_span
    induction h_span using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_iUnion, Set.mem_range] at hx
      obtain ⟨i, v, rfl⟩ := hx
      use fun j => if j = k - 1 - i.val then v else 0
      rw [evolve_from_zero_eq_sum]
      have hi_lt : k - 1 - i.val < k := by omega
      rw [Finset.sum_eq_single_of_mem (k - 1 - i.val) (Finset.mem_range.mpr hi_lt)]
      · simp only [ite_true]
        congr 1
        have hi_bound : i.val < k := i.isLt
        rw [Nat.sub_sub_self (Nat.lt_iff_le_pred hk |>.mp hi_bound)]
      · intro b bh b_diff
        rw [if_neg b_diff]
        simp only [ContinuousLinearMap.map_zero]
    | zero =>
      use fun _ => 0
      rw [evolve_from_zero_eq_sum]
      simp only [ContinuousLinearMap.map_zero, Finset.sum_const_zero]
    | add x y _ _ ihx ihy =>
      obtain ⟨ux, hux⟩ := ihx
      obtain ⟨uy, huy⟩ := ihy
      use fun j => ux j + uy j
      rw [evolve_from_zero_eq_sum]
      simp only [ContinuousLinearMap.map_add, Finset.sum_add_distrib]
      rw [← evolve_from_zero_eq_sum, ← evolve_from_zero_eq_sum]
      rw [hux, huy]
    | smul c x _ ihx =>
      obtain ⟨ux, hux⟩ := ihx
      use fun j => c • ux j
      rw [evolve_from_zero_eq_sum]
      simp only [ContinuousLinearMap.map_smul]
      rw [← Finset.smul_sum]
      congr 1
      rw [evolve_from_zero_eq_sum] at hux
      exact hux


/-- The controllability column space is non-decreasing with respect to `k`. -/
theorem controllabilityColumnSpace_mono (s : DiscreteLinearSystemState σ ι)
{k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    controllabilityColumnSpace s.a s.B k₁ ≤ controllabilityColumnSpace s.a s.B k₂ := by
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx ⊢

  obtain ⟨i, v, rfl⟩ := hx
  exact ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩, v, rfl⟩


/-- Stabilizatlon theorem: The controllability column space stabilizes after `n` steps,
    where `n` is the dimension of the state space.
    This is a consequence of the Cayley-Hamilton theorem. -/
theorem controllabilityColumnSpace_stabilizes
    [FiniteDimensional ℂ σ]
    (s : DiscreteLinearSystemState σ ι) (n : ℕ) (hn : n > 0)
    (h_dim : Module.finrank ℂ σ = n) :
    ∀ k ≥ n, controllabilityColumnSpace s.a s.B k = controllabilityColumnSpace s.a s.B n := by
  intro k hk
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, v, rfl⟩ := hx
    by_cases hi : i.val < n
    · apply Submodule.subset_span
      simp only [Set.mem_iUnion, Set.mem_range]
      exact ⟨⟨i.val, hi⟩, v, rfl⟩
    · push_neg at hi
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
      induction d with
      | zero =>
        simp only [Nat.add_zero] at hd
        rw [hd]
        apply cayley_hamilton_controllability' s.a s.B n hn h_dim
        trivial
      | succ m ih =>
        have h_ge : n + (m + 1) ≥ n := Nat.le_add_right n (m + 1)
        apply cayley_hamilton_controllability' s.a s.B n hn h_dim
        rw [hd]
        trivial
  · apply controllabilityColumnSpace_mono
    trivial


/-- The total reachable submodule is the limit (supremum) of the controllability column spaces. -/
def totalReachableSubmodule  (sys : DiscreteLinearSystemState σ ι) : Submodule ℂ σ :=
  ⨆ k : ℕ, controllabilityColumnSpace sys.a sys.B k


/-- If the system is reachable, then the total reachable set is the entire space. -/
theorem reachable_implies_total_reachable_eq_univ
    (sys : DiscreteLinearSystemState σ ι)
    (h_reach : sys.IsReachable) : totalReachableSet sys = Set.univ := by
  ext x
  simp only [totalReachableSet, Set.mem_iUnion]
  simp only [Set.mem_univ, iff_true]
  -- By definition of IsReachable, for any x there exists k and u such that we reach x
  obtain ⟨k, u, hk_pos, hx⟩ := h_reach x
  exact ⟨k, u, hx⟩


/-- For a finite dimensional system of dimension `n`, the total reachable submodule is equal to
    the controllability column space at step `n`. -/
theorem totalReachableSubmodule_eq_controllabilityColumnSpace
    [FiniteDimensional ℂ σ]
    (sys : DiscreteLinearSystemState σ ι) (n : ℕ) (hn : n > 0)
    (h_dim : Module.finrank ℂ σ = n) :
    totalReachableSubmodule sys = controllabilityColumnSpace sys.a sys.B n := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hk : k ≤ n
    · exact controllabilityColumnSpace_mono sys hk
    · push_neg at hk
      rw [controllabilityColumnSpace_stabilizes sys n hn h_dim k (le_of_lt hk)]
  · exact le_iSup (controllabilityColumnSpace sys.a sys.B) n

/-- If a system is reachable, then its controllability column space
at step `n` is the whole space (Top). -/
theorem reachable_implies_controllabilityColumnSpace_eq_top
    [FiniteDimensional ℂ σ]
    (sys : DiscreteLinearSystemState σ ι) (n : ℕ) (hn : n > 0)
    (h_dim : Module.finrank ℂ σ = n)
    (h_reach : sys.IsReachable) :
    controllabilityColumnSpace sys.a sys.B n = ⊤ := by
  rw [← totalReachableSubmodule_eq_controllabilityColumnSpace sys n hn h_dim]
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, u, hk_pos, hx⟩ := h_reach x
  have h_in_k : x ∈ reachableSetInKSteps sys k := ⟨u, hx⟩
  rw [reachable_set_eq_controllability_range sys k hk_pos] at h_in_k
  exact Submodule.mem_iSup_of_mem k h_in_k

/-- Alias for `reachable_implies_controllabilityColumnSpace_eq_top`. -/
theorem reachability_implies_full_rank
    [FiniteDimensional ℂ σ]
    (sys : DiscreteLinearSystemState σ ι) (n : ℕ) (hn : n > 0)
    (h_dim : Module.finrank ℂ σ = n)
    (h_reach : sys.IsReachable) :
    controllabilityColumnSpace sys.a sys.B n = ⊤ :=
  reachable_implies_controllabilityColumnSpace_eq_top sys n hn h_dim h_reach



/-- Reachability implies that the dimension of the controllability subspace is equal
to the dimension of the state space. -/
theorem reachability_implies_rank_eq_dim
    [FiniteDimensional ℂ σ]
    (sys : DiscreteLinearSystemState σ ι)
    (h_reach : sys.IsReachable)
    (hn : Module.finrank ℂ σ > 0) :
    Module.finrank ℂ (controllabilityColumnSpace sys.a sys.B (Module.finrank ℂ σ)) =
    Module.finrank ℂ σ := by
  have h_top := reachability_implies_full_rank sys (Module.finrank ℂ σ) hn rfl h_reach
  rw [h_top]
  exact finrank_top ℂ σ

/-- Alternative formulation: The controllability submodule has full rank -/
theorem reachability_implies_full_finrank
    [FiniteDimensional ℂ σ]
    (sys : DiscreteLinearSystemState σ ι) (n : ℕ)
    (h_dim : Module.finrank ℂ σ = n)
    (hn : n > 0)
    (h_reach : sys.IsReachable) :
    Module.finrank ℂ (controllabilityColumnSpace sys.a sys.B n) = n := by
  have h_top := reachability_implies_full_rank sys n hn h_dim h_reach
  rw [h_top]
  rw [finrank_top]
  exact h_dim



/-- The Kalman Controllability Rank Condition: If the controllability matrix
 has full rank, the system is reachable. -/
theorem full_finrank_implies_reachability
    [FiniteDimensional ℂ σ]
    (sys : DiscreteLinearSystemState σ ι) (n : ℕ)
    (h_dim : Module.finrank ℂ σ = n)
    (hn : n > 0)
    (h_top : Module.finrank ℂ (controllabilityColumnSpace sys.a sys.B n) = n) :
    sys.IsReachable := by
    intro x
    have h_sub_top : controllabilityColumnSpace sys.a sys.B n = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [h_top, h_dim]
    have h_reach_sys : reachableSetInKSteps sys n = controllabilityColumnSpace sys.a sys.B n := by
      rw [reachable_set_eq_controllability_range]
      exact hn
    have hx_in : x ∈ reachableSetInKSteps sys n := by
      rw [h_reach_sys]
      rw [h_sub_top]
      simp
    obtain ⟨u, hu⟩ := hx_in
    use n, u


/-- Full equivalence: A system is reachable
if and only if the controllability matrix has full rank. -/
theorem full_finrank_equivalent_to_reachability
    [FiniteDimensional ℂ σ]
    (sys : DiscreteLinearSystemState σ ι) (n : ℕ)
    (h_dim : Module.finrank ℂ σ = n)
    (hn : n > 0) :
    sys.IsReachable ↔ Module.finrank ℂ (controllabilityColumnSpace sys.a sys.B n) = n := by
    constructor
    · intro h_reach
      exact reachability_implies_full_finrank sys n h_dim hn h_reach
    · intro h_top
      exact full_finrank_implies_reachability sys n h_dim hn h_top
