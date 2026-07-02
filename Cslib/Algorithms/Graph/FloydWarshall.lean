/-
Copyright (c) 2026 Fawad Haider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Fawad Haider
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
# Floyd-Warshall

This file defines finite weighted directed graphs as min-plus matrices
`Fin n → Fin n → WithTop Nat` and proves the standard Floyd-Warshall invariant.

The theorem `phase_isShortestPathWeight` states that, after phase `k`, the entry
`phase w k i j` is the shortest weight among the restricted paths from `i` to `j`
whose direct edges are finite in `w` and whose intermediate vertices are
introduced by the first `k` phases.  The theorem
`RestrictedPath.mem_intermediates_lt` records the intended interpretation of the
phase index: every intermediate vertex of such a path has value `< k`, i.e. lies
in `{0, ..., k - 1}`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Graph.FloydWarshall

/-- Edge and path weights for Floyd-Warshall: finite natural costs plus infinity. -/
abbrev Weight := WithTop Nat

/-- A finite weighted directed graph, represented as a min-plus adjacency matrix. -/
abbrev Matrix (n : Nat) := Fin n → Fin n → Weight

/-- One Floyd-Warshall relaxation step through the pivot vertex `k`. -/
def step {n : Nat} (d : Matrix n) (k : Fin n) : Matrix n :=
  fun i j ↦ min (d i j) (d i k + d k j)

/--
The matrix after `k` Floyd-Warshall phases.

For `k ≤ n`, phase `k` has considered exactly the possible intermediate vertices
with values `< k`.  For `k > n`, the matrix remains stable.
-/
def phase {n : Nat} (w : Matrix n) : Nat → Matrix n
  | 0 => w
  | k + 1 =>
      if hk : k < n then
        step (phase w k) ⟨k, hk⟩
      else
        phase w k

/-- The all-pairs shortest-path matrix produced after all vertices have been considered. -/
def allPairsShortestPaths {n : Nat} (w : Matrix n) : Matrix n :=
  phase w n

/--
Input-graph-valid restricted paths used by the Floyd-Warshall invariant.

`RestrictedPath w k i j` is the family of paths from `i` to `j` generated after
the first `k` phases.  The constructor `edge` requires a finite edge in the input
matrix `w`; the constructor `through` is the Floyd-Warshall decomposition through
the newly available pivot vertex.
-/
inductive RestrictedPath {n : Nat} (w : Matrix n) : Nat → Fin n → Fin n → Type
  | edge {i j : Fin n} (h : w i j < ⊤) : RestrictedPath w 0 i j
  | keep {k : Nat} {i j : Fin n} :
      RestrictedPath w k i j → RestrictedPath w (k + 1) i j
  | through {k : Nat} {i j : Fin n} (hk : k < n) :
      RestrictedPath w k i ⟨k, hk⟩ →
      RestrictedPath w k ⟨k, hk⟩ j →
      RestrictedPath w (k + 1) i j

namespace RestrictedPath

/-- The min-plus weight of a restricted path. -/
def weight {n k : Nat} {w : Matrix n} {i j : Fin n} :
    RestrictedPath w k i j → Weight
  | @edge _ w i j _ => w i j
  | keep p => weight p
  | through _ p q => weight p + weight q

/-- The intermediate vertices of a restricted path, excluding its endpoints. -/
def intermediates {n k : Nat} {w : Matrix n} {i j : Fin n} :
    RestrictedPath w k i j → List (Fin n)
  | edge _ => []
  | keep p => intermediates p
  | @through _ _ k _ _ hk p q => intermediates p ++ [⟨k, hk⟩] ++ intermediates q

/-- Restricted paths have finite weight. -/
theorem weight_lt_top {n k : Nat} {w : Matrix n} {i j : Fin n}
    (p : RestrictedPath w k i j) :
    p.weight < ⊤ := by
  induction p with
  | edge h =>
      simpa [weight] using h
  | keep p ih =>
      simpa [weight] using ih
  | through _ p q ihp ihq =>
      simpa [weight] using And.intro ihp ihq

/--
All intermediate vertices of a `k`-restricted path lie among the first `k`
vertices.
-/
theorem mem_intermediates_lt {n k : Nat} {w : Matrix n} {i j v : Fin n}
    {p : RestrictedPath w k i j} (hv : v ∈ intermediates p) :
    v.val < k := by
  induction p with
  | edge =>
      simp [intermediates] at hv
  | keep p ih =>
      exact Nat.lt_trans (ih hv) (Nat.lt_succ_self _)
  | through hk p q ihp ihq =>
      rw [intermediates, List.mem_append] at hv
      rcases hv with hv | hvq
      · rw [List.mem_append] at hv
        rcases hv with hvp | hv
        · exact Nat.lt_trans (ihp hvp) (Nat.lt_succ_self _)
        · simp only [List.mem_singleton] at hv
          subst v
          exact Nat.lt_succ_self _
      · exact Nat.lt_trans (ihq hvq) (Nat.lt_succ_self _)

end RestrictedPath

/--
`d` is the shortest weight among the input-graph-valid restricted paths from `i` to `j`.

The first conjunct says that no restricted path has smaller weight.  The second
conjunct says that, if the shortest weight is finite, then the bound is attained
by an actual restricted path.
-/
def IsShortestPathWeight {n k : Nat} (w : Matrix n) (i j : Fin n) (d : Weight) :
    Prop :=
  (∀ p : RestrictedPath w k i j, d ≤ p.weight) ∧
    (d < ⊤ → ∃ p : RestrictedPath w k i j, p.weight = d)

@[simp]
theorem phase_zero {n : Nat} (w : Matrix n) : phase w 0 = w := rfl

@[simp]
theorem phase_succ_of_lt {n k : Nat} (w : Matrix n) (hk : k < n) :
    phase w (k + 1) = step (phase w k) ⟨k, hk⟩ := by
  simp [phase, hk]

@[simp]
theorem phase_succ_of_not_lt {n k : Nat} (w : Matrix n) (hk : ¬ k < n) :
    phase w (k + 1) = phase w k := by
  simp [phase, hk]

private theorem phase_succ_le_keep {n k : Nat} (w : Matrix n) (i j : Fin n) :
    phase w (k + 1) i j ≤ phase w k i j := by
  by_cases hk : k < n
  · simp [phase, step, hk]
  · simp [phase, hk]

private theorem phase_succ_le_through {n k : Nat} (w : Matrix n) (hk : k < n)
    (i j : Fin n) :
    phase w (k + 1) i j ≤ phase w k i ⟨k, hk⟩ + phase w k ⟨k, hk⟩ j := by
  simp [phase, step, hk]

/-- Every restricted path is bounded below by the corresponding Floyd-Warshall entry. -/
theorem phase_le_weight {n k : Nat} (w : Matrix n) {i j : Fin n}
    (p : RestrictedPath w k i j) :
    phase w k i j ≤ p.weight := by
  induction p with
  | edge =>
      simp [phase, RestrictedPath.weight]
  | keep p ih =>
      exact le_trans (phase_succ_le_keep w _ _) ih
  | through hk p q ihp ihq =>
      exact le_trans (phase_succ_le_through w hk _ _) (add_le_add ihp ihq)

/-- Each finite Floyd-Warshall entry is the weight of some restricted path. -/
theorem exists_weight_eq_phase_of_lt_top {n : Nat} (w : Matrix n) (k : Nat) :
    ∀ i j : Fin n, phase w k i j < ⊤ →
      ∃ p : RestrictedPath w k i j, p.weight = phase w k i j := by
  induction k with
  | zero =>
      intro i j h
      exact ⟨RestrictedPath.edge h, by simp [phase, RestrictedPath.weight]⟩
  | succ k ih =>
      intro i j h
      by_cases hk : k < n
      · let pivot : Fin n := ⟨k, hk⟩
        by_cases hle : phase w k i j ≤ phase w k i pivot + phase w k pivot j
        · have hKeep : phase w k i j < ⊤ := by
            have hmin :
                min (phase w k i j) (phase w k i pivot + phase w k pivot j) < ⊤ := by
              simpa [phase, step, hk, pivot] using h
            rwa [min_eq_left hle] at hmin
          obtain ⟨pKeep, hpKeep⟩ := ih i j hKeep
          refine ⟨RestrictedPath.keep pKeep, ?_⟩
          simp [RestrictedPath.weight, phase, step, hk, hpKeep]
          simpa [pivot] using hle
        · have hright : phase w k i pivot + phase w k pivot j ≤ phase w k i j :=
            le_of_not_ge hle
          have hThrough :
              phase w k i pivot + phase w k pivot j < ⊤ := by
            have hmin :
                min (phase w k i j) (phase w k i pivot + phase w k pivot j) < ⊤ := by
              simpa [phase, step, hk, pivot] using h
            rwa [min_eq_right hright] at hmin
          have hLeft : phase w k i pivot < ⊤ := (WithTop.add_lt_top.mp hThrough).1
          have hRight : phase w k pivot j < ⊤ := (WithTop.add_lt_top.mp hThrough).2
          obtain ⟨pLeft, hpLeft⟩ := ih i pivot hLeft
          obtain ⟨pRight, hpRight⟩ := ih pivot j hRight
          refine ⟨RestrictedPath.through hk pLeft pRight, ?_⟩
          simp [RestrictedPath.weight, phase, step, hk, hpLeft, hpRight]
          simpa [pivot] using (min_eq_right hright).symm
      · have hPrev : phase w k i j < ⊤ := by
          simpa [phase, hk] using h
        obtain ⟨pKeep, hpKeep⟩ := ih i j hPrev
        refine ⟨RestrictedPath.keep pKeep, ?_⟩
        simp [RestrictedPath.weight, phase, hk, hpKeep]

/--
Floyd-Warshall phase invariant.

After phase `k`, each matrix entry is the shortest weight among the paths whose
intermediate vertices are available in the first `k` phases.
-/
theorem phase_isShortestPathWeight {n : Nat} (w : Matrix n) (k : Nat) (i j : Fin n) :
    IsShortestPathWeight (n := n) (k := k) w i j (phase w k i j) :=
  ⟨fun p ↦ phase_le_weight w p, exists_weight_eq_phase_of_lt_top w k i j⟩

/-- The final Floyd-Warshall matrix gives shortest restricted paths using all vertices. -/
theorem allPairsShortestPaths_isShortestPathWeight {n : Nat} (w : Matrix n) (i j : Fin n) :
    IsShortestPathWeight (n := n) (k := n) w i j (allPairsShortestPaths w i j) :=
  phase_isShortestPathWeight w n i j

/--
Warshall-style reachability corollary: the phase entry is finite exactly when
there exists a finite-weight restricted path.
-/
theorem phase_lt_top_iff_exists_weight_lt_top {n k : Nat} (w : Matrix n) (i j : Fin n) :
    phase w k i j < ⊤ ↔
      ∃ p : RestrictedPath w k i j, p.weight < ⊤ := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_weight_eq_phase_of_lt_top w k i j h
    exact ⟨p, by simpa [hp] using h⟩
  · rintro ⟨p, hp⟩
    exact lt_of_le_of_lt (phase_le_weight w p) hp

/-- Final reachability corollary for the all-pairs matrix. -/
theorem allPairsShortestPaths_lt_top_iff_exists_weight_lt_top {n : Nat}
    (w : Matrix n) (i j : Fin n) :
    allPairsShortestPaths w i j < ⊤ ↔
      ∃ p : RestrictedPath w n i j, p.weight < ⊤ :=
  phase_lt_top_iff_exists_weight_lt_top w i j

end Cslib.Algorithms.Graph.FloydWarshall
