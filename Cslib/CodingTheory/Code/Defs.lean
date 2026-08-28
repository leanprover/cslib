/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang, Alex Chai, Erin Jaen
-/

module

public import Cslib.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.InformationTheory.Hamming

/-!
# Codes

This file defines (block) codes and some basic properties.

A code of block length `n` over an alphabet `α` is a set of words `Fin n → α`, called its
codewords. Its main parameters are its dimension `log_q |C|` (where `q = |α|` is the size of
the alphabet, assumed finite), its rate `dim C / n`, its minimum distance (the least Hamming
distance between two distinct codewords) and its relative minimum distance `minDist C / n`.

## References

* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory* (draft, 2023),
  <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf>
-/

@[expose] public section

namespace Cslib.CodingTheory

open scoped ENNReal

/-- A *code* of block length `n` over the alphabet `α` is a set of words of length `n` over `α`;
its elements are the *codewords*. -/
abbrev Code (α : Type*) (n : ℕ) := Set (Fin n → α)

namespace Code

variable {α : Type*} {n : ℕ}

section MinDist

variable [DecidableEq α]

/-- The minimum distance of a code: the least Hamming distance between two distinct codewords.
It is `⊤` if the code has fewer than two codewords. -/
noncomputable def minDist (C : Code α n) : ℕ∞ :=
  ⨅ c₁ ∈ C, ⨅ c₂ ∈ C, ⨅ _ : c₁ ≠ c₂, (hammingDist c₁ c₂ : ℕ∞)

/-- The minimum distance is a lower bound for the distance between any two distinct codewords. -/
lemma minDist_le_hammingDist {C : Code α n} {c₁ c₂ : Fin n → α}
    (h₁ : c₁ ∈ C) (h₂ : c₂ ∈ C) (hne : c₁ ≠ c₂) :
    C.minDist ≤ (hammingDist c₁ c₂ : ℕ∞) := by
  unfold minDist
  exact (iInf₂_le c₁ h₁).trans <| (iInf₂_le c₂ h₂).trans (iInf_le _ hne)

/-- The minimum distance is the greatest lower bound for the distances between distinct
codewords. -/
lemma le_minDist {C : Code α n} {m : ℕ∞}
    (h : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → m ≤ (hammingDist c₁ c₂ : ℕ∞)) :
    m ≤ C.minDist := by
  simp only [minDist, le_iInf_iff]
  exact h

/-- The minimum distance of any code is at least `1`: distinct codewords are at positive
distance, and the empty infimum is `⊤`. -/
lemma one_le_minDist (C : Code α n) : 1 ≤ C.minDist :=
  le_minDist fun c₁ _ c₂ _ hne => by
    have : hammingDist c₁ c₂ ≠ 0 := fun h => hne (by simpa using h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

/-- The minimum distance is antitone: enlarging a code cannot increase its minimum distance. -/
lemma minDist_anti {C D : Code α n} (h : C ⊆ D) : D.minDist ≤ C.minDist :=
  le_minDist fun _ hc₁ _ hc₂ hne => minDist_le_hammingDist (h hc₁) (h hc₂) hne

/-- If `C` has minimum distance at least `d` and every codeword of `C` is at distance at least `d`
from the word `c`, then `insert c C` still has minimum distance at least `d`. -/
lemma le_minDist_insert {C : Code α n} {c : Fin n → α} {d : ℕ∞} (hC : d ≤ C.minDist)
    (hc : ∀ x ∈ C, d ≤ (hammingDist x c : ℕ∞)) : d ≤ minDist (insert c C) := by
  refine le_minDist fun c₁ hc₁ c₂ hc₂ hne => ?_
  rcases Set.mem_insert_iff.mp hc₁ with rfl | h₁
  · rcases Set.mem_insert_iff.mp hc₂ with rfl | h₂
    · exact absurd rfl hne
    · rw [hammingDist_comm]
      exact hc c₂ h₂
  · rcases Set.mem_insert_iff.mp hc₂ with rfl | h₂
    · exact hc c₁ h₁
    · exact hC.trans (minDist_le_hammingDist h₁ h₂ hne)

/-- The minimum distance of a code `{x, y}` with two distinct codewords is `hammingDist x y`. -/
lemma minDist_pair {x y : Fin n → α} (hxy : x ≠ y) :
    minDist ({x, y} : Code α n) = hammingDist x y :=
  le_antisymm
    (minDist_le_hammingDist (Set.mem_insert x {y}) (Set.mem_insert_of_mem x rfl) hxy)
    (le_minDist <| by
      -- each codeword is `x` or `y`, and they are distinct
      rintro c₁ (rfl | rfl) c₂ (rfl | rfl) hne
      · exact absurd rfl hne
      · exact le_rfl
      · exact_mod_cast (hammingDist_comm _ _).le
      · exact absurd rfl hne)

/-- The relative minimum distance `minDist C / n` of a code, as an element of `ℝ≥0∞`. -/
noncomputable def relMinDist (C : Code α n) : ℝ≥0∞ := (C.minDist : ℝ≥0∞) / n

end MinDist

section Dim

variable [Fintype α]

/-- The dimension `log_q |C|` of a code (a real number), where `q = |α|` is the size of the
alphabet. -/
noncomputable def dim (C : Code α n) : ℝ := Real.logb (Fintype.card α) C.ncard

/-- The rate `dim C / n` of a code (with the convention that it is `0` if `n = 0`). -/
noncomputable def rate (C : Code α n) : ℝ := C.dim / n

/-- The dimension of a code is at most its block length. -/
lemma dim_le_n (C : Code α n) : C.dim ≤ n := by
  obtain h0 | hpos := Nat.eq_zero_or_pos C.ncard
  · -- the empty code: `dim C = logb q 0 = 0`
    simp [dim, h0]
  obtain hq | hq := Nat.lt_or_ge (Fintype.card α) 2
  · -- degenerate alphabet: the base of the logarithm is `0` or `1`, so `dim C = 0`
    rcases (by omega : Fintype.card α = 0 ∨ Fintype.card α = 1) with h | h <;> simp [dim, h]
  · -- `2 ≤ q`: apply `logb q` to `|C| ≤ q ^ n`
    have hq1 : (1 : ℝ) < Fintype.card α := by exact_mod_cast hq
    have hcard : (C.ncard : ℝ) ≤ (Fintype.card α : ℝ) ^ n := by
      have h := Set.ncard_le_ncard (Set.subset_univ C)
      simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
        Fintype.card_fin] at h
      exact_mod_cast h
    calc C.dim ≤ Real.logb (Fintype.card α) ((Fintype.card α : ℝ) ^ n) :=
          Real.logb_le_logb_of_le hq1 (by exact_mod_cast hpos) hcard
      _ = n := by rw [Real.logb_pow, Real.logb_self_eq_one hq1, mul_one]

/-- The rate of a code is at most `1`. -/
lemma rate_le_one (C : Code α n) : C.rate ≤ 1 :=
  div_le_one_of_le₀ C.dim_le_n (by positivity)

end Dim

end Code

end Cslib.CodingTheory
