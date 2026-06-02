/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.Ackermann
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Topology.Algebra.Order.Floor

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Peel
public import Mathlib.Tactic.Bound

public import Cslib.Foundations.Lint.Basic

/-!
# Asymptotic Growth Rates

## Named Growth Rates

This file collects about common "growth rates" that show up in complexity theory. While
`IsBigO` expresses growth rate up to a multiplicative constant, there are other important
classes not directly expressible as `IsBigO`. In rough order of literature frequency:
 * `GrowthRate.poly`: Polynomial growth, typically written `poly(n)` or `n ^ O(1)`.
 * `GrowthRate.polylog`: `(log n)^k`, that is, a polynomial in the logarithm.
 * `GrowthRate.exp`: Exponential growth with any rate, often written `exp(O(n))`
 * `GrowthRate.sublinear`: Sublinear growth, typically written `o(n)`.
 * `GrowthRate.quasilinear`: Growth as `O(n * (log n)^k)`
 * `GrowthRate.quasipoly`: Growth as `O(2 ^ (log n)^k)`
 * `GrowthRate.primitiveRecursive`: Growth as a primitive recursive function.
 * `GrowthRate.computable`: Any computable function. This excludes, for instance, the Busy
    Beaver function.

These are all given as a `GrowthRate := Set (ℕ → ℕ)`. We have `GrowthRate.bigO` as a thin wrapper
around `Asymptotics.IsBigO`, likewise for `littleO`.

We also provide aliases for some of the more common Big-O classes, in order to work
with them more cleanly.
 * `GrowthRate.const`: O(1)
 * `GrowthRate.log`: O(log n)
 * `GrowthRate.sqrt`: O(sqrt n)
 * `GrowthRate.linear`: O(n)
 * `GrowthRate.linearithmic`: O(n * log n)
 * `GrowthRate.twoPow`: O(2 ^ n)
 * `GrowthRate.ePow`: O(Real.exp n)

Where they involve functions with different definitions on
distinct types (e.g. `Nat.sqrt` vs. `Real.sqrt`, or `(2 : ℕ) ^ ·` vs. `(2 : ℝ) ^ .`), we
want to have both forms.

Since all of these rates are `Set`s, their ordering of "faster growth" is given by the
subset relation `⊆`. That is, where you might want to write `f ≤ g` where `f` and `g`
are growth rates, this is best written as `f ⊆ g`.

## Lawful Growth Rates

We call a `GrowthRate` *lawful* if it is closed under dominating sequences, addition, and
composition with a sublinear function; and is nontrivial (it contains at least one function
besides zero).

This last condition is equivalent to containing the constant function 1; or, containing any
two distinct functions. These conditions are enough to get most desirable properties, and all
of above have `LawfulGrowthRate` instances. This allows reusable proofs for many common properties,
such as invariance under affine scaling.

## Main Theorems

Most theorems in this file fall into one of three categories:
 * Equivalent definitions. Sometimes it's more convenient to have expressions as `ℕ → ℕ`,
 sometimes it's more convenient to work with real numbers. (For instance, `e ^ n`, or different
 bases of logarithms.) For instance, `GrowthRate.log_iff_rlog` relates `GrowthRate.log` to the
 real function `Real.log`, instead of its definition in terms of `Nat.log 2`.
 * Ordering. For instance, `GrowthRate.exp_ssubset_primitiveRecursive` shows that `exp` is a strict
   subset of `primitiveRecursive`.
 * Closure properties. For instance, `GrowthRate.linear_comp` says that any LawfulGrowthRate is
   closed under composition with any function `f ∈ GrowthRate.linear`. `GrowthRate.poly_comp` says
   that `GrowthRate.poly` is closed under composition. And `GrowthRate.exp_mul` says that
   `GrowthRate.exp` is closed under multiplication.

-/

@[expose] public section

namespace CSLib

open scoped Topology

/-- A **Growth rate** is just any collection of `ℕ → ℕ`, but as a type alias intended for
discussing how quickly certain classes functions grow, as is often needed in asymptotic runtime
or memory analysis in computational complexity theory. A `LawfulGrowthRate` instance puts
constraints on this set behaving well in various ways.
-/
abbrev GrowthRate := Set (ℕ → ℕ)

namespace GrowthRate

/-- The `GrowthRate` corresponding to `O(f)` in Landau notation. -/
def bigO (g : ℕ → ℕ) : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =O[.atTop] (g · : ℕ → ℤ)

/-- The `GrowthRate` corresponding to `o(f)` in Landau notation. -/
def littleO (g : ℕ → ℕ) : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =o[.atTop] (g · : ℕ → ℤ)

--Most named growth rates are defined in `Cslib.Algorithms.GrowthRate.Named.lean`, but these
-- are important enough to immediately have consequences for (e.g.) `LawfulGrowthRate` instances,
-- so we define them here.

/-- Constant growth rates: `O(1)` -/
abbrev const := bigO 1

/-- Sublinear growth rates: `o(n)` -/
abbrev sublinear := littleO id

/-- Linear growth rates: `O(n)` -/
abbrev linear := bigO id

/-- Constant functions are in the `GrowthRate.const` class. -/
theorem const_mem_const (k : ℕ) : (fun _ ↦ k) ∈ GrowthRate.const := by
  simp only [const, bigO, Pi.one_apply, Nat.cast_one, Asymptotics.isBigO_one_iff]
  use k
  simp

variable {f g a b : ℕ → ℕ}

/--
If a function `f : ℕ → ℕ` has constant growth rate (i.e., is O(1)), then it is bounded by some
constant `C`.
-/
lemma bounded_of_const (h : f ∈ GrowthRate.const) : ∃ C, ∀ n, f n ≤ C := by
  have ⟨C, hC⟩ := h.exists_nonneg
  simp_all only [Pi.one_apply, Nat.cast_one, Asymptotics.IsBigOWith, norm_natCast,
    norm_one, mul_one, Filter.eventually_atTop]
  refine ⟨⌊C⌋₊ + ∑ n ∈ .range hC.2.choose, f n, fun n ↦ ?_⟩
  by_cases hn : n < hC.2.choose
  · exact le_add_of_nonneg_of_le (Nat.zero_le _)
      (Finset.single_le_sum (fun x _ ↦ Nat.zero_le (f x)) (Finset.mem_range.mpr hn))
  · exact le_add_of_le_of_nonneg (Nat.le_floor <| hC.2.choose_spec n (le_of_not_gt hn))
      (Nat.zero_le _)

theorem comp_const (f) (hg : g ∈ const) : f ∘ g ∈ const := by
  have ⟨C, hC⟩ := bounded_of_const hg
  have ⟨M, hM⟩ : ∃ M, ∀ n, f (g n) ≤ M := by
    use (Finset.range (C + 1)).sup f
    exact fun n ↦ Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le (hC n)))
  apply Asymptotics.isBigO_iff.mpr
  use M
  filter_upwards [Filter.eventually_ge_atTop 0] with n hn
  simpa [hn] using hM n

theorem const_comp (hf : f ∈ const) (g) : f ∘ g ∈ const := by
  have ⟨C, hC⟩ := bounded_of_const hf
  norm_num [const, Asymptotics.isBigO_iff, bigO]
  use C, 0
  exact fun _ _ ↦ mod_cast (hC _)

theorem bigO_add (hf : f ∈ bigO a) (hg : g ∈ bigO b) :
    f + g ∈ bigO (a + b) := by
  rw [bigO] at *
  simp only [Asymptotics.IsBigO, Set.mem_setOf_eq, Pi.add_apply, Nat.cast_add] at *
  simp only [Asymptotics.IsBigOWith, norm_natCast, Filter.eventually_atTop] at *
  norm_num [Norm.norm]
  rcases hf with ⟨c₁, a₁, h₁⟩
  rcases hg with ⟨c₂, a₂, h₂⟩
  use c₁ ⊔ c₂, a₁ ⊔ a₂
  intro n hn
  rw [abs_of_nonneg, abs_of_nonneg]
  · nlinarith [h₁ n (le_trans (le_max_left _ _) hn), h₂ n (le_trans (le_max_right _ _) hn),
      le_max_left c₁ c₂, le_max_right c₁ c₂, Nat.zero_le (a n), Nat.zero_le (b n)]
  · nlinarith [Nat.zero_le (a n), Nat.zero_le (b n)]
  · nlinarith [Nat.zero_le (f n), Nat.zero_le (g n)]

end GrowthRate

/-- We call a `GrowthRate` *lawful* if it is closed under dominating sequences, addition, and
composition with a sublinear function; and is nontrivial (it contains at least one function besides
zero).

This last condition is equivalent to containing the constant function 1; or, containing any
two distinct functions. These conditions are enough to get most desirable properties. For instance,
all big-O and little-O rates are lawful, as is `poly`. -/
class LawfulGrowthRate (S : GrowthRate) : Prop where
  /-- If a function `f` is in S and it dominates `g` (is eventually no less), then `g ∈ S`. -/
  mem_dominating {f g : ℕ → ℕ} : (∀ᶠ x in .atTop, g x ≤ f x) → (f ∈ S) → g ∈ S
  /-- S is closed under addition. -/
  mem_add {f g : ℕ → ℕ} : (f ∈ S) → (g ∈ S) → (f + g ∈ S)
  /-- If a function `f` is in S and `g` is sublinear, then `f ∘ g ∈ S`. -/
  comp_le_id {f g : ℕ → ℕ} (hf : f ∈ S) (hg : g ≤ id) : f ∘ g ∈ S
  /-- S contains the constant function 1. -/
  one_mem : 1 ∈ S

namespace GrowthRate

--Basic facts about lawful growth rates.
section lawful

alias mem_dominating := LawfulGrowthRate.mem_dominating
alias add := LawfulGrowthRate.mem_add
alias comp_le_id' := LawfulGrowthRate.comp_le_id
alias one_mem := LawfulGrowthRate.one_mem

variable {f g : ℕ → ℕ} {S : GrowthRate} [LawfulGrowthRate S]

theorem comp_le_id (hf : f ∈ S) (hg : ∀ x, g x ≤ x) : f ∘ g ∈ S :=
  comp_le_id' hf hg

theorem mono (hf : f ∈ S) (hg : g ≤ f) : g ∈ S :=
  mem_dominating (.of_forall hg) hf

instance : Nonempty S :=
  ⟨1, one_mem (S := S)⟩

theorem zero_mem : 0 ∈ S := by
  have ⟨f, hf⟩ := Classical.inhabited_of_nonempty (α := S) inferInstance
  convert mem_dominating _ hf
  exact Filter.Eventually.of_forall fun _ ↦ Nat.zero_le _

instance : Nontrivial S :=
  ⟨⟨0, zero_mem⟩, ⟨1, one_mem⟩, by simp⟩

theorem const_mem (hf : f ∈ const) : f ∈ S := by
  have ⟨C, hC⟩ := bounded_of_const hf
  suffices h : (fun n ↦ C * 1) ∈ S from mem_dominating (by simp [hC]) h
  clear hC
  induction C
  · exact mem_dominating (by norm_num) one_mem
  · rename_i ih
    simp only [mul_one] at ih ⊢
    exact add ih one_mem

theorem sub (hf : f ∈ S) (g) : f - g ∈ S := by
  apply mem_dominating ?_ hf
  rw [Filter.eventually_atTop]
  exact ⟨0, fun _ _ ↦ (Nat.cast_le.mpr <| Nat.sub_le ..)⟩

theorem mul_const (hf : f ∈ S) (hg : g ∈ const) : (f * g) ∈ S := by
  have ⟨C, hC⟩ := bounded_of_const hg
  apply mem_dominating (f := C * f)
  · rw [Filter.eventually_atTop]
    refine ⟨0, fun n hn ↦ ?_⟩
    simp only [Pi.mul_apply, Pi.natCast_apply, Nat.cast_id]
    grw [← hC n, mul_comm]
  · clear hC
    induction C <;> simp [zero_mem, add_mul, add, *]

theorem const_mul (hf : f ∈ const) (hg : g ∈ S) : (f * g) ∈ S := by
  rw [mul_comm]
  exact mul_const hg hf

/-- If `f` has growth rate `S` and `g` has is `sublinear`, then `f ∘ g` has growth rate `S`.
With the written assumptions on `LawfulGrowthRate`, this is doesn't hold if we use `linear` instead
of `sublinear`. Consider the case `S := O(2^n)` and `g := 2n`. Then `2^(2n) = 4^n` which is not in
 `O(2^n)`. -/
theorem comp_sublinear (hf : f ∈ S) (hg : g ∈ sublinear) : f ∘ g ∈ S := by
  have ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, g n ≤ n := by
    simpa using hg.def zero_lt_one
  apply mem_dominating (f := f ∘ (fun n ↦ if n ≥ N then g n else n))
  · filter_upwards [Filter.eventually_ge_atTop N] with n hn
    simp [hn]
  · apply comp_le_id' hf
    intro n
    beta_reduce
    split_ifs with h
    · exact hN n h
    · exact le_refl _

theorem comp_sub_nat (hf : f ∈ S) (k : ℕ) : (fun n ↦ f (n - k)) ∈ S :=
  comp_le_id hf (by simp)

theorem comp_eventually_le_id (hf : f ∈ S) (hg : ∀ᶠ x in .atTop, g x ≤ x) : f ∘ g ∈ S := by
  apply mem_dominating (f := f ∘ (fun x ↦ min (g x) x))
  · filter_upwards [hg] with x hx
    simp [min_eq_left hx]
  · exact comp_le_id' hf (fun x ↦ min_le_right _ _)

/-- Any LawfulGrowthRate is closed under linear transformation on the output. -/
theorem linear_comp (hf : f ∈ linear) (hg : g ∈ S) : f ∘ g ∈ S := by
  have ⟨C, hC⟩ : ∃ C : ℕ, ∀ n, f n ≤ C * (n + 1) := by
    have ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * n := by
      have ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hf
      have ⟨N, hN⟩ := Filter.eventually_atTop.mp hC
      refine ⟨⌈C⌉₊, N, fun n hn ↦ ?_⟩
      specialize hN n hn; norm_num [Norm.norm] at hN
      exact_mod_cast hN.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) <| Nat.cast_nonneg _)
    refine ⟨C ⊔ (Finset.range N).sup f, fun n ↦ ?_⟩
    rcases lt_or_ge n N with hn | hn
    · grw [← le_max_right, ← Finset.le_sup (Finset.mem_range.mpr hn)]
      lia
    · grw [← le_max_left, hC n hn]
      lia
  have h_linear (C : ℕ) : C * (g + 1) ∈ S := by
    induction C
    · simp only [Nat.cast_zero, zero_mul]
      exact zero_mem
    · simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      exact add ‹_› (add hg one_mem)
  exact mem_dominating (Filter.Eventually.of_forall (by simpa using hC <| g ·)) (h_linear C)

/-- LawfulGrowthRate is closed under linear transformations. -/
lemma affine_comp {f : ℕ → ℕ} {a b : ℕ} (hf : f ∈ S) :
    (fun n ↦ a * f n + b) ∈ S :=
  add (const_mul (const_mem_const a) hf) (const_mem (const_mem_const b))

section instances

/-- We can show that `bigO f` is a `LawfulGrowthRate` if it satisfies two mild conditions:
f is positive at some point, and it's closed under composition with sub-identity functions. -/
@[implicit_reducible]
def instLawfulBigO
      (hf : ∃ a, ∀ (b : ℕ), a ≤ b → 0 < f b)
      (hf₂ : ∀ k ∈ bigO f, ∀ g ≤ id, k ∘ g ∈ bigO f) :
    LawfulGrowthRate (bigO f) where
  mem_dominating h hf := by
    simp only [bigO, Asymptotics.isBigO_iff, Int.norm_natCast, Filter.eventually_atTop] at h hf ⊢
    rcases h with ⟨a₁, hf₁⟩
    rcases hf with ⟨c, a₂, hg⟩
    refine ⟨c, a₁ ⊔ a₂, fun b hb ↦ ?_⟩
    grw [hf₁, hg]
    · exact le_of_max_le_right hb
    · exact le_of_max_le_left hb
  mem_add hf hg := hf.add hg
  one_mem := by
    simp_rw [bigO, Asymptotics.isBigO_iff]
    use 1
    simpa using hf
  comp_le_id hf hg := hf₂ _ hf _ hg

/-- We can show that `littleO f` is a `LawfulGrowthRate` if it satisfies two mild conditions:
f dominates the constant function 1, and it's closed under composition with
sub-identity functions. -/
@[implicit_reducible]
def instLawfulLittleO (hf : 1 ∈ littleO f)
  (hf₂ : ∀ k g, k ∈ littleO f → (∀ x, g x ≤ x) → (k ∘ g) ∈ littleO f) :
    LawfulGrowthRate (littleO f) where
  mem_dominating h hf := by
    simp only [Filter.eventually_atTop, littleO, Asymptotics.isLittleO_iff, Int.norm_natCast]
      at h hf ⊢
    intro c₀ hc₀
    rcases h with ⟨a₁, hf₁⟩
    have ⟨a₂, hg⟩ := hf hc₀
    refine ⟨a₁ ⊔ a₂, fun b hb ↦ ?_⟩
    grw [hf₁, hg]
    · exact le_of_max_le_right hb
    · exact le_of_max_le_left hb
  mem_add hf hg := hf.add hg
  one_mem := hf
  comp_le_id := hf₂ _ _

instance : LawfulGrowthRate const := by
  apply instLawfulBigO
  · simp
  · exact fun k a g a_1 ↦ const_comp a g

end instances
end lawful

end GrowthRate

end CSLib
