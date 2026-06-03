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
 * `GrowthRate.nearLinear`: Near-linear growth as `O(n * (log n)^k)`
 * `GrowthRate.almostLinear`: Almost-linear growth as `O(n ^ {1 + ε})` for every `ε > 0`.
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

/-! ### Operations on Growth Rates
We define addition, multiplication, and exponentiation of growth rates as the
downward closure of the corresponding pointwise operations. That is, for growth
rates `A` and `B`, the sum `A.gadd B` is not just `{f + g | f ∈ A, g ∈ B}` but
rather the set of all functions pointwise bounded by some `f + g`. -/

section operations

/-- Addition of growth rates: the set of all functions bounded pointwise by `f + g`
for some `f ∈ A` and `g ∈ B`. -/
def gadd (A B : GrowthRate) : GrowthRate :=
  {h | ∃ f ∈ A, ∃ g ∈ B, h ≤ f + g}

instance : Add GrowthRate := ⟨GrowthRate.gadd⟩

/-- Multiplication of growth rates: the set of all functions bounded pointwise by `f * g`
for some `f ∈ A` and `g ∈ B`. -/
protected def gmul (A B : GrowthRate) : GrowthRate :=
  {h | ∃ f ∈ A, ∃ g ∈ B, h ≤ f * g}

instance : Mul GrowthRate := ⟨GrowthRate.gmul⟩

/-- Exponentiation of growth rates: the set of all functions bounded pointwise by
`f(x) ^ g(x)` for some `f ∈ A` and `g ∈ B`. -/
protected def gpow (A B : GrowthRate) : GrowthRate :=
  {h | ∃ f ∈ A, ∃ g ∈ B, h ≤ fun x => f x ^ g x}

instance : HomogeneousPow GrowthRate := ⟨GrowthRate.gpow⟩

variable {A B C S : GrowthRate} {f g h : ℕ → ℕ}

theorem mem_add : h ∈ A + B ↔ ∃ f ∈ A, ∃ g ∈ B, h ≤ f + g :=
  Iff.rfl

theorem mem_mul : h ∈ A * B ↔ ∃ f ∈ A, ∃ g ∈ B, h ≤ f * g :=
  Iff.rfl

theorem mem_pow : h ∈ A ^ B ↔ ∃ f ∈ A, ∃ g ∈ B, h ≤ fun x => f x ^ g x :=
  Iff.rfl

/-- Addition of growth rates is commutative. -/
theorem gadd_comm : A + B = B + A := by
  simp only [Set.ext_iff, mem_add]
  conv in _ + _ => rw [add_comm]
  grind only

/-- Addition of growth rates is associative. -/
theorem gadd_assoc : (A + B) + C = A + (B + C) := by
  ext h
  constructor
  · rintro ⟨f, ⟨a, ha, b, hb, hab⟩, c, hc, h_le⟩
    exact ⟨a, ha, fun x => b x + c x, ⟨b, hb, c, hc, le_rfl⟩,
      fun x => le_trans (h_le x) (by have := Nat.add_le_add_right (hab x); simp at this ⊢; grind)⟩
  · rintro ⟨f, hf, g, ⟨b, hb, c, hc, hle'⟩, hle⟩
    exact ⟨f + b, ⟨f, hf, b, hb, le_refl _⟩, c, hc,
      fun x => le_trans (hle x) (by have := Nat.add_le_add_left (hle' x); simp at this ⊢; grind)⟩

instance : AddCommSemigroup GrowthRate where
  add_comm := @gadd_comm
  add_assoc := @gadd_assoc

/-- Multiplication of growth rates is commutative. -/
theorem gmul_comm : A * B = B * A := by
  simp only [Set.ext_iff, mem_mul]
  conv in _ * _ => rw [mul_comm]
  grind only

/-- Multiplication of growth rates is associative. -/
theorem gmul_assoc : (A * B) * C = A * (B * C) := by
  ext h
  constructor
  · rintro ⟨f, ⟨a, ha, b, hb, hab⟩, c, hc, h_le⟩
    refine ⟨a, ha, fun x => b x * c x, ⟨b, hb, c, hc, le_rfl⟩, fun x => ?_⟩
    have := h_le x
    have := hab x
    simp at *
    nlinarith
  · rintro ⟨f, hf, g, ⟨b, hb, c, hc, hle'⟩, hle⟩
    refine ⟨f * b, ⟨f, hf, b, hb, le_rfl⟩, c, hc, fun x => ?_⟩
    have := hle x
    have := hle' x
    simp only [Pi.mul_apply] at *
    nlinarith

instance : CommSemigroup GrowthRate where
  mul_comm _ _ := gmul_comm
  mul_assoc _ _ _ := gmul_assoc

theorem gmul_gadd_le : A * (B + C) ≤ (A * B) + (A * C) := by
  intro h
  rintro ⟨a, ha, g, ⟨b, hb, c, hc, hle'⟩, hle⟩
  exact ⟨fun x => a x * b x, ⟨a, ha, b, hb, le_refl _⟩,
    fun x => a x * c x, ⟨a, ha, c, hc, le_refl _⟩,
    fun x => by
      dsimp
      grind [hle x, Pi.mul_apply, Nat.mul_le_mul_left (a x) (hle' x), Pi.add_apply, left_distrib]⟩

theorem gmul_gadd_gmul_le : (A * B) + (A * C) ≤ (A + A) * (B + C) := by
  intro h
  rintro ⟨p, ⟨a₁, ha₁, b, hb, hle1⟩, q, ⟨a₂, ha₂, c, hc, hle2⟩, hle⟩
  refine ⟨a₁ + a₂, ⟨a₁, ha₁, a₂, ha₂, le_rfl⟩, b + c, ⟨b, hb, c, hc, le_rfl⟩, fun x => ?_⟩
  have := hle x; have := hle1 x; have := hle2 x
  simp only [Pi.add_apply, Pi.mul_apply] at *
  nlinarith

--We can't have a Distrib instance in general. We have that
--  A * (B + C) ≤ (A * B) + (A * C) ≤ (A + A) * (B + C)
--but we can't generically tighten this without a LawfulGrowthRate instance.

/-- Addition of growth rates is monotone in the right argument. -/
theorem gadd_mono_right (h : A ⊆ B) : C + A ⊆ C + B := by
  intro f hf
  obtain ⟨a, ha, b, hb, hle⟩ := hf
  exact ⟨a, ha, b, h hb, hle⟩

--We use AddLeftMono and AddRightMono instead of IsOrderedAddMonoid because we don't have an
-- additive identity.

instance : AddLeftMono GrowthRate where
  elim _ _ _ := gadd_mono_right

instance : AddRightMono GrowthRate :=
  addRightMono_of_addLeftMono _

theorem add_congr (hf : f ∈ A) (hg : g ∈ B) : (f + g) ∈ A + B :=
  ⟨f, hf, g, hg, le_refl _⟩

theorem mul_congr (hf : f ∈ A) (hg : g ∈ B) : (f * g) ∈ A * B :=
  ⟨f, hf, g, hg, le_refl _⟩

theorem pow_congr (hf : f ∈ A) (hg : g ∈ B) : (fun x ↦ f x ^ g x) ∈ A ^ B :=
  ⟨f, hf, g, hg, le_refl _⟩

/-! #### Lawful instances for growth rate operations -/

variable [LawfulGrowthRate A] [LawfulGrowthRate B]

omit [LawfulGrowthRate B] in
private lemma gadd_mem_dominating (hle : ∀ᶠ x in .atTop, g x ≤ f x) (hf : f ∈ A + B) :
    g ∈ A + B := by
  obtain ⟨a, ha, b, hb, hle'⟩ := hf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hle
  set a' : ℕ → ℕ := fun n => a n + (Finset.range N).sup g
  have ha' : a' ∈ A := by
    have h_const : ∀ k : ℕ, (fun _ => k) ∈ A := by
      intro k; induction k with
      | zero => exact mem_dominating (Filter.Eventually.of_forall fun _ => Nat.zero_le _) one_mem
      | succ k ih => exact add ih one_mem
    exact add ha (h_const _)
  exact ⟨a', ha', b, hb, fun n => by
    by_cases hn : n < N
    · exact le_add_of_le_of_nonneg
        (le_add_of_nonneg_of_le (Nat.zero_le _)
          (Finset.le_sup (f := g) (Finset.mem_range.mpr hn))) (Nat.zero_le _)
    · exact le_trans (hN n (not_lt.mp hn)) (le_trans (hle' n) (by simp [a']))⟩

instance : LawfulGrowthRate (A + B) where
  mem_dominating := gadd_mem_dominating
  mem_add := fun ⟨a₁, ha₁, b₁, hb₁, h₁⟩ ⟨a₂, ha₂, b₂, hb₂, h₂⟩ ↦
    ⟨_, add ha₁ ha₂, _, add hb₁ hb₂, fun x ↦ by
      rw [add_add_add_comm]; exact add_le_add (h₁ x) (h₂ x)⟩
  comp_le_id := fun ⟨a, ha, b, hb, hle⟩ hg ↦
    ⟨_, comp_le_id' ha hg, _, comp_le_id' hb hg, fun _ ↦ hle _⟩
  one_mem := ⟨1, one_mem, 1, one_mem, fun _ ↦ by simp⟩

private lemma gmul_mem_dominating (hle : ∀ᶠ x in .atTop, g x ≤ f x) (hf : f ∈ A * B) :
    g ∈ A * B := by
  obtain ⟨a, ha, b, hb, hle'⟩ := hf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hle
  have h_const : ∀ k : ℕ, (fun _ => k) ∈ A := by
    intro k; induction k with
    | zero => exact mem_dominating (Filter.Eventually.of_forall fun _ => Nat.zero_le _) one_mem
    | succ k ih => exact LawfulGrowthRate.mem_add ih one_mem
  refine ⟨a + (fun _ => (Finset.range N).sup g), LawfulGrowthRate.mem_add ha (h_const _),
    b + (fun _ => 1), LawfulGrowthRate.mem_add hb one_mem, fun x => ?_⟩
  by_cases hx : x < N
  · simp only [Pi.mul_apply, Pi.add_apply]
    nlinarith [Finset.le_sup (f := g) (Finset.mem_range.mpr hx), hle' x]
  · specialize hN x (not_lt.mp hx)
    specialize hle' x
    simp only [Pi.mul_apply, Pi.add_apply] at ⊢ hle'
    lia

private lemma gmul_mem_add' (hf : f ∈ A * B) (hg : g ∈ A * B) :
    f + g ∈ A * B := by
  obtain ⟨a₁, ha₁, b₁, hb₁, h₁⟩ := hf
  obtain ⟨a₂, ha₂, b₂, hb₂, h₂⟩ := hg
  refine ⟨_, add ha₁ ha₂, _, add hb₁ hb₂, fun i => ?_⟩
  specialize h₁ i
  specialize h₂ i
  simp only [Pi.mul_apply, Pi.add_apply] at ⊢ h₁ h₂
  lia

instance : LawfulGrowthRate (A * B) where
  mem_dominating := gmul_mem_dominating
  mem_add := gmul_mem_add'
  comp_le_id := fun ⟨a, ha, b, hb, hle⟩ hg ↦
    ⟨_, comp_le_id' ha hg, _, comp_le_id' hb hg, fun _ ↦ (hle _).trans (by simp)⟩
  one_mem := ⟨1, one_mem, 1, one_mem, by simp⟩

private lemma gpow_mem_dominating (hle : ∀ᶠ x in .atTop, g x ≤ f x) (hf : f ∈ A ^ B) :
    g ∈ A ^ B := by
  obtain ⟨a, ha, b, hb, hle'⟩ := hf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hle
  set M := Finset.sup (Finset.range N) g
  have h_add : ∀ (k : ℕ), (fun n => a n + k) ∈ A := by
    intro k; induction k with
    | zero => simpa using ha
    | succ k ih =>
      convert add ih one_mem using 1
  refine ⟨fun n => a n + (M + 1), h_add _, fun n => b n + 1, add hb one_mem, fun n => ?_⟩
  by_cases hn : n < N
  · simp only
    rw [pow_succ]
    have := Finset.le_sup (f := g) (Finset.mem_range.mpr hn)
    have := pow_pos (show 0 < a n + (M + 1) by linarith) (b n)
    nlinarith
  · calc g n ≤ f n := hN n (not_lt.mp hn)
      _ ≤ a n ^ b n := hle' n
      _ ≤ (a n + (M + 1)) ^ b n :=
        Nat.pow_le_pow_left (Nat.le_add_right _ _) _
      _ ≤ (a n + (M + 1)) ^ b n * (a n + (M + 1)) :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      _ = (a n + (M + 1)) ^ (b n + 1) := by ring

private lemma gpow_mem_add' (hf : f ∈ A ^ B) (hg : g ∈ A ^ B) :
    f + g ∈ A ^ B := by
  obtain ⟨a₁, ha₁, b₁, hb₁, h₁⟩ := hf
  obtain ⟨a₂, ha₂, b₂, hb₂, h₂⟩ := hg
  -- Use F = a₁ + a₂ + 2 ∈ A, G = b₁ + b₂ + 2 ∈ B, then f + g ≤ F^(G+1)
  set F := a₁ + a₂ + 2 with hF_def
  set G := b₁ + b₂ + 2 with hG_def
  have hF : F ∈ A := add (add ha₁ ha₂) (add one_mem one_mem)
  have hG : G ∈ B := add (add hb₁ hb₂) (add one_mem one_mem)
  have hG1 : G + 1 ∈ B := add hG one_mem
  refine ⟨F, hF, G + 1, hG1, fun x => ?_⟩
  simp only [hF_def, hG_def, Pi.add_apply, Pi.ofNat_apply] at *
  calc f x + g x
      ≤ a₁ x ^ b₁ x + a₂ x ^ b₂ x := Nat.add_le_add (h₁ x) (h₂ x)
    _ ≤ (a₁ x + a₂ x + 2) ^ (b₁ x + b₂ x + 2) +
        (a₁ x + a₂ x + 2) ^ (b₁ x + b₂ x + 2) := by
        apply Nat.add_le_add
        · grw [Nat.pow_le_pow_left (m := (a₁ x + a₂ x + 2)) (by omega)]
          exact Nat.pow_le_pow_of_le (by omega) (by omega)
        · grw [Nat.pow_le_pow_left (m := (a₁ x + a₂ x + 2)) (by omega)]
          exact Nat.pow_le_pow_of_le (by omega) (by omega)
    _ = 2 * (a₁ x + a₂ x + 2) ^ (b₁ x + b₂ x + 2) := by ring
    _ ≤ (a₁ x + a₂ x + 2) * (a₁ x + a₂ x + 2) ^ (b₁ x + b₂ x + 2) := by
        apply Nat.mul_le_mul_right; linarith
    _ = (a₁ x + a₂ x + 2) ^ (b₁ x + b₂ x + 2 + 1) := by ring

instance : LawfulGrowthRate (A ^ B) where
  mem_dominating := gpow_mem_dominating
  mem_add := gpow_mem_add'
  comp_le_id := fun ⟨a, ha, b, hb, hle⟩ hg ↦
    ⟨_, comp_le_id' ha hg, _, comp_le_id' hb hg, fun _ ↦ hle _⟩
  one_mem := ⟨1, one_mem, 1, one_mem, fun _ => by norm_num⟩

/-! #### Algebraic properties -/

/-- For a lawful growth rate `S`, `S.gadd S = S`: adding a growth rate to itself
gives back the same growth rate. -/
@[simp]
theorem add_self : A + A = A := by
  ext h
  constructor
  · rintro ⟨f, hf, g, hg, hfg⟩
    exact mem_dominating (Filter.Eventually.of_forall fun x => hfg x)
      (LawfulGrowthRate.mem_add hf hg)
  · intro hh
    exact ⟨h, hh, h, hh, fun n => Nat.le_add_left _ _⟩

omit [LawfulGrowthRate B] in
/-- Multiplication distributes over addition of growth rates (left distributivity).
Requires `A` to be lawful so that `A` is closed under addition. -/
protected theorem mul_add : A * (B + C) = (A * B) + (A * C) := by
  apply le_antisymm gmul_gadd_le
  convert ← gmul_gadd_gmul_le
  exact add_self

/-- For a lawful growth rate `S`, adding `const = O(1)` does not change it. -/
@[simp]
theorem add_const : A + const = A  := by
  refine le_antisymm ?_ ?_
  · trans A + A
    · exact gadd_mono_right (fun f hf ↦ const_mem hf)
    · rw [add_self]
  · intro h hh
    exact ⟨h, hh, 0, zero_mem, fun n => by simp⟩

end operations

end GrowthRate

end CSLib
