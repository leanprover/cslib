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

@[expose] public section

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
 * `GrowthRate.two_pow`: O(2 ^ n)
 * `GrowthRate.e_pow`: O(Real.exp n)

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

open scoped Topology

/-- A **Growth rate** is just any collection of `ℕ → ℕ`, but as a type alias intended for
discussing how quickly certain classes functions grow, as is often needed in asymptotic runtime
or memory analysis in computational complexity theory. A `LawfulGrowthRate` instance puts
constraints on this set behaving well in various ways.
-/
abbrev GrowthRate := Set (ℕ → ℕ)

namespace GrowthRate

section defs

def bigO (g : ℕ → ℕ) : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =O[.atTop] (g · : ℕ → ℤ)

def littleO (g : ℕ → ℕ) : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =o[.atTop] (g · : ℕ → ℤ)

--Defining the rate classes, sorted in order of growing more quickly.
--Summary:

/-
const       := bigO 1
log         := bigO (Nat.log 2)
polylog     := setOf ...
sqrt        := bigO Nat.sqrt
sublinear   := setOf ...
linear      := bigO id
linearithmic := bigO (fun n ↦ n * Nat.log 2 n)
quasilinear := setOf ...
poly        := setOf ...
quasipoly   := setOf ...
two_pow     := bigO (2 ^ ·)
e_pow       := bigO (⌈Real.exp ·⌉₊)
exp         := setOf ...
primitiveRecursive := setOf ...
computable := setOf ...
-/

/-- Constant growth rates: `O(1)` -/
abbrev const := bigO 1

/-- Logarithmic growth rates: `O(log n)` -/
abbrev log := bigO (Nat.log 2)

/-- Polylogarithmic growth rates: `(log n) ^ O(1)` -/
def polylog : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(Nat.log 2 n ^ C) : ℕ → ℤ)

/-- Square-root growth rates: `O(√n)` -/
abbrev sqrt := bigO Nat.sqrt

/-- Sublinear growth rates: `o(n)` -/
abbrev sublinear := littleO id

/-- Linear growth rates: `O(n)` -/
abbrev linear := bigO id

/-- linearithmic growth rates: `O(n * log n)` -/
abbrev linearithmic := bigO (fun n ↦ n * Nat.log 2 n)

/-- Quasilinear growth rates: `n * (log n)^O(1)` -/
def quasilinear : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(n * Nat.log 2 n ^ C) : ℕ → ℤ)

/-- Polynomial growth rates: `n ^ O(1)` -/
def poly : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (· ^ C : ℕ → ℤ)

/-- Quasipolynomial growth rates: `2 ^ {log(n) ^ O(1)}` -/
def quasipoly : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ 2 ^ (Nat.log 2 n ^ C) : ℕ → ℤ)

/-- `O(2 ^ n)` growth rates, not to be confused with `exp` which is `2 ^ O(n)`. -/
abbrev two_pow := bigO (2 ^ ·)

/-- `O(e ^ n)` growth rates, not to be confused with `exp` which is `e ^ O(n)`. -/
abbrev e_pow := bigO (⌈Real.exp ·⌉₊)

/-- Exponential growth rates: `O(1) ^ n`, or equivalently `2 ^ O(n)`. Corresponds to the
complexity class `E`. -/
def exp : GrowthRate :=
  setOf <| fun f ↦ ∃ (C : ℕ),
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ C ^ n : ℕ → ℤ)

/-- Primitive recursive growth rates.

We can't just define this as the set `fun f ↦ Primrec f`, because this would exclude for instance
the function `fun n ↦ if HaltingProblem n then 0 else 1`, even though that's O(1). We instead say
that this is `bigO` of some other primitive recursive function which gives an upper bound.
-/
def primitiveRecursive : GrowthRate :=
  setOf <| fun f ↦ ∃ g,
    Nat.Primrec g ∧ f ∈ bigO g

/-- Computable growth rates.

We can't just define this as the set `fun f ↦ Computable f`, because this would exclude for
instance the function `fun n ↦ if HaltingProblem n then 0 else 1`, even though that's O(1). We
instead say that this is `bigO` of some other computable function which gives an upper bound.
-/
def computable : GrowthRate :=
  setOf <| fun f ↦ ∃ g,
    Computable g ∧ f ∈ bigO g

end defs

section basic

/-- Constant functions are in the `GrowthRate.const` class. -/
theorem const_mem_const (k : ℕ) : (fun _ ↦ k) ∈ GrowthRate.const := by
  simp only [const, bigO, Pi.one_apply, Nat.cast_one, Asymptotics.isBigO_one_iff]
  use k
  simp

/--
If a function `f : ℕ → ℕ` has constant growth rate (i.e., is O(1)), then it is bounded by some
constant `C`.
-/
lemma bounded_of_const {f : ℕ → ℕ} (h : f ∈ GrowthRate.const) : ∃ C, ∀ n, f n ≤ C := by
  have ⟨C, hC⟩ := h.exists_nonneg
  simp_all only [Pi.one_apply, Nat.cast_one, Asymptotics.IsBigOWith, norm_natCast,
    norm_one, mul_one, Filter.eventually_atTop]
  refine ⟨⌊C⌋₊ + ∑ n ∈ .range hC.2.choose, f n, fun n ↦ ?_⟩
  by_cases hn : n < hC.2.choose
  · exact le_add_of_nonneg_of_le (Nat.zero_le _)
      (Finset.single_le_sum (fun x _ ↦ Nat.zero_le (f x)) (Finset.mem_range.mpr hn))
  · exact le_add_of_le_of_nonneg (Nat.le_floor <| hC.2.choose_spec n (le_of_not_gt hn))
      (Nat.zero_le _)

theorem bigO_add {f g a b : ℕ → ℕ} (hf : f ∈ bigO a) (hg : g ∈ bigO b) :
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

end basic

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
      nlinarith
    · grw [← le_max_left, hC n hn]
      linarith
  have h_linear (C : ℕ) : C * (g + 1) ∈ S := by
    induction C
    · simp only [Nat.cast_zero, zero_mul]
      exact zero_mem
    · simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      exact add ‹_› (add hg one_mem)
  exact mem_dominating (Filter.Eventually.of_forall (by simpa using hC <| g ·)) (h_linear C)

/-- LawfulGrowthRate is closed under linear transformations. -/
lemma affine_comp {S : GrowthRate} [LawfulGrowthRate S] {f : ℕ → ℕ} {a b : ℕ} (hf : f ∈ S) :
    (fun n ↦ a * f n + b) ∈ S :=
  add (const_mul (const_mem_const a) hf) (const_mem (const_mem_const b))

section instances

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

instance : LawfulGrowthRate log := by
  apply instLawfulBigO (by exact ⟨2, fun _ ↦ Nat.log_pos one_lt_two⟩)
  intro k hk g hg
  replace hk := hk.exists_nonneg
  simp_all only [Asymptotics.IsBigOWith, norm_natCast, Filter.eventually_atTop]
  rcases hk with ⟨C, hC, a, ha⟩
  apply Asymptotics.isBigO_iff.mpr
  have ⟨M, hM⟩ : ∃ M, ∀ b < a, k b ≤ M :=
    ⟨(Finset.range a).sup k, fun b hb ↦ Finset.le_sup (Finset.mem_range.mpr hb)⟩
  refine ⟨C ⊔ M + 1, Filter.eventually_atTop.mpr ⟨a + 1, fun x hx ↦ ?_⟩⟩
  norm_cast
  simp_all only [Order.add_one_le_iff, Function.comp_apply, norm_natCast]
  rcases lt_or_ge (g x) a with hgx | hgx
  · grw [hM _ hgx, ← le_max_right, ← Nat.le_log_of_pow_le one_lt_two (by linarith : 2 ^ 1 ≤ x)]
    simp
  · grw [ha _ hgx, ← le_max_left, hg x, add_mul]
    simp

lemma polylog_mem_dominating {f g : ℕ → ℕ} (h : ∀ᶠ x in .atTop, g x ≤ f x)
    (hf : f ∈ polylog) : g ∈ polylog := by
  refine hf.imp fun C hC ↦ ?_
  refine Asymptotics.IsBigO.trans ?_ hC
  rw [Asymptotics.isBigO_iff]
  use 1
  filter_upwards [h] with n hn
  simpa using mod_cast hn

instance : LawfulGrowthRate polylog where
  mem_dominating h hf := by
    refine hf.imp fun C hC ↦ ?_
    refine Asymptotics.IsBigO.trans ?_ hC
    rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [h] with n hn
    simpa using mod_cast hn
  mem_add hf hg := by
    rcases hf with ⟨a, ha⟩
    rcases hg with ⟨b, hb⟩
    use a + b
    refine Asymptotics.IsBigO.add (ha.trans ?_) (hb.trans ?_)
    all_goals (
      rw [Asymptotics.isBigO_iff]
      use 1
      norm_num
      use 2
      intro _ hn
      exact_mod_cast pow_le_pow_right₀ (Nat.le_log_of_pow_le one_lt_two hn) (by bound)
   )
  one_mem := by
    use 0
    simp only [Nat.cast_one, pow_zero, Asymptotics.isBigO_one_iff]
    use 1
    simp
  comp_le_id {f g} hf hg := by
    rcases hf with ⟨C, hC⟩
    have ⟨K, hK⟩ : ∃ K, ∀ n ≥ K, f n ≤ K * (Nat.log 2 n ^ C) := by
      norm_num [Asymptotics.isBigO_iff, Filter.eventually_atTop] at *
      rcases hC with ⟨c, a, hc⟩
      refine ⟨⌈c⌉₊ + a, fun n hn ↦ ?_⟩
      exact_mod_cast (show (f n : ℝ) ≤ (⌈c⌉₊ + a) * Nat.log 2 n ^ C by
        nlinarith [Nat.le_ceil c, hc n (by linarith),
          pow_nonneg (Nat.cast_nonneg (Nat.log 2 n) : (0 : ℝ) ≤ Nat.log 2 n) C])
    -- Let `B` be such that `f(n) ≤ B` for `n < M`.
    have ⟨B, hB⟩ : ∃ B, ∀ n < K, f n ≤ B := by
      refine ⟨Finset.sup (Finset.range K) f, fun n hn ↦ ?_⟩
      exact Finset.le_sup (Finset.mem_range.mpr hn)
    use C + 1
    apply Asymptotics.IsBigO.of_bound (K + B + 1)
    filter_upwards [Filter.eventually_ge_atTop K, Filter.eventually_gt_atTop 1] with n hn hn'
    norm_num [pow_succ']
    by_cases h : g n < K
    · refine le_trans (Nat.cast_le.mpr (hB _ h)) ?_
      norm_cast
      suffices 0 < Nat.log 2 n * Nat.log 2 n ^ C by nlinarith
      exact mul_pos (Nat.log_pos one_lt_two hn') (pow_pos (Nat.log_pos one_lt_two hn') _)
    · apply le_trans (Nat.cast_le.mpr (hK _ (by linarith)))
      norm_cast
      gcongr
      · linarith
      · refine le_trans (pow_le_pow_left' (Nat.log_mono_right <| hg n) _) ?_
        exact (le_mul_of_one_le_left (by positivity) <|
          Nat.le_log_of_pow_le (by norm_num) <| by linarith)

instance : LawfulGrowthRate sqrt :=  by
  apply instLawfulBigO
  · use 1
    intros
    positivity
  · simp only [bigO, Asymptotics.IsBigO, Set.mem_setOf_eq, Function.comp_apply,
      forall_exists_index]
    intro k x hk g hg
    norm_num [Asymptotics.IsBigOWith] at *
    rcases hk with ⟨a, ha⟩
    have ⟨c, hc⟩ : ∃ c, ∀ i ≤ a, k i ≤ c := by
      refine ⟨Finset.sup (Finset.range (a + 1)) k, fun i hi ↦ ?_⟩
      exact Finset.le_sup (Finset.mem_range_succ_iff.mpr hi)
    use c ⊔ ⌈x⌉₊, a + 1
    intro b hb
    by_cases h : g b ≤ a
    · refine le_trans (Nat.cast_le.mpr (hc _ h)) ?_
      exact le_trans (mod_cast le_max_left _ _)
        (le_mul_of_one_le_right (by positivity) (mod_cast Nat.sqrt_pos.mpr (by linarith)))
    · refine le_trans (ha _ ?_) ?_
      · linarith
      · gcongr
        · exact le_max_of_le_right (Nat.le_ceil _)
        · exact hg b

instance : LawfulGrowthRate sublinear := by
  apply instLawfulLittleO
  · simpa [littleO] using tendsto_natCast_atTop_atTop
  · intro k g hk hg
    unfold littleO at *
    norm_num [Asymptotics.isLittleO_iff] at *
    intro c hc_pos
    have ⟨N, hN⟩ := hk (half_pos hc_pos)
    use N + ⌈(2 * (∑ i ∈ .range N, k i)) / c⌉₊ + 1
    intro n hn
    rcases lt_or_ge (g n) N with hgn | hgn
    · have : (k (g n) : ℝ) ≤ ∑ i ∈ .range N, k i :=
        mod_cast Finset.single_le_sum (fun i _ ↦ Nat.zero_le (k i)) (Finset.mem_range.mpr hgn)
      have : (n : ℝ) ≥ N + ⌈2 * (∑ i ∈ .range N, k i) / c⌉₊ + 1 := mod_cast hn
      have := Nat.le_ceil (2 * (∑ i ∈ .range N, k i) / c)
      rw [div_le_iff₀ hc_pos] at this
      nlinarith
    · exact (hN _ hgn).trans (by nlinarith [(mod_cast hg n : (g n : ℝ) ≤ n)])

instance : LawfulGrowthRate linear := by
  apply instLawfulBigO
  · exact ⟨1, fun _ ↦ id⟩
  intro k hk g hg
  unfold bigO at hk ⊢
  have ⟨C, N, hC⟩ : ∃ C N, ∀ x ≥ N, k x ≤ C * x := by
    norm_num [Asymptotics.isBigO_iff] at hk
    rcases hk with ⟨c, N, hc⟩
    refine ⟨⌈c⌉₊, N, fun n hn ↦ ?_⟩
    exact_mod_cast (hc n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  refine Asymptotics.IsBigO.of_bound (C + ∑ x ∈ .range N, k x + 1)
    (Filter.eventually_atTop.mpr ⟨N, fun x hx ↦ ?_⟩)
  simp_all only [id_eq, Set.mem_setOf_eq, Function.comp_apply, norm_natCast,
    Nat.cast_sum, add_mul, one_mul]
  by_cases hx' : g x < N
  · exact le_add_of_le_of_nonneg (le_add_of_nonneg_of_le (by positivity) (mod_cast by
      have : k (g x) ≤ _ := Finset.single_le_sum (fun a _ ↦ Nat.zero_le (k a))
        (Finset.mem_range.mpr hx')
      nlinarith)) (by positivity)
  · rw [not_lt] at hx'
    exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg (mod_cast hC _ hx' |> le_trans <|
      Nat.mul_le_mul_left _ <| hg x) <| by positivity) <| by positivity

instance : LawfulGrowthRate linearithmic := by
  apply instLawfulBigO
  · use 2
    intro n hn
    nlinarith [Nat.log_pos one_lt_two hn]
  intro k hk g hg
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, k n ≤ C * n * Nat.log 2 n := by
    rcases hk.exists_pos with ⟨C, hC_pos, hC⟩
    rw [Asymptotics.isBigOWith_iff] at hC
    simp only [norm_natCast, Nat.cast_mul, norm_mul, Filter.eventually_atTop] at hC ⊢
    refine ⟨⌈C⌉₊, hC.choose, fun n hn ↦ ?_⟩
    rw [← @Nat.cast_le ℝ]
    push_cast
    nlinarith [Nat.le_ceil C, hC.choose_spec n hn,
      show (n : ℝ) * Nat.log 2 n ≥ 0 by positivity]
  apply Asymptotics.IsBigO.of_bound ((∑ n ∈ .range N, k n) + C) _
  simp only [Function.comp_apply, norm_natCast, Nat.cast_sum, Nat.cast_mul,
    norm_mul, Filter.eventually_atTop] at hC ⊢
  refine ⟨N + 2, fun n hn ↦ ?_⟩
  by_cases hgn : g n < N
  · exact le_trans
      (mod_cast Finset.single_le_sum (fun x _ ↦ Nat.zero_le (k x)) (Finset.mem_range.mpr hgn))
      (le_trans (le_add_of_nonneg_right <| Nat.cast_nonneg _) <|
        le_mul_of_one_le_right (by positivity) <|
          one_le_mul_of_one_le_of_one_le (mod_cast by linarith) <|
            mod_cast Nat.le_log_of_pow_le (by linarith) <| by linarith)
  · apply le_trans (Nat.cast_le.mpr (hC _ (by linarith))) ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (
      le_add_of_nonneg_left <| Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) <| by positivity)
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left (mul_le_mul (Nat.cast_le.mpr (hg n))
      (Nat.cast_le.mpr (Nat.log_mono_right (hg n))) (by positivity) (by positivity)) (by positivity)

lemma quasilinear_bound_mono (C : ℕ) : Monotone (fun n ↦ n * (Nat.log 2 n) ^ C) := by
  exact fun a b hab ↦ Nat.mul_le_mul hab (Nat.pow_le_pow_left (Nat.log_mono_right hab) _)

lemma isBigO_quasilinear_bound_comp_le_id (C : ℕ) (g : ℕ → ℕ) (hg : g ≤ id) :
    (fun n ↦ (g n * Nat.log 2 (g n) ^ C : ℤ)) =O[.atTop] (fun n ↦ (n * Nat.log 2 n ^ C : ℤ)) := by
  apply Asymptotics.IsBigO.of_bound 1
  simp only [norm_mul, norm_natCast, norm_pow, one_mul, Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  refine mul_le_mul (mod_cast hg n) ?_ (by positivity) (by positivity)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (mod_cast Nat.log_mono_right <| hg n) _

lemma isBigO_comp_bound_plus_const {h : ℕ → ℕ} (hf : (f · : ℕ → ℤ) =O[.atTop] (h · : ℕ → ℤ)) :
    (fun n ↦ (f (g n) : ℤ)) =O[.atTop] (fun n ↦ (h (g n) : ℤ) + 1) := by
  have ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, (f n : ℤ) ≤ C * (h n : ℤ) := by
    rw [Asymptotics.isBigO_iff'] at hf
    simp only [gt_iff_lt, norm_natCast, Filter.eventually_atTop] at hf ⊢
    refine ⟨⌈hf.choose⌉₊, hf.choose_spec.2.choose, fun n hn ↦ ?_⟩
    exact_mod_cast le_trans (hf.choose_spec.2.choose_spec n hn)
      (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  have ⟨M, hM⟩ : ∃ M, ∀ x < N, (f x : ℤ) ≤ M := by
    refine ⟨∑ x ∈ .range N, (f x : ℤ), fun x hx ↦ ?_⟩
    exact Finset.single_le_sum (fun x _ ↦ Nat.cast_nonneg (f x)) (Finset.mem_range.mpr hx)
  apply Asymptotics.IsBigO.of_bound (M ⊔ |C|)
  filter_upwards [Filter.eventually_gt_atTop N] with x hx
  by_cases hgx : g x < N
  · norm_num [Norm.norm]
    refine le_trans (mod_cast hM _ hgx) (le_trans (le_max_left _ _)
      (le_mul_of_one_le_right (by positivity) (mod_cast by linarith [Nat.zero_le (h (g x))])))
  · norm_num [Norm.norm]
    norm_cast
    simp only [not_lt, Nat.cast_add, Nat.cast_one] at hC hgx ⊢
    cases abs_cases C <;> nlinarith [hC (g x) hgx, le_max_left M |C|, le_max_right M |C|]

lemma one_isBigO_quasilinear_bound (C : ℕ) :
    (fun _ ↦ (1 : ℤ)) =O[.atTop] (fun n ↦ (n * (Nat.log 2 n) ^ C : ℤ)) := by
  rw [Asymptotics.isBigO_iff]
  use 1; norm_num
  refine ⟨2, fun n hn ↦ ?_⟩
  exact one_le_mul_of_one_le_of_one_le (by norm_cast; linarith)
    (one_le_pow₀ (mod_cast Nat.log_pos one_lt_two (by linarith)))

instance : LawfulGrowthRate quasilinear where
  mem_dominating h hf := by
    rcases hf with ⟨C, hC⟩
    refine ⟨C, Asymptotics.IsBigO.trans ?_ hC⟩
    rw [Asymptotics.isBigO_iff]
    use 1
    aesop
  mem_add hf hg := by
    rcases hf with ⟨a, ha⟩
    rcases hg with ⟨b, hb⟩
    use a + b
    refine Asymptotics.IsBigO.add (ha.trans ?_) (hb.trans ?_)
    all_goals (
      rw [Asymptotics.isBigO_iff]
      use 1
      norm_num
      use 2
      intro _ hn
      exact_mod_cast Nat.mul_le_mul_left _ <|
        pow_le_pow_right₀ (Nat.le_log_of_pow_le one_lt_two hn) (by bound)
   )
  one_mem := by
    use 0
    simp only [Asymptotics.isBigO_iff, Filter.eventually_atTop]
    use 1, 1
    intro b hb
    simp [hb]
  comp_le_id := by
    intro f g hf hg
    rcases hf with ⟨C, hC⟩
    use C
    simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_pow]
    apply (isBigO_comp_bound_plus_const hC).trans
    exact (isBigO_quasilinear_bound_comp_le_id C g hg).add (one_isBigO_quasilinear_bound C)

instance : LawfulGrowthRate poly where
  mem_dominating h hf := by
    simp_rw [poly, Set.mem_setOf, Asymptotics.isBigO_iff] at hf ⊢
    rcases hf with ⟨p, c, hf⟩
    use p, c
    filter_upwards [h, hf] with a h ha
    simp only [norm_natCast, norm_pow] at ha ⊢
    exact le_trans (mod_cast h) ha
  mem_add hf hg := by
    rcases hf with ⟨a, ha⟩
    rcases hg with ⟨b, hb⟩
    use a + b
    refine Asymptotics.IsBigO.add (ha.trans ?_) (hb.trans ?_)
    all_goals (
      rw [Asymptotics.isBigO_iff]
      use 1
      norm_num
      use 1
      intro _ hn
      exact_mod_cast pow_le_pow_right₀ hn (by bound)
   )
  one_mem := by
    use 0
    simp only [Asymptotics.isBigO_iff, Filter.eventually_atTop]
    use 1, 0
    simp
  comp_le_id := by
    intro f g hf hg
    rcases hf with ⟨C, hC⟩
    have ⟨K, hK⟩ : ∃ K, ∀ᶠ n in .atTop, f (g n) ≤ K * n ^ C := by
      have ⟨K, N, hK⟩ : ∃ K N, ∀ n ≥ N, f n ≤ K * n ^ C := by
        rw [Asymptotics.isBigO_iff'] at hC
        rcases hC with ⟨K, hK₀, hK⟩
        rcases Filter.eventually_atTop.mp hK with ⟨N, hN⟩
        refine ⟨⌈K⌉₊, N, fun n hn ↦ ?_⟩
        simpa [← @Nat.cast_le ℝ] using
          (hN n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
      use K + ∑ n ∈ .range N, f n
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      by_cases hgn : g n < N
      · exact le_trans (Finset.single_le_sum (fun x _ ↦ Nat.zero_le (f x))
          (Finset.mem_range.mpr hgn)) (Nat.le_trans (Nat.le_add_left _ _)
          (Nat.le_mul_of_pos_right _ (pow_pos (by linarith) _)))
      · exact le_trans (hK _ (by linarith)) (Nat.mul_le_mul_right _ (Nat.le_add_right _ _) |>
          le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hg n) _)))
    use C
    rw [Asymptotics.isBigO_iff]
    exact ⟨K, by filter_upwards [hK] with n hn; simpa using mod_cast hn⟩

instance : LawfulGrowthRate quasipoly where
  mem_dominating h hf := by
    simp only [quasipoly, Filter.eventually_atTop, Asymptotics.isBigO_iff, norm_natCast,
      Set.mem_setOf] at h hf ⊢
    rcases hf with ⟨C, c, a, hC⟩
    rcases h with ⟨a₂, h⟩
    use C, c, a₂ + a
    intro n hn
    grw [h n (by omega), hC n (by omega)]
  mem_add hf hg := by
    rcases hf with ⟨a, ha⟩
    rcases hg with ⟨b, hb⟩
    use a + b
    refine Asymptotics.IsBigO.add (ha.trans ?_) (hb.trans ?_)
    all_goals (
      rw [Asymptotics.isBigO_iff]
      use 1
      norm_num [Int.norm_eq_abs]
      use 2
      intro _ hn
      exact_mod_cast pow_le_pow_right₀ one_le_two <|
        pow_le_pow_right₀ (Nat.le_log_of_pow_le one_lt_two hn) (by bound)
   )
  one_mem := ⟨0, by simp⟩
  comp_le_id := by
    intro f g hf hg
    rcases hf with ⟨a, ha⟩
    have h_log_le : ∀ n, (Nat.log 2 (g n)) ^ a ≤ (Nat.log 2 n) ^ a := by
      exact fun n ↦ Nat.pow_le_pow_left (Nat.log_mono_right <| hg n) _
    have h_exp_le : ∀ n, 2 ^ ((Nat.log 2 (g n)) ^ a) ≤ 2 ^ ((Nat.log 2 n) ^ a) := by
      exact fun n ↦ pow_le_pow_right₀ (by decide) (h_log_le n)
    use a
    have ⟨C, hC⟩ : ∃ C, ∀ n, f n ≤ C * 2 ^ ((Nat.log 2 n) ^ a) := by
      have ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * 2 ^ (Nat.log 2 n) ^ a := by
        rw [Asymptotics.isBigO_iff] at ha
        norm_num at *
        rcases ha with ⟨c, N, hN⟩
        norm_num [Norm.norm] at hN
        refine ⟨⌈c⌉₊, N, fun n hn ↦ ?_⟩
        exact_mod_cast le_trans (hN n hn)
          (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
      use C + ∑ n ∈ .range N, f n + 1
      intros n
      by_cases hn : n < N
      · nlinarith [Finset.single_le_sum (fun x _ ↦ Nat.zero_le (f x)) (Finset.mem_range.mpr hn),
          Nat.one_le_pow (Nat.log 2 n ^ a) 2 zero_lt_two]
      · exact le_trans (hC n (le_of_not_gt hn)) (Nat.mul_le_mul_right _ (by
          linarith [Nat.zero_le (∑ n ∈ .range N, f n)]))
    apply Asymptotics.IsBigO.of_bound C
    simp only [Function.comp_apply, norm_natCast, norm_pow, Filter.eventually_atTop]
    refine ⟨1, fun n hn ↦ ?_⟩
    erw [Real.norm_of_nonneg (by positivity)]
    exact_mod_cast le_trans (hC _) (mul_le_mul_of_nonneg_left (mod_cast h_exp_le _)
      (Nat.cast_nonneg _))

instance : LawfulGrowthRate two_pow := by
  apply instLawfulBigO
  · use 0
    intros
    positivity
  · intros k hk g hg
    obtain ⟨C, hC⟩ : ∃ C, ∀ n, k n ≤ C * 2 ^ n := by
      obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ n in .atTop, k n ≤ C * 2 ^ n := by
        have ⟨C, hC⟩ := hk.exists_pos
        rw [Asymptotics.isBigOWith_iff] at hC
        norm_num [Norm.norm] at hC
        exact ⟨⌈C⌉₊, Filter.eventually_atTop.mpr ⟨hC.2.choose, fun n hn ↦ by
          exact_mod_cast hC.2.choose_spec n hn |> le_trans <|
            mul_le_mul_of_nonneg_right (Nat.le_ceil _) <| by positivity⟩⟩
      simp only [Filter.eventually_atTop] at hC
      obtain ⟨M, hM⟩ : ∃ M, ∀ n < hC.choose, k n ≤ M := by
        exact ⟨Finset.sup (Finset.range hC.choose) k, fun n hn ↦
          Finset.le_sup (Finset.mem_range.mpr hn)⟩
      refine ⟨C ⊔ M, fun n ↦ ?_⟩
      by_cases hn : n < hC.choose
      · exact le_trans (hM n hn) (by
          nlinarith [Nat.le_max_left C M, Nat.le_max_right C M, Nat.one_le_pow n 2 zero_lt_two])
      · exact le_trans (hC.choose_spec n (le_of_not_gt hn)) (by
          nlinarith [Nat.le_max_left C M, Nat.le_max_right C M, Nat.one_le_pow n 2 zero_lt_two])
    have h_comp : ∀ x, k (g x) ≤ C * 2 ^ x := by
      exact fun x ↦ le_trans (hC _) (Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by decide) (hg x)))
    apply Asymptotics.IsBigO.of_bound (C + 1)
    simp only [Function.comp_apply, norm_natCast, Nat.cast_pow, Nat.cast_ofNat, norm_pow,
      Filter.eventually_atTop]
    refine ⟨0, fun n hn ↦ ?_⟩
    erw [Real.norm_of_nonneg (by norm_num)]
    grw [h_comp n, ← zero_lt_one, add_zero]
    norm_cast

instance : LawfulGrowthRate e_pow := by
  apply instLawfulBigO
  · use 0
    intros
    positivity
  · intro k hk g hg
    obtain ⟨C, hC⟩ : ∃ C, ∀ n, k n ≤ C * ⌈Real.exp n⌉₊ := by
      obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, k n ≤ C * ⌈Real.exp n⌉₊ := by
        have h_def : ∃ C N, ∀ n ≥ N, k n ≤ C * ⌈Real.exp n⌉₊ := by
          change (k · : ℕ → ℤ) =O[.atTop] (fun n : ℕ ↦ ⌈Real.exp n⌉₊ : ℕ → ℤ) at hk
          rw [Asymptotics.isBigO_iff] at hk
          norm_num +zetaDelta at *
          obtain ⟨c, a, h⟩ := hk
          refine ⟨⌈c⌉₊, a, fun n hn ↦ ?_⟩
          exact_mod_cast (h n hn).trans
            (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
        exact h_def
      obtain ⟨M, hM⟩ : ∃ M, ∀ n < N, k n ≤ M := by
        exact ⟨(Finset.range N).sup k, fun n hn ↦ Finset.le_sup (Finset.mem_range.mpr hn)⟩
      refine ⟨C ⊔ M, fun n ↦ ?_⟩
      rcases lt_or_ge n N with hn | hn
      · grw [hM n hn, ← le_max_right]
        nlinarith [Nat.ceil_pos.mpr (Real.exp_pos n)]
      · grw [hC n hn, ← le_max_left]
    have h_comp : ∀ n, k (g n) ≤ C * ⌈Real.exp (g n)⌉₊ := by
      exact fun n ↦ hC _
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    simpa using mod_cast h_comp n |> le_trans <| mul_le_mul_of_nonneg_left
      (Nat.ceil_mono <| Real.exp_le_exp.mpr <| Nat.cast_le.mpr <| hg n) <| Nat.cast_nonneg _

instance : LawfulGrowthRate exp where
  mem_dominating h hf := by
    simp only [exp, Filter.eventually_atTop, Asymptotics.isBigO_iff, norm_natCast,
      Set.mem_setOf] at h hf ⊢
    choose C c a hC using hf
    choose a₂ h using h
    use C, c, a₂ + a
    intro n hn
    grw [h n (by omega), hC n (by omega)]
  mem_add hf hg := by
    rcases hf with ⟨a, ha⟩
    rcases hg with ⟨b, hb⟩
    use a + b
    refine Asymptotics.IsBigO.add (ha.trans ?_) (hb.trans ?_)
    all_goals (
      rw [Asymptotics.isBigO_iff]
      use 1
      norm_num [Int.norm_eq_abs]
      use 2
      intros
      exact pow_le_pow_left₀ (by positivity) (by rw [abs_of_nonneg (by positivity)]; bound) _
   )
  one_mem := by
    use 1
    simp only [Pi.one_apply, Nat.cast_one, one_pow, Asymptotics.isBigO_one_iff, norm_one]
    use 1
    simp
  comp_le_id {f g} hf hg := by
    obtain ⟨C, hC⟩ : ∃ C, f ∈ bigO (fun n ↦ C ^ n) := by
      exact hf.imp (mod_cast fun _ ↦ id)
    -- Since g(n) ≤ n, if C ≥ 1, then C^{g(n)} ≤ C^n. If C = 0, then f(n) is eventually 0,
    -- so f(g(n)) is eventually 0, which is O(1^n).
    by_cases hC_ge_1 : C ≥ 1
    · -- Since `g(n) ≤ n`, we have `C^(g(n)) ≤ C^n` for all `n`.
      have h_exp_g : (fun n ↦ C ^ g n) ∈ bigO (fun n ↦ C ^ n) := by
        apply Asymptotics.isBigO_iff.mpr
        refine ⟨1, Filter.Eventually.of_forall fun n ↦ ?_⟩
        simpa using pow_le_pow_right₀ (mod_cast hC_ge_1) (hg n)
      have h_f_g : f ∘ g ∈ bigO (fun n ↦ C ^ g n) := by
        simp only [bigO, Nat.cast_pow, Asymptotics.isBigO_iff, norm_natCast, norm_pow,
          Filter.eventually_atTop, Set.mem_setOf_eq, Function.comp_apply] at *
        rcases hC with ⟨c, a, hc⟩
        use c ⊔ (∑ x ∈ .range (a + 1), (f x : ℝ) / (C ^ x : ℝ)), a + 1
        intro b hb
        by_cases hgb : g b ≤ a
        · apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
          rw [Finset.sum_mul]
          exact le_trans (by rw [div_mul_cancel₀ _ (by positivity)])
            (Finset.single_le_sum (fun x _ ↦ by positivity) (Finset.mem_range.mpr (by linarith)))
        · grw [hc _ (by linarith), ← le_max_left]
      have h_f_g_final : f ∘ g ∈ bigO (fun n ↦ C ^ n) := by
        apply_rules [Asymptotics.IsBigO.trans]
      use C
      exact h_f_g_final
    · have hC_zero : C = 0 := Nat.eq_zero_of_not_pos hC_ge_1
      have h_eventually_zero : ∃ N, ∀ n ≥ N, f n = 0 := by
        have := hC
        norm_num [hC_zero, bigO] at this
        rw [Asymptotics.isBigO_iff] at this
        norm_num +zetaDelta at *
        refine ⟨this.choose_spec.choose + 1, fun n hn ↦ ?_⟩
        simpa [show n ≠ 0 by linarith] using this.choose_spec.choose_spec n (by linarith)
      obtain ⟨N, hN⟩ := h_eventually_zero
      use 1
      simp only [Function.comp_apply, Nat.cast_one, one_pow, Asymptotics.isBigO_one_iff,
        norm_natCast]
      refine ⟨∑ n ∈ .range N, (f n : ℝ), Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩⟩
      by_cases h : g n < N
      · simp only [Set.mem_setOf_eq]
        exact_mod_cast Finset.single_le_sum (fun a _ ↦ Nat.cast_nonneg _) (Finset.mem_range.mpr h)
      · simp_all only [nonpos_iff_eq_zero, one_ne_zero, not_false_eq_true, not_lt,
          CharP.cast_eq_zero, Set.mem_setOf_eq]
        positivity

section runningMax

/--
`runningMax f n` is the maximum value of `f k` for all `k ≤ n`. It is defined recursively:
`runningMax f 0 = f 0`, and `runningMax f (n+1) = max (runningMax f n) (f (n+1))`.
-/
def runningMax (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec (f 0) (fun k res ↦ res ⊔ (f (k + 1))) n

lemma runningMax_le (f : ℕ → ℕ) (n : ℕ) : f n ≤ runningMax f n := by
  induction n <;> simp [*, runningMax]

lemma runningMax_mono (f : ℕ → ℕ) : Monotone (runningMax f) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  exact le_max_left _ _

/-
The step function for `runningMax` is primitive recursive.
-/
def runningMaxStep (f : ℕ → ℕ) (n res : ℕ) : ℕ := res ⊔ (f (n + 1))

lemma runningMaxStep_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.Primrec (Nat.unpaired (runningMaxStep f)) := by
  have h_max : Nat.Primrec (Nat.unpaired Nat.max) := by
    have h_max : Nat.Primrec (Nat.unpaired (fun x y ↦ y + (x - y))) := by
      have h_max : Nat.Primrec (Nat.unpaired (fun x y ↦ y + x)) := by
        simpa only [add_comm] using Nat.Primrec.add
      convert h_max.comp (Nat.Primrec.pair (Nat.Primrec.right) Nat.Primrec.sub) using 1
      ext ⟨x, y⟩
      · simp
      · simp [Nat.unpaired, Nat.unpair_pair]
        ring
    grind
  convert h_max.comp <| Nat.Primrec.pair Nat.Primrec.right <|
    (hf.comp Nat.Primrec.succ).comp Nat.Primrec.left using 1
  unfold runningMaxStep
  aesop

/-
If `f` is primitive recursive, then `runningMax f` is primitive recursive.
-/
lemma runningMax_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (runningMax f) := by
  have h (n) : runningMax f n = n.rec (f 0) (Nat.unpaired (runningMaxStep f) <| Nat.pair · ·) := by
    induction n <;> aesop
  rw [funext h]
  exact Nat.Primrec.prec1 (f 0) (runningMaxStep_primrec hf)

/--
Every primitive recursive function is dominated (in the Big-O sense) by a monotone
primitive recursive function.
-/
lemma Primrec.exists_monotone_dominating {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ g, Nat.Primrec g ∧ Monotone g ∧ f ∈ bigO g := by
  use runningMax f
  and_intros
  · exact runningMax_primrec hf
  · exact runningMax_mono f
  · exact Asymptotics.isBigO_of_le _ (by simpa using runningMax_le f)

/--
If a monotone function `h : ℕ → ℕ` is not the zero function, then it is eventually at least 1.
-/
lemma monotone_nat_eventually_pos {h : ℕ → ℕ} (h_mono : Monotone h) (h_not_zero : h ≠ 0) :
    ∀ᶠ n in .atTop, 1 ≤ h n := by
  rw [Filter.eventually_atTop]
  refine (Function.ne_iff.mp h_not_zero).imp fun n hn m hm ↦ ?_
  specialize h_mono hm
  exact Nat.pos_of_ne_zero fun hnm ↦ hn <| by aesop

lemma bigO_comp_le_id_of_pos {f g h : ℕ → ℕ} (h_mono : Monotone h) (h_pos : ∀ n, 1 ≤ h n)
    (hg : g ≤ id) (hf : f ∈ bigO h) : f ∘ g ∈ bigO h := by
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * h n := by
    obtain ⟨C, N, hC⟩ := hf.exists_pos
    rw [Asymptotics.isBigOWith_iff] at hC
    rw [Filter.eventually_atTop] at hC
    rcases hC with ⟨N, hN⟩
    use ⌈C⌉₊, N
    intro n hn
    specialize hN n hn
    norm_num [Norm.norm] at hN
    exact_mod_cast hN.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  set M := Finset.sup (Finset.range N) (fun k ↦ f k)
  refine Asymptotics.IsBigO.of_bound (C + M) (Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩)
  by_cases hgn : g n ≥ N
  · norm_num
    exact_mod_cast le_trans (hC _ hgn) (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) |>
      le_trans <| Nat.mul_le_mul_left _ <| h_mono <| hg _
  · simp only [not_le, Function.comp_apply, norm_natCast] at *
    exact le_trans (Nat.cast_le.mpr <| Finset.le_sup (Finset.mem_range.mpr hgn)) <|
      by norm_cast; nlinarith [h_pos n]

end runningMax

instance : LawfulGrowthRate primitiveRecursive where
  mem_dominating h hf := by
    rw [primitiveRecursive, Set.mem_setOf] at hf ⊢
    peel hf with g hg hf
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    refine Asymptotics.IsBigO.trans ?_ hf
    rw [Asymptotics.isBigO_iff]
    exact ⟨1, Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ by simpa using mod_cast hN n hn⟩⟩
  mem_add hf hg := by
    obtain ⟨a, ha₁, ha₂⟩ := hf
    obtain ⟨b, hb₁, hb₂⟩ := hg
    simp_rw [primitiveRecursive, ← Primrec.nat_iff] at *
    exact ⟨_, Primrec.nat_add.comp ha₁ hb₁, bigO_add ha₂ hb₂⟩
  one_mem := by
    use fun _ ↦ 1
    simp only [Nat.Primrec.const, bigO, Nat.cast_one, Asymptotics.isBigO_one_iff, norm_natCast,
      Set.mem_setOf_eq, Pi.one_apply, true_and]
    use 1
    norm_num
  comp_le_id := by
    intros f g hf hg
    obtain ⟨h, hh₁, hh₂⟩ := hf
    -- By `Primrec.exists_monotone_dominating`, there exists `H` such that `Nat.Primrec H`,
    -- `Monotone H`, and `h = O(H)`.
    obtain ⟨H, hH₁, hH₂, hH₃⟩ := Primrec.exists_monotone_dominating hh₁
    -- Let `H' n = H n + 1`. `H'` is primitive recursive (sum of primrec and const).
    set H' : ℕ → ℕ := fun n ↦ H n + 1
    have hH'_primrec : Nat.Primrec H' := by
      exact Nat.Primrec.succ.comp hH₁
    -- Since `H'` is monotone and positive, and `f = O(H')`, we can apply
    -- `GrowthRate.bigO_comp_le_id_of_pos`.
    have h_comp : f ∘ g ∈ bigO H' := by
      apply bigO_comp_le_id_of_pos
      · exact fun n m hnm ↦ Nat.succ_le_succ (hH₂ hnm)
      · exact fun n ↦ Nat.succ_pos _
      · assumption
      · apply Asymptotics.IsBigO.trans hh₂
        apply Asymptotics.IsBigO.trans hH₃
        apply Asymptotics.isBigO_iff.mpr
        norm_num +zetaDelta at *
        use 1, 0
        intro n hn
        erw [Real.norm_of_nonneg] <;> norm_cast <;> linarith
    exact ⟨H', hH'_primrec, h_comp⟩

/-
For every computable function `f`, there exists a computable monotone function `g` such
that `f ≤ g`.
-/
lemma exists_monotone_computable_bound' {f : ℕ → ℕ} (hf : Computable f) :
    ∃ g, Computable g ∧ Monotone g ∧ ∀ n, f n ≤ g n := by
  let g := fun n ↦ ((List.range (n+1)).map f).foldl max 0
  have hg : Computable g := by
    have h_max : ∀ n, g n = Nat.recOn n (f 0) (fun n g ↦ g ⊔ (f (n + 1))) := by
      intro n
      induction n
      · aesop
      · simp only [g]
        rw [List.range_succ]
        aesop
    rw [show g = _ from funext h_max]
    have h_rec : Computable (fun p : ℕ × ℕ ↦ (p.1 + 1, p.2 ⊔ (f (p.1 + 1)))) := by
      apply Computable.pair
      · exact Computable.succ.comp Computable.fst
      · apply Computable.of_eq (f := fun p ↦ p.2 ⊔ f (p.1 + 1))
        · have h_max1 : Computable (fun (p : ℕ × ℕ) ↦ (p.2, f (p.1 + 1))) := by
            exact Computable.pair (Computable.snd) (hf.comp (Computable.succ.comp (Computable.fst)))
          have h_max : Computable (fun (p : ℕ × ℕ) ↦ p.1 ⊔ p.2) := by
            -- The max function is primitive recursive, hence computable.
            have h_max_primrec : Primrec (fun (p : ℕ × ℕ) ↦ p.1 ⊔ p.2) := by
              exact Primrec.nat_max
            exact Primrec.to_comp h_max_primrec
          exact h_max.comp h_max1
        · exact fun n ↦ rfl
    have h_iter : ∀ n, (Nat.recOn n (f 0) fun n g ↦ g ⊔ (f (n + 1))) = (Nat.iterate
        (fun p : ℕ × ℕ ↦ (p.1 + 1, p.2 ⊔ (f (p.1 + 1)))) n (0, f 0)).2 := by
      intro n
      induction n
      · simp
      simp_all only [Function.iterate_succ_apply']
      rename_i n ih
      erw [show (Nat.iterate (fun p : ℕ × ℕ ↦ (p.1 + 1, p.2 ⊔ f (p.1 + 1))) n
        (0, f 0)).1 = n from
        Nat.recOn n rfl fun n ihn ↦ by simp [*, Function.iterate_succ_apply']]
    have h_eq : (fun x ↦ Nat.recOn x (f 0) fun n g ↦ g ⊔ f (n + 1)) =
        fun n ↦ ((fun p : ℕ × ℕ ↦ (p.1 + 1, p.2 ⊔ f (p.1 + 1))) ^[n] (0, f 0)).2 :=
      funext h_iter
    rw [h_eq]
    have h_iter : Computable (fun n ↦ (Nat.iterate
        (fun p : ℕ × ℕ ↦ (p.1 + 1, p.2 ⊔ (f (p.1 + 1)))) n (0, f 0))) := by
      have h_iter : ∀ n, (Nat.iterate (fun p : ℕ × ℕ ↦ (p.1 + 1, p.2 ⊔ (f (p.1 + 1))))
          n (0, f 0)) = Nat.recOn n (0, f 0) (fun n p ↦ (p.1 + 1, p.2 ⊔ (f (p.1 + 1)))) := by
        exact fun n ↦ by induction n <;> simp [*, Function.iterate_succ_apply']
      apply Computable.of_eq
      · apply Computable.nat_rec (h := fun n p ↦ (p.2.1 + 1, p.2.2 ⊔ f (p.2.1 + 1)))
        · exact Computable.id
        · exact Computable.const (0, f 0)
        · exact h_rec.comp (Computable.snd.comp (Computable.snd))
      · exact fun n ↦
          Eq.symm (Prod.ext (congrArg Prod.fst (h_iter n)) (congrArg Prod.snd (h_iter n)))
    exact Computable.snd.comp h_iter
  have hmono : Monotone g := by
    apply monotone_nat_of_le_succ
    simp [g, List.range_succ]
    grind
  have hle (n) : f n ≤ g n := by
    induction n <;> simp [g, List.range_succ]
  exact ⟨g, hg, hmono, hle⟩

/-
If `h` is monotone and `≥ 1`, and `f = O(h)` and `g ≤ id`, then `f ∘ g = O(h)`.
-/
lemma bigO_comp_le_id {f g h : ℕ → ℕ} (hh_mono : Monotone h) (hh_pos : ∀ n, 1 ≤ h n)
     (hf : f ∈ bigO h) (hg : g ≤ id) : f ∘ g ∈ bigO h := by
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * h n := by
    obtain ⟨C, N, hC⟩ := hf.exists_pos
    rw [Asymptotics.isBigOWith_iff] at hC
    rw [Filter.eventually_atTop] at hC
    rcases hC with ⟨N, hN⟩
    use ⌈C⌉₊, N
    intro n hn
    specialize hN n hn
    norm_num [Norm.norm] at hN
    exact_mod_cast hN.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) <| Nat.cast_nonneg _)
  -- Let `M = max_{k < N} f(k)`.
  obtain ⟨M, hM⟩ : ∃ M, ∀ k < N, f k ≤ M := by
    use Finset.sup (Finset.range N) f
    exact fun k hk ↦ Finset.le_sup (Finset.mem_range.mpr hk)
  have h_bound : ∀ n, f (g n) ≤ (C + M) * h n := by
    intro n; by_cases hgn : g n < N
    · nlinarith [hM (g n) hgn, hh_pos n]
    · simp_all only [not_lt, add_mul]
      exact le_add_of_le_of_nonneg (le_trans (hC _ hgn) (Nat.mul_le_mul_left _ (hh_mono (hg _))))
        (Nat.zero_le _)
  apply Asymptotics.IsBigO.of_bound (C + M)
  simp only [Function.comp_apply, norm_natCast, Filter.eventually_atTop]
  exact ⟨0, fun n hn ↦ mod_cast h_bound n⟩

instance : LawfulGrowthRate computable where
  mem_dominating h hf := by
    rw [computable, Set.mem_setOf] at hf ⊢
    peel hf with g hg hf
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    refine (Asymptotics.isBigO_iff.mpr ?_).trans hf
    use 1
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ by simpa using mod_cast hN n hn⟩
  mem_add hf hg := by
    obtain ⟨a, ha₁, ha₂⟩ := hf
    obtain ⟨b, hb₁, hb₂⟩ := hg
    use a + b
    exact ⟨Primrec.nat_add.to_comp.comp ha₁ hb₁, bigO_add ha₂ hb₂⟩
  one_mem := by
    use fun _ ↦ 1
    simp only [bigO, Nat.cast_one, Asymptotics.isBigO_one_iff, norm_natCast, Set.mem_setOf_eq,
      Pi.one_apply]
    use Computable.const 1, 1
    exact Filter.eventually_atTop.mpr ⟨0, fun _ _ ↦ by norm_num⟩
  comp_le_id {f g} hf hg := by
    obtain ⟨g, hg₁, hg₂⟩ := hf
    obtain ⟨h', hh'₁, hh'₂⟩ := exists_monotone_computable_bound' hg₁
    set h'' : ℕ → ℕ := fun n ↦ h' n + 1
    have hh''₁ : Computable h'' :=
      Computable.succ.comp hh'₁
    have hh''₂ : Monotone h'' :=
      fun n m hnm ↦ Nat.succ_le_succ (hh'₂.1 hnm)
    have hh''₃ : ∀ n, 1 ≤ h'' n :=
      fun n ↦ Nat.succ_pos _
    have hfg : f ∈ bigO h'' := by
      have hfg : f ∈ bigO h' := by
        apply Asymptotics.IsBigO.trans hg₂
        apply Asymptotics.IsBigO.of_bound 1
        exact Filter.eventually_atTop.mpr ⟨0, fun n hn ↦ by simpa using mod_cast hh'₂.2 n⟩
      apply hfg.trans
      rw [Asymptotics.isBigO_iff]
      norm_num +zetaDelta at *
      exact ⟨1, 0, fun n hn ↦ by erw [Real.norm_of_nonneg] <;> norm_num; linarith⟩
    exact ⟨h'', hh''₁, bigO_comp_le_id hh''₂ hh''₃ hfg hg⟩

end instances
end lawful

section equivalent_defs
--Equivalent versions in terms of other functions or big-O-style descriptions

theorem bigO_log2_eq_log : bigO Nat.log2 = log := by
  rw [funext @Nat.log2_eq_log_two]

theorem clog_mem_log2 : Nat.clog 2 ∈ log := by
  rw [← bigO_log2_eq_log]
  -- Since Nat.clog 2 n is either 0 or Nat.log 2 n + 1, we can choose C = 2.
  have h_bound : ∀ n, Nat.clog 2 n ≤ 2 * Nat.log 2 n + 2 := by
    intro n
    by_cases hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3
    · rcases hn with (rfl | rfl | rfl | rfl) <;> decide
    · have h_bound : 2^(2 * Nat.log 2 n + 2) ≥ n := by
        exact le_trans (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _))
          (Nat.pow_le_pow_right (by decide) (by linarith))
      exact Nat.le_trans (Nat.clog_mono_right _ h_bound) (by norm_num)
  have h_bigO : ∃ C N, ∀ n ≥ N, Nat.clog 2 n ≤ C * Nat.log2 n := by
    -- C = 4 and N = 2 suffices for the bigO.
    use 4, 2
    intro n hn
    rw [Nat.log2_eq_log_two]
    linarith [h_bound n, show Nat.log 2 n ≥ 1 from Nat.le_log_of_pow_le one_lt_two hn]
  obtain ⟨C, N, hC⟩ := h_bigO
  apply Asymptotics.IsBigO.of_bound C _
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  simpa using mod_cast hC n hn


theorem log_iff_rlog {f : ℕ → ℕ} : f ∈ log ↔ (f · : ℕ → ℝ) =O[.atTop] (Real.log ·) := by
  simp only [log]
  constructor <;> intro H
  · rw [Asymptotics.isBigO_iff] at *
    obtain ⟨c, hc⟩ : ∃ c, ∀ᶠ x in .atTop, f x ≤ c * Nat.log 2 x := by
      simp only [Filter.eventually_atTop]
      rw [bigO, Set.mem_setOf_eq, Asymptotics.isBigO_iff'] at H
      simp only [norm, Int.cast_natCast, Nat.abs_cast, Filter.eventually_atTop] at H
      obtain ⟨c, hc, a, ha⟩ := H
      refine ⟨⌈c⌉₊, a, fun n hn ↦ ?_⟩
      exact_mod_cast (by nlinarith [Nat.le_ceil c, ha n hn] : (f n : ℝ) ≤ ⌈c⌉₊ * Nat.log 2 n)
    obtain ⟨c', hc'⟩ : ∃ c' : ℝ, ∀ x ≥ 2, Nat.log 2 x ≤ c' * Real.log x := by
      use 1 / Real.log 2
      intro x hx
      rw [div_mul_eq_mul_div, le_div_iff₀ (Real.log_pos one_lt_two)]
      norm_cast
      rw [one_mul, ← Real.log_rpow zero_lt_two]
      gcongr
      norm_cast
      exact Nat.pow_log_le_self 2 <| by linarith
    use c * c'
    filter_upwards [hc, Filter.eventually_ge_atTop 2] with x hx₁ hx₂
    norm_num [mul_assoc]
    rw [abs_of_nonneg (Real.log_nonneg (by norm_cast; linarith))]
    grw [hx₁, ← hc' x (mod_cast hx₂)]
    norm_cast
  · have h_log2 : (fun x ↦ (f x : ℝ)) =O[.atTop] (fun x ↦ Real.log x / Real.log 2) := by
      rw [Asymptotics.isBigO_iff'] at *
      simp_all only [RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop, norm_div,
        mul_div]
      refine ⟨H.choose * |Real.log 2|,
        mul_pos H.choose_spec.1 (abs_pos.mpr (ne_of_gt (Real.log_pos one_lt_two))),
        H.choose_spec.2.choose, fun n hn ↦ ?_⟩
      grw [le_div_iff₀ (by positivity), H.choose_spec.2.choose_spec n hn, mul_right_comm]
    have h_log2_nat : (fun x ↦ (f x : ℝ)) =O[.atTop] (fun x ↦ (Nat.log 2 x : ℝ)) := by
      apply h_log2.trans
      have h_log2_ge : ∀ x : ℕ, x ≥ 2 → Real.log x / Real.log 2 ≤ Nat.log 2 x + 1 := by
        intro x hx
        rw [div_le_iff₀ (Real.log_pos one_lt_two)]
        norm_cast
        rw [← Real.log_rpow zero_lt_two]
        gcongr
        exact_mod_cast (Nat.lt_pow_succ_log_self one_lt_two _).le
      apply Asymptotics.IsBigO.of_bound 2
      filter_upwards [Filter.eventually_ge_atTop 2] with x hx
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      grw [h_log2_ge x hx]
      norm_cast
      linarith [Nat.le_log_of_pow_le (x := 1) one_lt_two hx]
    convert h_log2_nat using 1
    simp [bigO]
    norm_num [Asymptotics.isBigO_iff]

theorem polylog_iff_rlog {f : ℕ → ℕ} : f ∈ polylog ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ (Real.log n) ^ C : ℕ → ℝ) := by
  -- To prove the equivalence, we can use the fact that ℤ and ℝ are isomorphic in this context.
  have h_iso : ∀ f g : ℕ → ℤ, (f · : ℕ → ℤ) =O[.atTop] (g · : ℕ → ℤ) ↔
      (fun x ↦ f x : ℕ → ℝ) =O[.atTop] (fun n ↦ g n : ℕ → ℝ) := by
    norm_num [Asymptotics.isBigO_iff, Norm.norm]
  simp only [polylog, Nat.cast_pow, h_iso, Int.cast_natCast, Int.cast_pow, Set.mem_setOf_eq]
  constructor <;> rintro ⟨C, hC⟩ <;> use C <;> apply hC.trans
  · -- We use that `Real.log x ≥ Real.log 2 * Nat.log 2 x` for all `x ≥ 1`.
    have h_log_ge : ∀ x : ℕ, 1 ≤ x → Real.log (x : ℝ) ≥ Real.log 2 * Nat.log 2 x := by
      intro x hx
      rw [mul_comm]
      rw [← Real.log_rpow zero_lt_two]
      apply Real.log_le_log (by positivity)
      norm_cast
      exact Nat.pow_log_le_self 2 (by positivity)
    apply Asymptotics.IsBigO.of_bound ((Real.log 2) ⁻¹ ^ C)
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), inv_pow]
    exact le_trans (by ring_nf; norm_num)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (h_log_ge x hx) _)
        (by positivity))
  · -- Since `log₂ n ≤ log n / log 2`, we have `(log₂ n)^C ≤ (log n / log 2)^C`.
    have h_log_bound : ∀ n : ℕ, n ≥ 2 → (Real.log n) ^ C ≤
        (Nat.log 2 n + 1) ^ C * (Real.log 2) ^ C := by
      intro n hn
      have h_log_bound : Real.log n ≤ (Nat.log 2 n + 1) * Real.log 2 := by
        rw [← Real.log_rpow zero_lt_two]
        gcongr
        norm_cast
        exact (Nat.lt_pow_succ_log_self one_lt_two _).le
      simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) h_log_bound C
    have h_log_bound_further : ∀ n : ℕ, n ≥ 2 → (Real.log n) ^ C ≤
        2 ^ C * (Nat.log 2 n) ^ C * (Real.log 2) ^ C := by
      intros n hn
      have h_log_bound_further : (Nat.log 2 n + 1) ^ C ≤ 2 ^ C * (Nat.log 2 n) ^ C := by
        rw [← mul_pow]
        gcongr
        linarith [Nat.log_pos one_lt_two hn]
      grw [h_log_bound n hn]
      exact mul_le_mul_of_nonneg_right (mod_cast h_log_bound_further) (by positivity)
    apply Asymptotics.IsBigO.of_bound (2 ^ C * Real.log 2 ^ C)
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    linarith [h_log_bound_further n hn]

theorem sqrt_iff_rsqrt {f : ℕ → ℕ} : f ∈ sqrt ↔ (f · : ℕ → ℝ) =O[.atTop] (√·) := by
  simp only [sqrt, bigO, Asymptotics.isBigO_iff', norm_natCast, Filter.eventually_atTop,
    Set.mem_setOf_eq, Real.norm_eq_abs, Real.sqrt_nonneg, abs_of_nonneg]
  constructor <;> rintro ⟨w, hw, k, h⟩
  · refine ⟨w, hw, k, fun n hn ↦ (h n hn).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' _) hw.le
  · refine ⟨w * 2, by positivity, k, fun m hm ↦ (h m hm).trans ?_⟩
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    rw [Real.sqrt_le_left (by positivity)]
    norm_cast
    nlinarith only [m.lt_succ_sqrt]

theorem linearithmic_iff_rlog {f : ℕ → ℕ} : f ∈ linearithmic ↔
    (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ x * Real.log x) := by
  have h_log_equiv : (fun x : ℕ ↦ (Nat.log 2 x : ℝ)) =O[.atTop] (Real.log ·) ∧
      (fun x : ℕ ↦ Real.log x) =O[.atTop] (fun x : ℕ ↦ (Nat.log 2 x : ℝ)) := by
    constructor <;> rw [Asymptotics.isBigO_iff]
    · use 1 / Real.log 2
      field_simp
      filter_upwards [Filter.eventually_gt_atTop 1] with x hx
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
        ← Real.log_rpow zero_lt_two]
      exact Real.log_le_log (by positivity) (mod_cast Nat.pow_log_le_self 2 <| by linarith)
    · -- We use `x < 2^(Nat.log 2 x + 1)` to show `Real.log x < (Nat.log 2 x + 1) * Real.log 2`.
      have h_log_bound : ∀ x : ℕ, x ≥ 2 → Real.log x < (Nat.log 2 x + 1) * Real.log 2 := by
        intro x hx; rw [← Real.log_rpow zero_lt_two]
        gcongr
        norm_cast
        exact Nat.lt_pow_succ_log_self one_lt_two _
      use 2 * Real.log 2
      filter_upwards [Filter.eventually_ge_atTop 2] with x hx
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      nlinarith [h_log_bound x hx, Real.log_pos one_lt_two,
        show (Nat.log 2 x : ℝ) ≥ 1 from mod_cast Nat.le_log_of_pow_le (by norm_num) (by linarith)]
  constructor <;> intro h
  · have h_combined : (fun x : ℕ ↦ (f x : ℝ)) =O[.atTop] (fun x : ℕ ↦ (x * Nat.log 2 x : ℝ)) := by
      have h_def : (fun x : ℕ ↦ (f x : ℝ)) =O[.atTop] (fun x : ℕ ↦ (x * Nat.log 2 x : ℝ)) := by
        convert h using 1
        simp [linearithmic, bigO]
        norm_num [Asymptotics.isBigO_iff]
      exact h_def
    apply h_combined.trans
    exact (Asymptotics.isBigO_refl _ _).mul h_log_equiv.1
  · have h_equiv : (fun x : ℕ ↦ (f x : ℝ)) =O[.atTop] (fun x : ℕ ↦ x * (Nat.log 2 x : ℝ)) := by
      exact h.trans (by simpa using (Asymptotics.isBigO_refl _ _).mul h_log_equiv.2)
    convert h_equiv using 1
    simp [bigO]
    norm_num [Asymptotics.isBigO_iff]

theorem quasilinear_iff_rlog {f : ℕ → ℕ} : f ∈ quasilinear ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ n * (Real.log n) ^ C : ℕ → ℝ) := by
  constructor
  · rintro ⟨C, hC⟩
    have h_log : (fun n ↦ (Nat.log 2 n : ℝ)) =O[.atTop] (fun n ↦ Real.log n) := by
      rw [Asymptotics.isBigO_iff]
      -- We choose `c = 1 / log 2`.
      use 1 / Real.log 2
      filter_upwards [Filter.eventually_gt_atTop 1] with x hx using by
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        simpa using Real.log_le_log (by positivity)
          (show (x : ℝ) ≥ 2 ^ Nat.log 2 x by exact_mod_cast Nat.pow_log_le_self 2 (by linarith))
    have h_replace : (fun n ↦ (n * Nat.log 2 n ^ C : ℝ)) =O[.atTop]
        (fun n ↦ (n * Real.log n ^ C : ℝ)) := by
      exact Asymptotics.IsBigO.mul (Asymptotics.isBigO_refl _ _) (h_log.pow _)
    have h_trans : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ (n * Nat.log 2 n ^ C : ℝ)) := by
      rw [Asymptotics.isBigO_iff] at *; aesop
    exact ⟨C, h_trans.trans h_replace⟩
  · simp only [forall_exists_index]
    intros C hC
    have h_nat_log : ∃ C' : ℕ, (fun x ↦ (f x : ℝ)) =O[.atTop]
        (fun n ↦ (n : ℝ) * (Nat.log 2 n) ^ C') := by
      refine ⟨C, hC.trans ?_⟩
      have h_log : (fun n : ℕ ↦ Real.log n) =O[.atTop] (fun n : ℕ ↦ (Nat.log 2 n : ℝ)) := by
        have h_log_eq : ∀ n : ℕ, n ≥ 2 → Real.log n ≤ Real.log 2 * Nat.log 2 n + Real.log 2 := by
          intro n hn
          have h_log : n ≤ 2 ^ (Nat.log 2 n + 1) :=
            (Nat.lt_pow_succ_log_self one_lt_two _).le
          have := (n : ℝ).log_le_log (y := 2 ^ (Nat.log 2 n + 1)) (by positivity) (mod_cast h_log)
          norm_num [Real.log_pow] at this
          linarith
        rw [Asymptotics.isBigO_iff]
        refine ⟨Real.log 2 + Real.log 2, Filter.eventually_atTop.mpr ⟨2, fun n hn ↦ ?_⟩⟩
        rw [Real.norm_of_nonneg (Real.log_nonneg (by norm_cast; linarith)),
          Real.norm_of_nonneg (Nat.cast_nonneg _)]
        nlinarith [h_log_eq n hn, Real.log_pos one_lt_two,
          show (Nat.log 2 n : ℝ) ≥ 1 from mod_cast Nat.le_log_of_pow_le one_lt_two (by linarith)]
      exact (Asymptotics.isBigO_refl _ _).mul (h_log.pow _)
    simpa [quasilinear, Asymptotics.isBigO_iff] using h_nat_log

theorem poly_iff_rpow {f : ℕ → ℕ} : f ∈ poly ↔
    ∃ (C : ℝ), (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ n ^ C : ℕ → ℝ) := by
  simp only [poly, Asymptotics.isBigO_iff, Int.norm_natCast, Filter.eventually_atTop,
     Set.mem_setOf_eq, Real.norm_eq_abs, Nat.abs_cast]
  use fun ⟨C, c, a, h⟩ ↦ ⟨C, c, a, fun b hb ↦ by simpa using h b hb⟩
  refine fun ⟨C, c, a, h⟩ ↦ ⟨⌈C⌉₊, c ⊔ 1, a + 1, fun b _ ↦ (h b (by linarith)).trans ?_⟩
  refine mul_le_mul (le_max_left c 1) ?_ (by positivity) (by positivity)
  rw [abs_of_nonneg (by positivity)]
  exact (Real.rpow_le_rpow_of_exponent_le (mod_cast by linarith) (Nat.le_ceil C)).trans (by simp)

lemma bigO_const_pow_log_le_two_pow_log (A : ℝ) (C : ℕ) :
    ∃ C' : ℕ, (fun n ↦ A ^ (Nat.log2 n ^ C)) =O[.atTop] (fun n ↦ (2 : ℝ) ^ (Nat.log2 n ^ C')) := by
  use C + 1
  -- Let `k = ⌈log₂ |A|⌉`. Then `|A| ≤ 2^k`.
  set k : ℕ := Nat.ceil (Real.logb 2 (|A|)) with hk
  -- Then `|A|^((log n)^C) ≤ (2^k)^((log n)^C) = 2^(k * (log n)^C)`.
  have h_bound : ∀ᶠ n in .atTop, |A| ^ (Nat.log2 n) ^ C ≤ (2 : ℝ) ^ (k * (Nat.log2 n) ^ C) := by
    have h_bound : |A| ≤ (2 : ℝ) ^ k := by
      by_cases hA : A = 0
      · norm_num [hA]
      · have h := Nat.le_ceil (Real.logb 2 |A|)
        rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity)] at h
        exact_mod_cast h
    simpa only [pow_mul] using .of_forall fun n ↦ pow_le_pow_left₀ (abs_nonneg _) h_bound _
  have h_const : ∃ N : ℕ, ∀ n ≥ N, k * (Nat.log2 n) ^ C ≤ (Nat.log2 n) ^ (C + 1) := by
    use 2 ^ (k + 1)
    intro n hn
    rw [pow_succ']
    gcongr
    rw [Nat.le_log2]
    · exact le_trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)) hn
    · linarith [Nat.pow_le_pow_right two_pos (show k + 1 ≥ 1 by norm_num)]
  apply Asymptotics.IsBigO.of_bound 1
  subst k
  simp only [norm_pow, Real.norm_eq_abs, one_mul, Filter.eventually_atTop]
  simp only [Real.logb_abs, Filter.eventually_atTop, Nat.abs_ofNat] at *
  refine ⟨Nat.max h_bound.choose h_const.choose, fun n hn ↦ ?_⟩
  exact (h_bound.choose_spec n (le_trans (Nat.le_max_left _ _) hn)).trans <|
    pow_le_pow_right₀ one_le_two (h_const.choose_spec n ((le_max_right _ _).trans hn))

theorem quasipoly_iff_real_two_pow {f : ℕ → ℕ} : f ∈ quasipoly ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ 2 ^ (Nat.log2 n ^ C) : ℕ → ℝ) := by
  simp [quasipoly, Asymptotics.isBigO_iff, Norm.norm, Nat.log2_eq_log_two]

theorem quasipoly_iff_real_const_pow {f : ℕ → ℕ} : f ∈ quasipoly ↔
    ∃ A C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ A ^ (Nat.log2 n ^ C) : ℕ → ℝ) := by
  rw [quasipoly_iff_real_two_pow]
  use (⟨2, ·⟩)
  rintro ⟨A, C, hC⟩
  exact (bigO_const_pow_log_le_two_pow_log A C).imp (fun _ ↦ hC.trans)

theorem e_pow_iff_rexp {f : ℕ → ℕ} : f ∈ e_pow ↔
    (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ Real.exp x) := by
  have h_ceil (n : ℕ) : ⌈(Real.exp n)⌉₊ ≤ 2 * (Real.exp n) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_nonneg n), Real.add_one_le_exp n]
  rw [e_pow, bigO, Set.mem_setOf]
  constructor
  · intro hf
    rw [Asymptotics.isBigO_iff'] at *
    simp only [norm_natCast, Filter.eventually_atTop, Real.norm_eq_abs, Real.abs_exp] at *
    obtain ⟨c, hc, a, ha⟩ := hf
    exact ⟨c * 2, mul_pos hc zero_lt_two, a, fun n hn ↦ by nlinarith [ha n hn, h_ceil n]⟩
  · intro hf
    rw [Asymptotics.isBigO_iff] at *
    obtain ⟨c, hc⟩ := hf
    simp only [norm, Nat.abs_cast, Real.abs_exp, Filter.eventually_atTop, Int.cast_natCast] at *
    refine ⟨c * 2, hc.choose, fun n hn ↦ ?_⟩
    nlinarith [hc.choose_spec n hn, h_ceil n, Real.exp_pos n, Nat.le_ceil (Real.exp n)]

theorem exp_iff_rpow {f : ℕ → ℕ} : f ∈ exp ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ C ^ x : ℕ → ℝ) := by
  constructor
  · rintro ⟨C, hC⟩
    use C
    simpa [Asymptotics.isBigO_iff] using hC
  · -- If there exists a real number `C` such that `f(n) = O(C^n)`, then there exists a
    -- natural number `k` such that `f(n) = O(k^n)`.
    rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (fun x ↦ (f x : ℝ)) =O[.atTop] (fun x ↦ (n : ℝ) ^ x) := by
      use ⌈|C|⌉₊
      apply hC.trans
      rw [Asymptotics.isBigO_iff]
      norm_num
      exact ⟨1, 0, fun n hn ↦ by grw [one_mul, ← Nat.le_ceil]⟩
    use n
    simpa [Asymptotics.isBigO_iff'] using hn

theorem exp_iff_rexp_mul {f : ℕ → ℕ} : f ∈ exp ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ Real.exp (C * x) : ℕ → ℝ) := by
  rw [exp_iff_rpow]
  constructor <;> rintro ⟨C, hC⟩
  · use Real.log (|C| + 1)
    apply hC.trans
    rw [Asymptotics.isBigO_iff]
    simp only [norm_pow, Real.norm_eq_abs, Real.abs_exp, Filter.eventually_atTop] at *
    refine ⟨1, 0, fun n hn ↦ ?_⟩
    rw [Real.exp_mul, Real.exp_log (by positivity)]
    norm_num
    exact pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg C]) _
  · use Real.exp C
    simpa [Real.exp_mul] using hC

end equivalent_defs

section closure_mul

variable {f g : ℕ → ℕ}

theorem polylog_mul (hf : f ∈ polylog) (hg : g ∈ polylog) : (f * g) ∈ polylog := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add]

theorem linear_of_sqrt_mul_sqrt (hf : f ∈ sqrt) (hg : g ∈ sqrt) : (f * g) ∈ linear := by
  convert (hf.mul hg).trans ?_
  rw [Asymptotics.isBigO_iff']
  simp only [norm_mul, norm_natCast, id_eq, Filter.eventually_atTop]
  exact ⟨1, by norm_num, 0, fun b hb ↦ by
    norm_cast; nlinarith [Nat.sqrt_le b]⟩

theorem linearithmic_of_linear_mul (hf : f ∈ linear) (hg : g ∈ log) : (f * g) ∈ linearithmic := by
  exact Asymptotics.IsBigO.mul hf hg

theorem quasilinear_mul_polylog (hf : f ∈ quasilinear) (hg : g ∈ polylog) :
    (f * g) ∈ quasilinear := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add, mul_assoc]

theorem poly_mul (hf : f ∈ poly) (hg : g ∈ poly) : (f * g) ∈ poly := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add]

theorem quasipoly_mul (hf : f ∈ quasipoly) (hg : g ∈ quasipoly) : (f * g) ∈ quasipoly := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  simp only [quasipoly, Set.mem_setOf_eq, Pi.mul_apply, Nat.cast_mul]
  use a + b
  convert (ha.mul hb).trans ?_
  norm_num [Asymptotics.isBigO_iff, Norm.norm]
  use 2, 2, fun k hk ↦ ?_
  have hl := Nat.log_pos one_lt_two hk
  rw [← pow_succ', Nat.pow_add, ← pow_add]
  apply pow_le_pow_right₀ one_le_two
  nlinarith [pow_pos hl a, pow_pos hl b]

theorem e_pow_of_two_pow_mul_quasipoly (hf : f ∈ two_pow) (hg : g ∈ quasipoly) :
    (f * g) ∈ e_pow := by
  simp only [two_pow, bigO, Nat.cast_pow, Nat.cast_ofNat, Set.mem_setOf_eq, quasipoly, e_pow,
    Pi.mul_apply, Nat.cast_mul] at *
  simp only [Asymptotics.isBigO_iff', norm_natCast, norm_pow, Filter.eventually_atTop] at hf hg
  simp only [Asymptotics.isBigO_iff, norm_mul, norm_natCast, Filter.eventually_atTop]
  obtain ⟨c₁, hc₁, k₁, h₁⟩ := hf
  obtain ⟨C, c₂, hc₂, k₂, h₂⟩ := hg
  use c₁
  suffices hs : ∃ k, ∀ b ≥ k, (2 ^ b) * (c₂ * 2 ^ Nat.log 2 b ^ C) ≤ ⌈Real.exp b⌉₊ by
    rcases hs with ⟨k, hk⟩
    use k ⊔ k₁ ⊔ k₂
    intro b hb
    specialize h₁ b ((le_max_right _ _).trans <| (le_max_left _ _).trans hb)
    specialize h₂ b ((le_max_right _ _).trans hb)
    specialize hk b ((le_max_left _ _).trans <| (le_max_left _ _).trans hb)
    simp only [norm, Int.cast_ofNat, Nat.abs_ofNat] at h₁ h₂
    trans (c₁ * 2 ^ b) * (c₂ * 2 ^ Nat.log 2 b ^ C)
    · gcongr
    · rw [mul_assoc]
      gcongr
  clear c₁ hc₁ k₁ h₁ k₂ h₂
  -- Simplifying the goal using properties of exponential functions and logs
  suffices h_exp_log : ∃ k : ℕ, ∀ b ≥ k, c₂ * 2 ^ (b + Nat.log 2 b ^ C) ≤ Nat.ceil (Real.exp b) by
    simpa only [mul_assoc, mul_comm, mul_left_comm, pow_add] using h_exp_log
  suffices h_exp_log : ∃ k : ℕ, ∀ b ≥ k, c₂ * 2 ^ (b + Nat.log 2 b ^ C) ≤ Real.exp b by
    exact ⟨h_exp_log.choose, fun n hn ↦ by
      simpa only [pow_add, mul_assoc] using (h_exp_log.choose_spec n hn).trans (Nat.le_ceil _)⟩
  -- By dividing both sides of the inequality by `2^b`, we reduce to showing
  -- `c₂ * 2 ^ ((log₂ b) ^ C) ≤ exp(b * (1 - log 2))`.
  suffices h₂ : ∃ k : ℕ, ∀ b ≥ k, c₂ * 2 ^ (Nat.log 2 b ^ C) ≤ Real.exp (b * (1 - Real.log 2)) by
    refine h₂.imp (fun k hk b hb ↦ ?_)
    rw [pow_add, ← mul_comm]
    specialize hk b hb
    convert mul_le_mul_of_nonneg_left hk <| pow_nonneg zero_le_two b using 1
    · ring
    · rw [mul_sub, mul_one, Real.exp_sub]
      norm_num [Real.exp_neg, Real.exp_nat_mul, Real.exp_log, mul_div_cancel₀]
  suffices h_exp_poly : Filter.atTop.Tendsto (fun b : ℕ ↦
      (2 ^ (Nat.log 2 b ^ C) : ℝ) / Real.exp (b * (1 - Real.log 2))) (𝓝 0) by
    have := h_exp_poly.eventually (gt_mem_nhds <| show 0 < c₂⁻¹ by positivity)
    rw [Filter.eventually_atTop] at this
    peel this with _ n _ this
    rw [div_lt_iff₀ (Real.exp_pos _)] at this
    nlinarith [Real.exp_pos (n * (1 - Real.log 2)), inv_mul_cancel₀ hc₂.ne']
  suffices h_log : Filter.atTop.Tendsto (fun y : ℕ ↦
      (2 ^ (y ^ C) : ℝ) / Real.exp (2 ^ y * (1 - Real.log 2))) (𝓝 0) by
    refine squeeze_zero_norm' ?_ (h_log.comp (f := Nat.log 2) ?_)
    · simp only [norm_div, norm_pow, Real.norm_ofNat, Real.norm_eq_abs, Real.abs_exp,
        Function.comp_apply, Filter.eventually_atTop]
      refine ⟨4, fun n hn ↦ ?_⟩
      gcongr
      · linarith [Real.log_le_sub_one_of_pos zero_lt_two]
      · exact_mod_cast Nat.pow_log_le_self 2 <| by linarith
    · rw [Filter.tendsto_atTop_atTop]
      exact fun b ↦ ⟨2 ^ b, fun a ha ↦ Nat.le_log_of_pow_le (by norm_num) ha⟩
  suffices h_ln : Filter.atTop.Tendsto (fun y : ℕ ↦
      y ^ C * Real.log 2 - 2 ^ y * (1 - Real.log 2)) .atBot by
    -- If the natural logarithm of the expression tends to `-∞`, then the expression tends to `0`.
    have h_exp_ln : Filter.Tendsto (fun y : ℕ ↦ Real.exp _) .atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h_ln
    convert h_exp_ln using 2
    norm_num [Real.exp_sub, Real.exp_nat_mul, Real.exp_log]
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
    norm_num [mul_comm]
  have h_exp_poly : Filter.Tendsto (fun y : ℕ ↦ (2 : ℝ) ^ y / y ^ C) .atTop .atTop := by
    suffices h_exp : Filter.Tendsto (fun x : ℝ ↦ Real.exp (x * Real.log 2) / x ^ C) .atTop .atTop by
      convert h_exp.comp tendsto_natCast_atTop_atTop using 2
      norm_num [Real.exp_nat_mul, Real.exp_log]
    suffices h_limit_y : Filter.Tendsto (fun y : ℝ ↦ Real.exp y / y ^ C) .atTop .atTop by
      have h_subst : Filter.Tendsto (fun x : ℝ ↦
          Real.exp (x * Real.log 2) / (x * Real.log 2) ^ C) .atTop .atTop := by
        exact h_limit_y.comp <| Filter.tendsto_id.atTop_mul_const <| Real.log_pos <| by norm_num
      have h_simplify : Filter.Tendsto (fun x : ℝ ↦
          Real.exp (x * Real.log 2) / x ^ C / (Real.log 2) ^ C) .atTop .atTop := by
        simpa only [mul_pow, div_div] using h_subst
      convert h_simplify.atTop_mul_const (pow_pos (Real.log_pos one_lt_two) C) using 2
      ring_nf
      norm_num [mul_assoc, mul_comm, mul_left_comm]
    exact Real.tendsto_exp_div_pow_atTop _
  have h_rewrite : Filter.atTop.Tendsto (fun y : ℕ ↦
      (y ^ C : ℝ) * (Real.log 2 - (2 ^ y * (1 - Real.log 2)) / y ^ C)) .atBot := by
    have h_ln_tendsto : Filter.atTop.Tendsto (fun y : ℕ ↦
        Real.log 2 - (2 ^ y * (1 - Real.log 2)) / y ^ C) .atBot := by
      have h_mul : Filter.atTop.Tendsto (fun y : ℕ ↦ 2 ^ y * (1 - Real.log 2) / y ^ C) .atTop := by
        simpa only [mul_div_right_comm] using h_exp_poly.atTop_mul_const (sub_pos.mpr <|
          Real.log_two_lt_d9.trans_le <| by norm_num)
      rw [Filter.tendsto_atTop_atBot]
      exact fun x ↦ Filter.eventually_atTop.mp (h_mul.eventually_gt_atTop (Real.log 2 - x)) |>
        fun ⟨N, hN⟩ ↦ ⟨N, fun n hn ↦ by linarith [hN n hn]⟩
    rw [Filter.tendsto_atTop_atBot] at *
    intro b
    obtain ⟨i, hi⟩ := h_ln_tendsto (b ⊓ 0)
    refine ⟨i + 1, fun j hj ↦ ?_⟩
    refine le_trans (mul_le_mul_of_nonneg_left (hi _ (by linarith)) (by positivity)) ?_
    nlinarith [min_le_left b 0, min_le_right b 0,
        show (j:ℝ) ^ C ≥ 1 from one_le_pow₀ (by norm_cast; linarith)]
  exact h_rewrite.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with y hy using (by
    rw [mul_sub, mul_div_cancel₀ _ (by positivity)]))

theorem exp_mul (hf : f ∈ exp) (hg : g ∈ exp) : (f * g) ∈ exp := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  use a * b
  simp only [Nat.cast_mul, mul_pow]
  exact ha.mul hb

theorem primitiveRecursive_mul (hf : f ∈ primitiveRecursive) (hg : g ∈ primitiveRecursive) :
    (f * g) ∈ primitiveRecursive := by
  rcases hf with ⟨a, ha₁, ha₂⟩
  rcases hg with ⟨b, hb₁, hb₂⟩
  use a * b
  rw [← Primrec.nat_iff] at *
  use Primrec.nat_mul.comp ha₁ hb₁
  exact ha₂.mul hb₂

theorem computable_mul (hf : f ∈ computable) (hg : g ∈ computable) :
    (f * g) ∈ computable := by
  rcases hf with ⟨a, ha₁, ha₂⟩
  rcases hg with ⟨b, hb₁, hb₂⟩
  use a * b
  use Primrec.nat_mul.to_comp.comp ha₁ hb₁
  exact ha₂.mul hb₂

end closure_mul

section ordering

theorem const_subset_log : const ⊆ log := by
  refine fun _ h ↦ h.trans ?_
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨1, 2, fun _ hn ↦ ?_⟩
  exact one_le_mul_of_one_le_of_one_le le_rfl (mod_cast Nat.le_log_of_pow_le one_lt_two hn)

theorem const_ssubset_log : const ⊂ log := by
  simp only [const, log, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset,
    Pi.one_apply, Nat.cast_one]
  use const_subset_log
  simp only [Asymptotics.isBigO_one_iff, Int.norm_natCast, not_forall]
  use Nat.log 2, Asymptotics.isBigO_refl _ _
  norm_num [Filter.IsBoundedUnder, Filter.IsBounded]
  intro x n
  rcases exists_nat_gt x with ⟨k, hk⟩
  refine ⟨2 ^ (n + k + 1), ?_, ?_⟩
  · linarith [(n + k + 1).lt_two_pow_self]
  · rw [Nat.log_pow (by norm_num)]
    push_cast
    linarith

theorem log_ssubset_polylog : log ⊂ polylog := by
  rw [log, polylog, ssubset_iff_subset_not_subset]
  simp only [bigO, Set.setOf_subset_setOf, forall_exists_index, not_forall]
  use fun f h ↦ ⟨1, by simpa [pow_one] using h⟩
  use fun n ↦ (Nat.log 2 n) ^ 2, 2, Asymptotics.isBigO_refl ..
  simp only [Classical.not_imp, Nat.cast_pow, Asymptotics.isBigO_iff, norm_pow, norm_natCast,
    Filter.eventually_atTop, not_exists, not_forall, not_le]
  intro x y
  obtain ⟨n, hn⟩ := exists_nat_gt x
  refine ⟨2 ^ (y + n + 1), ?_, ?_⟩
  · linarith [(y + n + 1).lt_two_pow_self]
  · simp only [one_lt_two, Nat.log_pow, Nat.cast_add, Nat.cast_one]
    nlinarith

/-
For f ∈ polylog, there exists k with f = O((log n)^k). We need f ∈ sqrt = bigO(Nat.sqrt).
Since (log n)^k / √n → 0 as n → ∞ (any power of log grows slower than √n), eventually
(log n)^k ≤ √n. From f(n) ≤ c * (log n)^k and (log n)^k ≤ √n eventually, we get
f(n) ≤ c * √n eventually.
-/
theorem polylog_subset_sqrt : polylog ⊆ sqrt := by
  intro f hf
  suffices h : ∃ N, ∀ n ≥ N, (f n : ℝ) ≤ (Nat.sqrt n : ℝ) by
    obtain ⟨N, hN⟩ := h
    simp_rw [sqrt, bigO, Set.mem_setOf, Asymptotics.isBigO_iff, Filter.eventually_atTop]
    exact ⟨1, N, (by simpa using hN · ·)⟩
  rcases hf with ⟨C, hC⟩
  have h_bound : Filter.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / √n) .atTop (𝓝 0) := by
    -- We can convert this statement into a form that allows us to apply the squeeze theorem.
    suffices h_convert : Filter.atTop.Tendsto (fun n : ℕ ↦ (Real.logb 2 n) ^ C / √n) (𝓝 0) by
      refine squeeze_zero_norm' ?_ h_convert
      norm_num [abs_div, abs_of_nonneg, Real.sqrt_nonneg]
      refine ⟨2, fun n hn ↦ ?_⟩
      gcongr
      rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
      exact Real.log_le_log (by positivity) (mod_cast Nat.pow_log_le_self _ <| by positivity)
    -- We apply the squeeze theorem by substituting `y = log n`.
    suffices h_convert : Filter.atTop.Tendsto (fun y ↦ (y / Real.log 2) ^ C / (y / 2).exp) (𝓝 0) by
      have := h_convert.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      apply this.congr'
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [Real.logb, Function.comp_apply, Function.comp_apply, Real.sqrt_eq_rpow,
        Real.rpow_def_of_pos (by positivity)]
      ring_nf
    -- We simplify the expression inside the limit further by substituting `z = y / 2`.
    suffices h_simp : Filter.atTop.Tendsto (fun z ↦ (2 * z / Real.log 2) ^ C / z.exp) (𝓝 0) by
      convert h_simp.comp (Filter.tendsto_id.atTop_mul_const (by norm_num : 0 < (2⁻¹ : ℝ))) using 2
      norm_num
      ring_nf
    suffices h_factor : Filter.atTop.Tendsto (fun z : ℝ ↦ z ^ C / z.exp) (𝓝 0) by
      convert h_factor.const_mul ((2 / Real.log 2) ^ C) using 2
      · ring
      · ring
    simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C
  obtain ⟨k, hk⟩ : ∃ k, ∀ᶠ n in .atTop, (f n : ℝ) ≤ k * (Nat.log 2 n : ℝ) ^ C := by
    rw [Asymptotics.isBigO_iff'] at hC; aesop
  have h_combined : ∃ N, ∀ n ≥ N, (k * (Nat.log 2 n : ℝ) ^ C) / √n ≤ 1 := by
    simpa [mul_div_assoc] using (h_bound.const_mul k).eventually (ge_mem_nhds <| by simp)
  obtain ⟨N, hN⟩ := h_combined
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hk
  use N ⊔ M + 1
  intro n hn
  specialize hN n (by linarith [le_max_left N M, le_max_right N M])
  specialize hM n (by linarith [le_max_left N M, le_max_right N M])
  rw [div_le_iff₀] at hN
  · rw [Nat.cast_le, Nat.le_sqrt, ← @Nat.cast_le ℝ, Nat.cast_mul]
    nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg n)]
  · grind [Real.sqrt_pos, Nat.cast_pos]

theorem polylog_ssubset_sqrt : polylog ⊂ sqrt := by
  use polylog_subset_sqrt
  simp only [polylog, sqrt, bigO, Set.setOf_subset_setOf]
  push Not
  use Nat.sqrt, Asymptotics.isBigO_refl ..
  intro C
  refine Asymptotics.IsLittleO.not_isBigO ?_ (Filter.frequently_atTop.mpr (⟨· + 2, by simp⟩))
  rw [Asymptotics.isLittleO_iff]
  intro c a
  simp only [Nat.cast_pow, norm_pow, norm_natCast, Filter.eventually_atTop]
  have h_log_growth : Filter.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / √n) .atTop (𝓝 0) := by
    have h_log_growth : Filter.Tendsto (fun x : ℝ ↦ (Real.logb 2 x) ^ C / √x) .atTop (𝓝 0) := by
      suffices h : Filter.Tendsto (fun y : ℝ ↦ y ^ C / √(2 ^ y)) .atTop (𝓝 0) by
        have := h.comp (Real.tendsto_log_atTop.const_mul_atTop (by positivity : 0 < (Real.log 2)⁻¹))
        refine this.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop 0] with x hx
        field_simp
        simp only [Function.comp_apply, Real.logb]
        -- Simplify the denominator: `√(2^((log x) / log 2)) = √x`.
        field_simp
        erw [Real.rpow_logb] <;> linarith
      suffices hy : Filter.atTop.Tendsto (fun y ↦ y ^ C / (y * Real.log 2 / 2).exp) (𝓝 0) by
        convert hy using 2; norm_num [Real.sqrt_eq_rpow, Real.rpow_def_of_pos]
        ring_nf
        rw [← Real.exp_mul]
      suffices h_log : Filter.Tendsto (fun z ↦ (2 * z / Real.log 2) ^ C / z.exp) .atTop (𝓝 0) by
        have h_log : Filter.atTop.Tendsto (fun y : ℝ ↦
            ((2 * (y * Real.log 2 / 2)) / Real.log 2) ^ C / (y * Real.log 2 / 2).exp) (𝓝 0) := by
          exact h_log.comp <| Filter.Tendsto.atTop_mul_const (by positivity) <|
            Filter.tendsto_id.atTop_mul_const (by positivity)
        convert h_log using 3
        ring_nf
        norm_num
      suffices h_term : Filter.atTop.Tendsto (fun z : ℝ ↦ z ^ C / z.exp) (𝓝 0) by
        convert h_term.const_mul ((Real.log 2) ⁻¹ ^ C * 2 ^ C) using 2
        · ring
        · ring
      simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C
    refine squeeze_zero_norm' ?_ (h_log_growth.comp tendsto_natCast_atTop_atTop)
    refine Filter.eventually_atTop.mpr ⟨2, fun n hn ↦ ?_⟩
    rw [Function.comp_apply, Real.norm_of_nonneg (by positivity)]
    gcongr
    rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_rpow zero_lt_two]
    apply Real.log_le_log (by positivity)
    norm_cast
    exact Nat.pow_log_le_self _ (by positivity)
  have this := h_log_growth.eventually (gt_mem_nhds <| show 0 < c / 2 by positivity)
  rw [Filter.eventually_atTop] at this
  obtain ⟨w, h⟩ := this
  refine ⟨w + 4, fun n hn ↦ ?_⟩
  specialize h n (by linarith)
  rw [div_lt_iff₀ (by norm_num; linarith)] at h
  refine le_trans (le_of_lt h) ?_
  have _ : (√n:ℝ) ≤ Nat.sqrt n + 1 := Real.sqrt_le_iff.2
    ⟨by positivity, by norm_cast; nlinarith [Nat.lt_succ_sqrt n]⟩
  nlinarith [show (Nat.sqrt n:ℝ) ≥ 1 from Nat.one_le_cast.2 (n.sqrt_pos.2 (by linarith))]

theorem sqrt_subset_sublinear : sqrt ⊆ sublinear := by
  simp only [sqrt, bigO, sublinear]
  intro f hf
  refine hf.trans_isLittleO ?_; clear f hf
  erw [Asymptotics.isLittleO_iff]
  intro c a
  simp only [Int.norm_natCast, Filter.eventually_atTop, id_eq]
  use Nat.ceil ((1 / c) ^ 2)
  intro b hb
  have h : (1 : ℝ) / c ≤ √b := (Real.le_sqrt_of_sq_le <| by simpa using hb)
  rw [div_le_iff₀ (by positivity)] at h
  have _ : b.sqrt  ≤ √(b : ℝ) := Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' b
  nlinarith [Real.sq_sqrt <| Nat.cast_nonneg b]

theorem sqrt_ssubset_sublinear : sqrt ⊂ sublinear := by
  use sqrt_subset_sublinear
  simp only [sqrt, sublinear, bigO]
  norm_num [littleO]
  use fun n ↦ Nat.sqrt n * Nat.log 2 n
  simp only [Nat.cast_mul]
  constructor
  · refine Asymptotics.isLittleO_iff.2 fun ε hε ↦ ?_
    have h_log_div : Filter.Tendsto (fun x : ℕ ↦ (Nat.log 2 x : ℝ) / √x) .atTop (𝓝 0) := by
      -- We use the change of variables `u = log₂ x` to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun u : ℝ ↦ u / 2^(u/2)) .atTop (𝓝 0) by
        have h_log : Filter.Tendsto (fun x : ℕ ↦
            (Nat.log 2 x : ℝ) / 2 ^ (Nat.log 2 x / 2 : ℝ)) .atTop (𝓝 0) := by
          apply h_log.comp
          apply tendsto_natCast_atTop_atTop.comp
          rw [Filter.tendsto_atTop_atTop]
          exact fun n ↦ ⟨2 ^ n, fun x hx ↦ Nat.le_log_of_pow_le (by norm_num) hx⟩
        refine squeeze_zero_norm' ?_ h_log
        simp only [norm_div, RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop]
        refine ⟨2, fun n hn ↦ ?_⟩
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        gcongr
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos, Real.rpow_def_of_pos] <;> norm_num
        · have := Real.log_le_log (by positivity)
            (show (n : ℝ) ≥ 2 ^ Nat.log 2 n by exact_mod_cast Nat.pow_log_le_self 2 (by positivity))
          norm_num at *
          nlinarith [Real.log_pos one_lt_two]
        · linarith
      suffices h_exp : Filter.atTop.Tendsto (fun u ↦ u / (u * Real.log 2 / 2).exp) (𝓝 0) by
        convert h_exp using 2
        norm_num [Real.rpow_def_of_pos]
        ring_nf
      suffices h_y : Filter.Tendsto (fun y : ℝ ↦ 2 * y / Real.exp y) .atTop (𝓝 0) by
        have h := h_y.comp (Filter.tendsto_id.atTop_mul_const (by positivity : 0 < Real.log 2 / 2))
        convert h.div_const (Real.log 2) using 2 <;> norm_num
        ring_nf
        norm_num [mul_assoc, mul_comm, mul_left_comm]
      simpa [mul_div_assoc, Real.exp_neg] using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 2
    replace h_log_div := h_log_div.eventually (gt_mem_nhds <| show 0 < ε by positivity)
    simp only [Filter.eventually_atTop, norm_mul, norm_natCast] at h_log_div ⊢
    rcases h_log_div with ⟨w, h⟩
    refine ⟨w + 1, fun n hn ↦ ?_⟩
    specialize h n (by linarith)
    rw [div_lt_iff₀] at h
    · nlinarith [show (Nat.sqrt n : ℝ) ≤ √n from Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' n,
        Real.mul_self_sqrt <| Nat.cast_nonneg n,
        show (Nat.log 2 n : ℝ) ≥ 0 by positivity]
    · norm_num at *
      linarith
  · intro a
    contrapose! a
    rw [Asymptotics.isBigO_iff]
    simp only [norm_mul, norm_natCast, Filter.eventually_atTop, not_exists, not_forall,
      not_le]
    intro x x₁
    have h_log_growth : Filter.atTop.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) - x) .atTop := by
      refine Filter.tendsto_atTop_add_const_right _ _ <| tendsto_natCast_atTop_atTop.comp ?_
      rw [Filter.tendsto_atTop_atTop]
      exact (⟨2 ^ ·, fun _ ↦ Nat.le_log_of_pow_le one_lt_two⟩)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h_log_growth.eventually_gt_atTop 0)
    use x₁ + N + 1, by linarith
    have _ : (Nat.sqrt (x₁ + N + 1) : ℝ) ≥ 1 := mod_cast Nat.sqrt_pos.mpr (by linarith)
    specialize hN (x₁ + N + 1) (by linarith)
    nlinarith

theorem sublinear_ssubset_linear : sublinear ⊂ linear := by
  simp only [littleO, linear, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset]
  push Not
  use fun _ ↦ Asymptotics.IsLittleO.isBigO, id, Asymptotics.isBigO_refl ..
  apply Asymptotics.isLittleO_irrefl'
  apply Filter.Eventually.frequently
  rw [Filter.eventually_atTop]
  use 1
  intro b hb
  simp [Nat.ne_zero_of_lt hb]

theorem linear_subset_linearithmic : linear ⊆ linearithmic := by
  refine fun _ h ↦ h.trans ?_
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨1, 2, fun n hn ↦ ?_⟩
  rw [one_mul]
  exact_mod_cast Nat.le_mul_of_pos_right n (Nat.log_pos one_lt_two hn)

theorem linear_ssubset_linearithmic : linear ⊂ linearithmic := by
  use linear_subset_linearithmic
  simp only [linearithmic, bigO, Nat.cast_mul, linear, id_eq, Set.setOf_subset_setOf, not_forall]
  use fun n ↦ n * Nat.log 2 n
  use mod_cast Asymptotics.isBigO_refl ..
  norm_num [Asymptotics.isBigO_iff]
  intro x k
  have ⟨n, hn⟩ := exists_nat_gt (|x| + 1)
  use 2 ^ (k + n)
  norm_num [Nat.log_pow]
  constructor
  · linarith [(k + n).lt_two_pow_self]
  · nlinarith [abs_lt.mp (show |x| < n by linarith), pow_pos (M₀ := ℝ) two_pos (k + n)]

theorem linearithmic_subset_quasilinear : linearithmic ⊆ quasilinear :=
  fun _ _ ↦ ⟨1, by simpa⟩

theorem linearithmic_ssubset_quasilinear : linearithmic ⊂ quasilinear := by
  use linearithmic_subset_quasilinear
  simp only [quasilinear, bigO, Set.setOf_subset_setOf, not_forall, exists_prop]
  use fun n ↦ n * (Nat.log 2 n) ^ 2
  use ⟨2, mod_cast Asymptotics.isBigO_refl ..⟩
  norm_num [Asymptotics.isBigO_iff', ← mul_assoc]
  intro x _ y
  have ⟨n, _⟩ := exists_nat_gt x
  refine ⟨2 ^ (y + n + 1), le_trans (by linarith) Nat.lt_two_pow_self.le, ?_⟩
  rw [Nat.log_pow Nat.one_lt_ofNat]
  push_cast
  nlinarith [(by positivity : 0 < (2 : ℝ) ^ (y + n + 1) * (y + n + 1))]

theorem quasilinear_subset_poly : quasilinear ⊆ poly := by
  simp only [quasilinear, poly, Set.setOf_subset_setOf, forall_exists_index]
  intro f C h
  use C + 1
  apply h.trans
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨1, 2, fun n hn ↦ ?_⟩; norm_num
  suffices h : (Nat.log 2 n : ℝ) ^ C ≤ (n : ℝ) ^ C by
    simpa [pow_succ'] using mul_le_mul_of_nonneg_left h <| Nat.cast_nonneg _
  gcongr
  exact (Nat.log_lt_of_lt_pow (by linarith) (by linarith [n.lt_two_pow_self])).le

theorem quasilinear_ssubset_poly : quasilinear ⊂ poly := by
  use quasilinear_subset_poly
  simp only [quasilinear, poly, Set.setOf_subset_setOf, not_forall, exists_prop]
  use (· ^ 2)
  use ⟨2, mod_cast Asymptotics.isBigO_refl ..⟩
  norm_num [Asymptotics.isBigO_iff']
  intro x y hy z
  have h_exp : Filter.atTop.Tendsto (fun n : ℕ ↦ n * (Nat.log 2 n : ℝ) ^ x / n ^ 2) (𝓝 0) := by
    -- We can simplify the expression inside the limit.
    suffices hs : Filter.atTop.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ x / n) (𝓝 0) by
      apply hs.congr'
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [div_eq_div_iff] <;> ring_nf <;> positivity
    suffices h_log : Filter.atTop.Tendsto (fun y : ℕ ↦ (y : ℝ) ^ x / (2 ^ y)) (𝓝 0) by
      have h_subst : Filter.atTop.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ x / _) (𝓝 0) :=
        h_log.comp <| Filter.tendsto_atTop_atTop.mpr <|
          (⟨2 ^ ·, fun m ↦ Nat.le_log_of_pow_le one_lt_two⟩)
      refine squeeze_zero_norm' ?_ h_subst
      filter_upwards [Filter.eventually_gt_atTop 1] with n hn
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      norm_cast
      exact Nat.pow_log_le_self 2 (Nat.ne_zero_of_lt hn)
    -- We substitute `z = y * log 2` to simplify.
    suffices h_log : Filter.Tendsto (fun z : ℝ ↦ z ^ x / Real.exp z) .atTop (𝓝 0) by
      have := h_log.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two))
      convert this.div_const (Real.log 2 ^ x) using 2 <;> norm_num [Real.exp_nat_mul, Real.exp_log]
      ring_nf
      norm_num [ne_of_gt, Real.log_pos]
    simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero x
  have h := h_exp.eventually (gt_mem_nhds <| show 0 < y⁻¹ by positivity)
  rw [Filter.eventually_atTop] at h
  rcases h with ⟨N, hN⟩
  use N + z + 1, by linarith
  specialize hN (N + z + 1) (by linarith)
  rw [div_lt_iff₀ (by positivity)] at hN
  nlinarith [inv_mul_cancel₀ hy.ne', pow_pos (a := (N + z + 1 : ℝ)) (by positivity) 2]

theorem poly_subset_quasipoly : poly ⊆ quasipoly := by
  refine fun f ⟨c, hf⟩ ↦ ⟨c + 1, hf.trans ?_⟩
  simp only [Asymptotics.isBigO_iff, norm_pow, Int.norm_natCast, Filter.eventually_atTop]
  use 1, 2 ^ (c + 1)
  intro b hb
  erw [Real.norm_of_nonneg <| by positivity]
  have h : (b : ℝ) ^ c ≤ (2 : ℝ) ^ ((Nat.log 2 b) * (c + 1)) := by
    have h₁ : b ^ c ≤ 2 ^ ((Nat.log 2 b) * c) * 2 ^ c := by
      rw [pow_mul, ← mul_pow, ← pow_succ]
      exact_mod_cast Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self one_lt_two b).le c
    norm_cast
    rw [Nat.mul_succ, pow_add]
    refine h₁.trans <| Nat.mul_le_mul_left _ ?_
    refine pow_le_pow_right₀ one_le_two <| Nat.le_log_of_pow_le one_lt_two ?_
    linarith [pow_succ 2 c]
  apply h.trans
  rcases hk : Nat.log 2 b with (_ | k)
  · simp
  rcases c with (_ | c)
  · simp
  rw [one_mul]
  apply pow_le_pow_right₀ one_le_two
  norm_num [Nat.log_eq_iff, Nat.pow_succ, mul_comm (k + 1)] at *
  have h₂ : 1 < k + 1 := Nat.succ_lt_succ <| Nat.pos_of_ne_zero <| by
    rintro rfl
    linarith [c.lt_two_pow_self]
  nlinarith [c.lt_pow_self h₂, (2).lt_pow_self h₂]

theorem poly_ssubset_quasipoly : poly ⊂ quasipoly := by
  use poly_subset_quasipoly
  simp only [exists_and_right, Classical.not_imp, quasipoly, poly, Set.setOf_subset_setOf,
    forall_exists_index, not_forall, not_exists]
  use fun n ↦ 2 ^ (Nat.log 2 n) ^ 2
  use ⟨2, mod_cast Asymptotics.isBigO_refl ..⟩
  intro k hk
  rw [Asymptotics.isBigO_iff'] at hk
  simp only [Nat.cast_pow, Nat.cast_ofNat, norm_pow, norm_natCast, Filter.eventually_atTop] at hk
  rcases hk with ⟨c, hc₀, a, ha⟩
  -- Choose `b = 2^m` for some `m` large enough such that `2^(m^2) > c * (2^m)^k`.
  have ⟨m, hm⟩ : ∃ m : ℕ, m > a ∧ 2 ^ (m ^ 2) > c * (2 ^ m) ^ k := by
    -- We choose `m` large enough such that `2^(m^2) > c * 2^(mk)`
    have ⟨m, hm₁, hm₂⟩ : ∃ m : ℕ, m > a ∧ m^2 > m * k + Real.logb 2 c := by
      use a + k + ⌊Real.logb 2 c⌋₊ + 1, by linarith
      push_cast
      nlinarith [Nat.lt_floor_add_one (Real.logb 2 c)]
    use m
    rw [gt_iff_lt, Real.logb, add_div', div_lt_iff₀] at hm₂ <;> norm_num at *
    · use hm₁
      rw [← Real.log_lt_log_iff (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      norm_num
      linarith
    · positivity
  specialize ha (2 ^ m) (hm.1.le.trans m.lt_two_pow_self.le)
  norm_num [Norm.norm] at ha
  order

lemma polylog_is_littleO_sqrt {f : ℕ → ℕ} (hf : f ∈ polylog) :
    (fun n ↦ (f n : ℝ)) =o[.atTop] (√·) := by
  have h_log_poly : ∀ w : ℕ, (fun n ↦ (Nat.log 2 n : ℝ) ^ w) =o[.atTop] (√·) := by
    intro w
    have h_log : Filter.atTop.Tendsto (fun n ↦ (Real.log n / Real.log 2) ^ w / √n) (𝓝 0) := by
      suffices hs : Filter.Tendsto (fun n ↦ (Real.log n) ^ w / √n) .atTop (𝓝 0) by
        convert hs.div_const (Real.log 2 ^ w) using 2 <;> ring
      suffices h_log : Filter.Tendsto (fun y ↦ y ^ w / Real.exp (y / 2)) .atTop (𝓝 0) by
        have := h_log.comp (Real.tendsto_log_atTop)
        apply this.congr'
        filter_upwards [Filter.eventually_gt_atTop 0] with x hx
        rw [Function.comp_apply, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
        ring_nf
      suffices h_z : Filter.Tendsto (fun z ↦ (2 * z) ^ w / Real.exp z) .atTop (𝓝 0) by
        convert h_z.comp (Filter.tendsto_id.atTop_mul_const (by norm_num : 0 < (2⁻¹ : ℝ))) using 2
        norm_num
        ring_nf
      suffices h_factor : Filter.Tendsto (fun z ↦ z ^ w / Real.exp z) .atTop (𝓝 0) by
        convert h_factor.const_mul (2 ^ w) using 2 <;> ring
      simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero w
    rw [Asymptotics.isLittleO_iff_tendsto']
    · have h_log : Filter.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ w / √n) .atTop (𝓝 0) := by
        have : ∀ n : ℕ, n ≥ 2 → (Nat.log 2 n) ^ w / √n ≤ (Real.log n / Real.log 2) ^ w / √n := by
          intro n hn; gcongr
          rw [le_div_iff₀ (Real.log_pos (by norm_num)), ← Real.log_pow]
          exact Real.log_le_log (by positivity) (mod_cast Nat.pow_log_le_self _ (by positivity))
        refine squeeze_zero_norm' ?_ (h_log.comp tendsto_natCast_atTop_atTop)
        rw [Filter.eventually_atTop]
        use 2
        exact fun n ↦ by rw [Real.norm_of_nonneg (by positivity)]; exact this n
      convert h_log using 1
    · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' <| by positivity
  rcases hf with ⟨w, hw⟩
  have h_log_poly : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℝ) ^ w) := by
    rw [Asymptotics.isBigO_iff] at *
    aesop
  exact h_log_poly.trans_isLittleO (by aesop)

theorem quasipoly_subset_two_pow : quasipoly ⊆ two_pow := by
  rintro f ⟨C, hC⟩
  suffices h_exp :(fun n ↦ 2 ^ (Nat.log 2 n ^ C) : ℕ → ℤ) =O[.atTop] (fun n ↦ 2 ^ n : ℕ → ℤ) by
    simpa [two_pow, bigO] using hC.trans h_exp
  suffices h_exp : ∀ᶠ n in .atTop, (Nat.log 2 n ^ C : ℕ) ≤ n by
    rw [Asymptotics.isBigO_iff]
    norm_num +zetaDelta at *
    rcases h_exp with ⟨k, hk⟩
    refine ⟨1, k, fun n hn ↦ ?_⟩
    rw [one_mul]
    exact pow_le_pow_right₀ (by norm_num [Norm.norm]) (hk n hn)
  have h_log : Filter.atTop.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ C / n) (𝓝 0) := by
    -- We substitute `m = log₂ n`.
    suffices h_log : Filter.atTop.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ C / (2 ^ m : ℝ)) (𝓝 0) by
      have h_log : Filter.atTop.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / _) (𝓝 0) :=
        h_log.comp (Filter.tendsto_atTop_atTop.mpr <|
          (⟨2 ^ ·, fun n hn ↦ Nat.le_log_of_pow_le one_lt_two hn⟩))
      refine squeeze_zero_norm' ?_ h_log
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      norm_cast
      exact Nat.pow_log_le_self 2 hn.ne'
    -- We substitute `m = log₂ n` and use that `2^m` grows exponentially.
    suffices h_log : Filter.atTop.Tendsto (fun m : ℕ ↦ m ^ C / (m * Real.log 2).exp) (𝓝 0) by
      simpa [Real.exp_nat_mul, Real.exp_log] using h_log
    suffices h_log2 : Filter.atTop.Tendsto (fun y : ℝ ↦ y ^ C / Real.exp y) (𝓝 0) by
      have h := h_log2.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two))
      convert h.div_const (Real.log 2 ^ C) using 2 <;> ring_nf
      norm_num [Real.exp_ne_zero]
      exact eq_div_of_mul_eq (by positivity) (by ring_nf)
    simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C
  replace h_log := h_log.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [h_log, Filter.eventually_gt_atTop 0] with n hn hn'
  rw [div_lt_one (by positivity)] at hn
  exact_mod_cast hn.le


theorem quasipoly_ssubset_two_pow : quasipoly ⊂ two_pow := by
  use quasipoly_subset_two_pow
  simp only [quasipoly, bigO, two_pow, Nat.cast_pow, Nat.cast_ofNat, Set.setOf_subset_setOf,
    not_forall, exists_prop]
  use (2 ^ ·), mod_cast Asymptotics.isBigO_refl ..
  -- Assume for contradiction that there exists a constant `C` such that `2^n = O(2^((log n)^C))`.
  by_contra h_contra
  have ⟨C, hC⟩ := h_contra
  have h_exp : Filter.atTop.Tendsto (fun n ↦ (2 : ℝ) ^ (Nat.log 2 n ^ C) / 2 ^ n) (𝓝 0) := by
    -- We rewrite `2^((log n)^C) / 2^n = 2^((log n)^C - n)`.
    suffices h_exp : Filter.atTop.Tendsto (fun n ↦ (2 : ℝ) ^ ((Nat.log 2 n) ^ C - n : ℝ)) (𝓝 0) by
      convert h_exp using 2
      norm_num [Real.rpow_sub]
      norm_cast
    have h_log : Filter.atTop.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ C - n) Filter.atBot := by
      have h_log : Filter.atTop.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ C / n) (𝓝 0) := by
        -- We substitute `m = log₂ n`.
        suffices h_log : Filter.atTop.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ C / (2 ^ m)) (𝓝 0) by
          have h_log : Filter.atTop.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / _) (𝓝 0) :=
            h_log.comp (Filter.tendsto_atTop_atTop.mpr <|
              (⟨2 ^ ·, fun n hn ↦ Nat.le_log_of_pow_le one_lt_two hn⟩))
          refine squeeze_zero_norm' ?_ h_log
          filter_upwards [Filter.eventually_gt_atTop 0] with n hn
          rw [Real.norm_of_nonneg (by positivity)]
          gcongr
          norm_cast
          exact Nat.pow_log_le_self 2 hn.ne'
        -- We substitute `m = log₂ n` and use that `2^m` grows much faster than `m^C`.
        have h_log : Filter.atTop.Tendsto (fun m : ℕ ↦ m ^ C / (m * Real.log 2).exp) (𝓝 0) := by
          suffices h_log : Filter.atTop.Tendsto (fun y : ℝ ↦ y ^ C / y.exp) (𝓝 0) by
            have hs : Filter.atTop.Tendsto (fun m : ℕ ↦ (m * Real.log 2 : ℝ) ^ C / _) (𝓝 0) :=
              h_log.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two))
            convert hs.div_const (Real.log 2 ^ C) using 2
            · ring_nf
              norm_num [mul_right_comm, mul_assoc, mul_left_comm, ne_of_gt, Real.log_pos]
            · simp
          simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C
        simpa [Real.exp_nat_mul, Real.exp_log] using h_log
      -- We can rewrite the limit expression using the properties of limits.
      have h_rw : Filter.atTop.Tendsto (fun n ↦ ((Nat.log 2 n : ℝ) ^ C / n - 1) * n) .atBot := by
        apply Filter.Tendsto.neg_mul_atTop (C := -1)
        · norm_num
        · simpa using h_log.sub_const 1
        · exact tendsto_natCast_atTop_atTop
      apply h_rw.congr'
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [sub_mul, div_mul_cancel₀ _ (by positivity)]
      ring
    norm_num [Real.rpow_def_of_pos]
    exact Filter.Tendsto.const_mul_atBot (by positivity) h_log
  rw [Asymptotics.isBigO_iff] at hC
  simp only [Nat.cast_pow, Nat.cast_ofNat, norm_pow, Filter.eventually_atTop] at hC
  obtain ⟨c, a, hc⟩ := hC
  have h_div : ∀ b ≥ a, 1 ≤ c * (2 : ℝ) ^ (Nat.log 2 b ^ C) / (2 : ℝ) ^ b := by
    intro b hb
    specialize hc b hb
    rw [le_div_iff₀ (by positivity)]
    norm_num [Norm.norm] at hc ⊢
    omega
  refine absurd ?_ (show ¬1 ≤ c * 0 by norm_num)
  refine le_of_tendsto_of_tendsto tendsto_const_nhds (h_exp.const_mul c) ?_
  rw [Filter.EventuallyLE, Filter.eventually_atTop]
  exact ⟨a, (by simpa [mul_div_assoc] using h_div · ·)⟩

theorem two_pow_subset_e_pow : two_pow ⊆ e_pow := by
  -- `2^n ≤ e^n` since `2 < e`.
  have h_exp_bound : ∀ n : ℕ, 2 ^ n ≤ Real.exp n := by
    intro n
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos] <;> norm_num
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (Real.log_two_lt_d9.le.trans (by norm_num))
  have h_two_pow_e_pow : (2 ^ · : ℕ → ℕ) ∈ bigO (fun n ↦ ⌈Real.exp n⌉₊ : ℕ → ℕ) := by
    apply Asymptotics.isBigO_iff.mpr
    use 1
    refine Filter.eventually_atTop.mpr ⟨0, fun n hn ↦ ?_⟩
    erw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast Nat.le_of_lt_succ <| by
      rw [← @Nat.cast_lt ℝ]
      push_cast
      linarith [Nat.le_ceil (Real.exp n), h_exp_bound n]
  convert h_two_pow_e_pow using 1
  constructor <;> intro h <;> unfold two_pow e_pow at *
  · aesop
  · exact fun f hf ↦ hf.trans h

theorem two_pow_ssubset_e_pow : two_pow ⊂ e_pow := by
  use two_pow_subset_e_pow
  simp only [e_pow, bigO, two_pow, Nat.cast_pow, Nat.cast_ofNat, Set.setOf_subset_setOf, not_forall,
    exists_prop]
  use (⌈Real.exp ·⌉₊), Asymptotics.isBigO_refl ..
  rw [Asymptotics.isBigO_iff']
  norm_num [Norm.norm]
  have h_exp : Filter.Tendsto (fun n : ℕ ↦ (Real.exp n : ℝ) / 2 ^ n) .atTop .atTop := by
    suffices h : Filter.Tendsto (fun n : ℕ ↦ (Real.exp 1 / 2 : ℝ) ^ n) .atTop .atTop by
      simpa [Real.exp_nat_mul, div_pow] using h
    exact tendsto_pow_atTop_atTop_of_one_lt <| by linarith [Real.exp_one_gt_two]
  intro x hx n
  replace h_exp := h_exp.eventually_gt_atTop (x + 1)
  replace h_exp := (Filter.eventually_ge_atTop n).and h_exp
  have ⟨m, hm⟩ := Filter.eventually_atTop.mp h_exp
  specialize hm m le_rfl
  refine ⟨m, hm.1, ?_⟩
  have hm₁ := hm.2
  rw [lt_div_iff₀ (by positivity)] at hm₁
  nlinarith [Nat.le_ceil (Real.exp m), show (2 : ℝ) ^ m > 0 by positivity]

theorem e_pow_subset_exp : e_pow ⊆ exp := by
  refine fun f h ↦ ⟨⌈Real.exp 1⌉₊, h.trans (Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩)⟩
  have h_exp_growth (x : ℕ) : Real.exp x ≤ ⌈Real.exp 1⌉₊ ^ x := by
    simpa using pow_le_pow_left₀ (by positivity) (Nat.le_ceil (Real.exp 1)) x
  simp only [Int.norm_natCast, Filter.eventually_atTop]
  use 1
  intros
  erw [Real.norm_of_nonneg (by positivity)]
  exact_mod_cast le_trans (Nat.ceil_mono <| h_exp_growth _) (by norm_num)

theorem e_pow_ssubset_exp : e_pow ⊂ exp := by
  use e_pow_subset_exp
  rw [Set.not_subset]
  use (3 ^ ·), ⟨3, by simpa using Asymptotics.isBigO_refl ..⟩
  simp only [e_pow, bigO, Set.mem_setOf_eq, Nat.cast_pow, Nat.cast_ofNat]
  intro h
  rw [Asymptotics.isBigO_iff'] at h
  contrapose h
  simp_rw [not_exists, not_and]
  intro c _
  have h_exp : Filter.Tendsto (fun x : ℕ ↦ (3 ^ x : ℝ) / ⌈(Real.exp x)⌉₊) .atTop .atTop := by
    have h_exp_approx : ∀ n : ℕ, (3 ^ n : ℝ) / ⌈(Real.exp n)⌉₊ ≥ (3 / Real.exp 1) ^ n / 2 := by
      intro n
      rw [div_pow, Real.exp_one_pow, div_div, ge_iff_le,
        div_le_div_iff₀ (by positivity) (by positivity)]
      grw [Nat.ceil_lt_add_one (by positivity),
        ← show Real.exp ↑n + 1 ≤ Real.exp ↑n * 2 by linarith [Real.add_one_le_exp n]]
    refine Filter.tendsto_atTop_mono h_exp_approx ?_
    refine Filter.Tendsto.atTop_div_const (by positivity) (tendsto_pow_atTop_atTop_of_one_lt ?_)
    rw [one_lt_div (by positivity)]
    exact Real.exp_one_lt_d9.trans_le <| by norm_num
  replace h_exp := h_exp.eventually_gt_atTop c
  simp only [Filter.eventually_atTop, Int.norm_natCast, not_exists, not_forall,
    not_le, exists_prop] at h_exp ⊢
  intro x
  rcases h_exp with ⟨w, h⟩
  refine ⟨_, Nat.le_add_left x w, ?_⟩
  erw [Real.norm_of_nonneg (by positivity)]
  specialize h (w + x) (by linarith)
  rw [lt_div_iff₀ (by positivity)] at h
  exact_mod_cast h

theorem exp_subset_primitiveRecursive : exp ⊆ primitiveRecursive := by
  rintro f ⟨k, hk⟩
  norm_cast at hk
  refine ⟨_, ?_, hk⟩
  simpa using Nat.Primrec.pow.comp (.pair (.const k) .id)

/-- The factorial function is not in `exp`. -/
theorem factorial_not_mem_exp : Nat.factorial ∉ exp := by
  rintro ⟨c, hc⟩
  rw [Asymptotics.isBigO_iff] at hc
  contrapose hc
  simp_rw [not_exists]
  simp only [Filter.eventually_atTop, not_exists, not_forall]
  intro y z
  -- We'll use the exponential property: the factorial grows faster than any exponential function.
  have hf_growth : Filter.Tendsto (fun n ↦ (y * (c ^ n) : ℝ) / n.factorial) .atTop (𝓝 0) := by
    have h := FloorSemiring.tendsto_pow_div_factorial_atTop (c : ℝ)
    simpa [mul_div_assoc] using h.const_mul y
  have ⟨w, h⟩ := Filter.eventually_atTop.mp <| hf_growth.eventually (gt_mem_nhds zero_lt_one)
  refine ⟨_, le_max_left z w, ?_⟩
  specialize h _ (le_max_right z w)
  rw [div_lt_one (by positivity)] at h
  simpa using h

--PR'ed in https://github.com/leanprover-community/mathlib4/pull/33864
/-- The factorial function is primitve recursive. -/
theorem _root_.Primrec.factorial : Primrec Nat.factorial := by
  convert Primrec.list_foldl (σ := ℕ) (h := fun n ⟨p, k⟩ ↦ p * (k + 1))
    Primrec.list_range (Primrec.const 1) ?_
  · rw [← Finset.prod_range_add_one_eq_factorial, ← List.foldl_map, ← List.prod_eq_foldl]
    rw [← List.prod_toFinset _ List.nodup_range, ← List.toFinset_range]
  · refine Primrec.comp₂ ?_ .right
    exact Primrec.nat_mul.comp₂ .left (Primrec.succ.comp₂ .right)

theorem exp_ssubset_primitiveRecursive : exp ⊂ primitiveRecursive := by
  use exp_subset_primitiveRecursive
  rw [Set.not_subset]
  use Nat.factorial
  constructor
  · use Nat.factorial
    rw [← Primrec.nat_iff]
    exact ⟨Primrec.factorial, Asymptotics.isBigO_refl ..⟩
  · exact factorial_not_mem_exp

theorem primitiveRecursive_subset_computable : primitiveRecursive ⊆ computable := by
  rintro f ⟨g, hg⟩
  rw [← Primrec.nat_iff] at hg
  exact ⟨g, hg.left.to_comp, hg.right⟩

theorem primitiveRecursive_ssubset_computable : primitiveRecursive ⊂ computable := by
  use primitiveRecursive_subset_computable
  rw [Set.not_subset]
  use (fun x ↦ ack x x)
  simp only [primitiveRecursive, bigO, Set.mem_setOf_eq, not_exists, not_and]
  constructor
  · use fun x ↦ ack x x
    constructor
    · exact Computable.comp computable₂_ack (Computable.id.pair Computable.id)
    · exact Asymptotics.isBigO_refl ..
  · intro x hx
    rw [Asymptotics.isBigO_iff']
    -- Since ack n n grows faster than any primrec, for any constant c,
    -- there exists an n such that ack n n > c * x n.
    have h_ineq : ∀ c > 0, ∃ N, ∀ n ≥ N, ack n n > c * x n := by
      intro c hc_pos
      -- There exists an m such that ack(m, n) > c * x(n) for all n.
      obtain ⟨m, hm⟩ : ∃ m, ∀ n, ack m n > c * x n := by
        apply exists_lt_ack_of_nat_primrec
        suffices h_poly : Nat.Primrec (fun n ↦ c * n) by
          exact h_poly.comp hx
        convert Nat.Primrec.mul.comp ((Nat.Primrec.const c).pair Nat.Primrec.id) using 2
        norm_num [Nat.unpaired]
      exact ⟨m, fun n hn ↦ by simpa using (hm n).trans_le (ack_le_ack hn le_rfl)⟩
    simp only [norm_natCast, Filter.eventually_atTop, not_exists, not_and, not_forall, not_le]
    intro c hc n
    obtain ⟨N, hN⟩ := h_ineq (⌈c⌉₊) (Nat.ceil_pos.mpr hc)
    use n + N, by omega
    grw [Nat.le_ceil c]
    exact_mod_cast hN _ (by omega)

end ordering

section closure_comp

variable {f g : ℕ → ℕ}

/--
If a function `g` is polynomially bounded, then `log(g(n))` is `O(log n)`.
-/
private lemma isBigO_log_comp_poly_real {C : ℝ} (hg : (g · : ℕ → ℝ) =O[.atTop] (· ^ C : ℕ → ℝ)) :
    (Real.log <| g ·) =O[.atTop] (Real.log ·) := by
  rw [Asymptotics.isBigO_iff'] at hg ⊢
  obtain ⟨c, hc₀, hc⟩ := hg
  use |C| + 1, by positivity
  filter_upwards [hc, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ⌈c⌉₊] with x h₁ h₂ h₃
  by_cases hx₄ : g x = 0
  · simp_all only [RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop,
      CharP.cast_eq_zero, norm_zero, mul_nonneg_iff_of_pos_left, abs_nonneg, Real.log_zero]
    positivity
  · simp_all only [RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop]
    rw [
      abs_of_nonneg (Real.log_nonneg <| mod_cast Nat.one_le_iff_ne_zero.mpr hx₄),
      abs_of_nonneg (Real.log_nonneg <| mod_cast h₂.le)]
    have h := Real.log_le_log (by positivity) h₁
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_abs, Real.log_rpow (by positivity)] at h
    have _ := @Real.log_nonneg x (mod_cast h₂.le)
    cases abs_cases C
    · nlinarith [@Real.log_le_log c x hc₀ ((Nat.le_ceil c).trans (mod_cast h₃.le))]
    · nlinarith [@Real.log_le_log c x hc₀ ((Nat.le_ceil c).trans (mod_cast h₃.le))]

theorem log_comp_poly (hf : f ∈ log) (hg : g ∈ poly) : f ∘ g ∈ log := by
  -- Apply `poly_iff_rpow` on `hg` to get a constant `C` such that `g n =O n^C`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, (fun n ↦ (g n : ℝ)) =O[.atTop] (fun n ↦ (n : ℝ) ^ C) :=
    poly_iff_rpow.mp hg
  -- Apply `isBigO_log_comp_poly_real` to `hC` to deduce that `Real.log (g n) =O Real.log n`.
  have h_log_g : (fun n ↦ Real.log (g n)) =O[.atTop] (Real.log ·) :=
    isBigO_log_comp_poly_real hC
  -- Since `f` is bounded by `A + B * log x`, `f (g n) ≤ A + B * log (g n)` for large `g n`.
  have h_f_g : ∃ A B : ℝ, ∀ n, f (g n) ≤ A + B * Real.log (g n) := by
    obtain ⟨A, B, hAB⟩ : ∃ A B : ℝ, ∀ x : ℕ, x ≥ 1 → f x ≤ A + B * Real.log x := by
      have h_f_g : (fun x : ℕ ↦ (f x : ℝ)) =O[.atTop] (Real.log ·) := by
        exact log_iff_rlog.mp hf
      rw [Asymptotics.isBigO_iff] at h_f_g
      norm_num +zetaDelta at *
      obtain ⟨c, a, hc⟩ := h_f_g
      use (∑ x ∈ .range (a + 1), f x) + |c|, |c|
      intro x hx; by_cases hx' : x ≤ a
      · simp_all only [Nat.cast_sum]
        refine le_add_of_le_of_nonneg ?_ (by positivity)
        refine le_add_of_le_of_nonneg ?_ (by positivity)
        exact Finset.single_le_sum (fun x _ ↦ (f x).cast_nonneg) (Finset.mem_range.mpr (by omega))
      · simp_all only [not_le, Nat.cast_sum]
        have _ := Real.log_nonneg (show (x : ℝ) ≥ 1 by norm_cast)
        specialize hc x hx'.le
        cases abs_cases c <;>
        cases abs_cases (Real.log x) <;>
        nlinarith [show 0 ≤ ∑ i ∈ .range (a + 1), (f i : ℝ) by positivity]
    refine ⟨A ⊔ (f 0), B ⊔ 0, fun n ↦ ?_⟩
    by_cases hn : 1 ≤ g n
    · exact hAB _ hn |> le_trans <| by gcongr <;> norm_num
    · simp at hn; simp [hn]
  -- Since `Real.log (g n) =O Real.log n`, by transitivity `f (g n) =O Real.log n`.
  obtain ⟨A, B, hAB⟩ := h_f_g
  have h_trans : (fun n ↦ (f (g n) : ℝ)) =O[.atTop] (Real.log ·) := by
    have h_const : (fun n ↦ A : ℕ → ℝ) =O[.atTop] (Real.log ·) := by
      norm_num [Asymptotics.isBigO_iff]
      refine ⟨|A|, 3, fun n hn ↦ ?_⟩
      rw [abs_of_nonneg (Real.log_nonneg <| by norm_cast; linarith)]
      exact le_mul_of_one_le_right (abs_nonneg _) <| by
        rw [Real.le_log_iff_exp_le <| by positivity]
        exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [show (n : ℝ) ≥ 3 by norm_cast]
    refine Asymptotics.IsBigO.trans ?_ (h_const.add (h_log_g.const_mul_left B))
    rw [Asymptotics.isBigO_iff]
    simp only [RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop]
    exact ⟨1, 0, fun n hn ↦ by rw [one_mul]; exact le_trans (hAB n) (le_abs_self _)⟩
  exact log_iff_rlog.mpr h_trans

private lemma log_le_const_mul_log_add_const {f : ℕ → ℕ} (hf : f ∈ log) :
    ∃ (C D : ℝ), ∀ n, (f n : ℝ) ≤ C * (Nat.log 2 n) + D := by
  unfold log bigO at hf
  obtain ⟨C, N, hN⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * Nat.log 2 n := by
    norm_num [Asymptotics.isBigO_iff] at hf
    rcases hf with ⟨c, N, hc⟩
    refine ⟨⌈c⌉₊, N, fun n hn ↦ ?_⟩
    exact_mod_cast (hc n hn).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil _) <| Nat.cast_nonneg _)
  -- Let `D = max_{n < N} f(n)`.
  obtain ⟨D, hD⟩ : ∃ D, ∀ n < N, f n ≤ D := by
    exact ⟨Finset.sup (Finset.range N) f, fun n hn ↦ Finset.le_sup (Finset.mem_range.mpr hn)⟩
  exact ⟨C, D, fun n ↦ if hn : n < N
    then by exact (Nat.cast_le.mpr (hD n hn)).trans (by norm_cast; nlinarith)
    else by exact (Nat.cast_le.mpr (hN n (le_of_not_gt hn))).trans (by norm_cast; nlinarith)⟩

private lemma log_of_quasipoly_mem_polylog (hg : g ∈ quasipoly) : (Nat.log 2 <| g ·) ∈ polylog := by
  -- Since `g ∈ quasipoly`, we know that `g(n) = O(2^{(log n)^C})` for some `C`.
  obtain ⟨C, hC⟩ : ∃ C : ℕ, (fun n ↦ (g n : ℝ)) =O[.atTop]
      (fun n ↦ (2 : ℝ) ^ (Nat.log 2 n ^ C) : ℕ → ℝ) := by
    obtain ⟨C, hC⟩ := hg
    use C
    norm_num [Asymptotics.isBigO_iff, Asymptotics.IsBigOWith] at *
    rcases hC with ⟨c, a, hc⟩
    exact ⟨c, a, fun n hn ↦ le_trans (hc n hn) (by norm_num [Norm.norm])⟩
  -- Taking the logarithm, we get `log(g(n)) ≤ log(K * 2^{(log n)^C}) ≈ log K + (log n)^C`.
  obtain ⟨C', D, h_log⟩ : ∃ C' D : ℝ, ∀ n, (Nat.log 2 (g n) : ℝ) ≤ C' * (Nat.log 2 n) ^ C + D := by
    -- Since `g(n) = O(2^{(log n)^C})`, we have `g(n) ≤ K * 2^{(log n)^C}` for some constant `K`.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ n, g n ≤ K * 2 ^ (Nat.log 2 n ^ C) := by
      obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ n, g n ≤ K * 2 ^ (Nat.log 2 n ^ C) := by
        rw [Asymptotics.isBigO_iff'] at hC
        norm_num +zetaDelta at *
        obtain ⟨c, hc₀, a, ha⟩ := hC
        -- Let `K = max_{0 ≤ n < a} g(n) / 2^((log n)^C)`.
        obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ n < a, (g n : ℝ) ≤ K * 2 ^ (Nat.log 2 n ^ C) := by
          use ∑ n ∈ .range a, (g n : ℝ) / 2 ^ (Nat.log 2 n ^ C)
          intro n hn; rw [Finset.sum_mul _ _ _]
          rw [← Finset.mem_range] at hn
          refine le_trans ?_ (Finset.single_le_sum (by intros; positivity) hn)
          rw [div_mul_cancel₀ _ (by positivity)]
        use K ⊔ c
        intro n
        rcases lt_or_ge n a with hn | hn
        · exact le_trans (hK n hn) (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        · exact le_trans (ha n hn) (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      use ⌈K⌉₊
      intro n
      exact_mod_cast le_trans (hK n) (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
    -- Taking the logarithm, we get `log(g(n)) ≤ log(K * 2^{(log n)^C}) = log K + (log n)^C`.
    have h_log_bound : ∀ n, Nat.log 2 (g n) ≤ Real.log K / Real.log 2 + (Nat.log 2 n) ^ C := by
      intro n
      have h_log_bound : Nat.log 2 (g n) ≤ Real.log (K * 2 ^ (Nat.log 2 n ^ C)) / Real.log 2 := by
        rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
        by_cases hn : g n = 0
        · norm_num [hn]
          rcases K with (_ | K)
          · norm_num
          simp only [Nat.cast_add, Nat.cast_one]
          exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by simp) (one_le_pow₀ one_le_two))
        · exact Real.log_le_log (by positivity) (mod_cast (Nat.pow_log_le_self 2 hn).trans (hK n))
      by_cases hK : K = 0
      · simp_all
      · simp only [ne_eq, Nat.cast_eq_zero, not_false_eq_true, pow_eq_zero_iff',
          OfNat.ofNat_ne_zero, Nat.log_eq_zero_iff, Order.lt_two_iff,
          Nat.not_ofNat_le_one, or_false, not_and, Decidable.not_not, false_and, Real.log_mul,
          Real.log_pow, Nat.cast_pow, hK] at h_log_bound
        exact h_log_bound.trans_eq (by rw [add_div, mul_div_cancel_right₀ _ (by positivity)])
    exact ⟨1, Real.log K / Real.log 2, fun n ↦ by linarith [h_log_bound n]⟩
  have h_poly : (fun n ↦ (Nat.log 2 (g n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n ^ C : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound (|C'| + |D|)
    norm_num +zetaDelta at *
    refine ⟨2, fun n hn ↦ ?_⟩
    apply le_trans (h_log n)
    have _ : (Nat.log 2 n : ℝ) ^ C ≥ 1 :=
      one_le_pow₀ (mod_cast Nat.le_log_of_pow_le (by norm_num) (by linarith))
    cases abs_cases C' <;>
    cases abs_cases D <;>
    nlinarith
  use C
  rw [Asymptotics.isBigO_iff] at *
  aesop

theorem log_comp_quasipoly (hf : f ∈ log) (hg : g ∈ quasipoly) : f ∘ g ∈ polylog := by
  obtain ⟨K, hK⟩ := log_of_quasipoly_mem_polylog hg
  -- Since `f ∈ log`, by `log_le_const_mul_log_add_const`, `f(x) ≤ A * log x + B`.
  obtain ⟨A, B, hA⟩ : ∃ A B : ℝ, ∀ n, (f n : ℝ) ≤ A * (Nat.log 2 n) + B :=
    log_le_const_mul_log_add_const hf
  -- Since `h(n) = O((log n)^K)`, `A h(n) + B` is also `O((log n)^K)` (as `polylog` is
  -- closed under scalar multiplication and addition).
  have hp : (fun n ↦ A * Nat.log 2 (g n) + B) =O[.atTop] (fun n ↦ (Nat.log 2 n ^ K : ℝ)) := by
    -- Since `h(n) = O((log n)^K)`, multiplying by a constant `A` preserves the big-O.
    have h : (fun n ↦ A * Nat.log 2 (g n)) =O[.atTop] (fun n ↦ (Nat.log 2 n ^ K : ℝ)) := by
      have h : (fun n ↦ (Nat.log 2 (g n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n ^ K : ℝ)) := by
        convert hK using 1
        norm_num [Asymptotics.isBigO_iff, bigO]
      exact h.const_mul_left A
    refine h.add ?_ |> fun h ↦ h.trans ?_
    · rw [Asymptotics.isBigO_iff]
      use ‖B‖
      filter_upwards [Filter.eventually_gt_atTop 1] with n hn
      simp only [Real.norm_eq_abs, norm_pow, RCLike.norm_natCast]
      refine le_mul_of_one_le_right (abs_nonneg _) ?_
      exact one_le_pow₀ (mod_cast Nat.le_log_of_pow_le (by norm_num) (by linarith))
    · apply Asymptotics.isBigO_refl
  use K
  rw [Asymptotics.isBigO_iff] at *
  norm_num at *
  choose C D hC using hp
  exact ⟨C, D, fun n hn ↦ (hA _).trans <| (le_abs_self _).trans (hC n hn)⟩

lemma Nat.log2_pow_le (b n : ℕ) : Nat.log 2 (b ^ n) ≤ n * (Nat.log 2 b + 1) := by
  suffices Nat.log 2 (b ^ n) ≤ n * Nat.log 2 b + n by
    linarith
  suffices h : b ^ n ≤ 2 ^ (n * Nat.log 2 b + n) from
    (Nat.log_mono_right h).trans (by simp)
  rw [pow_add, pow_mul', ← mul_pow, ← pow_succ]
  exact Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self one_lt_two b).le n

private lemma exists_le_log_add_const {f : ℕ → ℕ} (hf : f ∈ log) :
    ∃ C D, ∀ n, f n ≤ C * Nat.log 2 n + D := by
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * Nat.log 2 n := by
    have h_bound : ∃ C, ∀ᶠ n in .atTop, f n ≤ C * Nat.log 2 n := by
      have := hf
      unfold log at this
      unfold bigO at this
      norm_num [Asymptotics.isBigO_iff] at this
      obtain ⟨C, a, hC⟩ := this
      refine ⟨⌈C⌉₊, Filter.eventually_atTop.mpr ⟨a, fun n hn ↦ ?_⟩⟩
      rw [← @Nat.cast_le ℝ]
      push_cast
      nlinarith [Nat.le_ceil C, hC n hn, show (Nat.log 2 n : ℝ) ≥ 0 by positivity]
    aesop
  -- Let `D` be the maximum of `f(n)` for `n < N`.
  obtain ⟨D, hD⟩ : ∃ D, ∀ n < N, f n ≤ D := by
    exact ⟨(Finset.range N).sup f, fun n hn ↦ Finset.le_sup (Finset.mem_range.mpr hn)⟩
  exact ⟨C, D, fun n ↦ if hn : n < N
    then (hD n hn).trans (Nat.le_add_left _ _)
    else (hC n (le_of_not_gt hn)).trans (Nat.le_add_right _ _)⟩

theorem log_comp_exp (hf : f ∈ log) (hg : g ∈ exp) : f ∘ g ∈ linear := by
  obtain ⟨B, K, hB⟩ : ∃ B K, ∀ᶠ n in .atTop, g n ≤ K * B ^ n := by
    unfold exp at hg
    norm_num [Asymptotics.isBigO_iff] at hg
    obtain ⟨C, c, a, hc⟩ := hg
    use C, ⌈c⌉₊
    filter_upwards [Filter.eventually_ge_atTop a] with n hn
    exact_mod_cast (hc n hn).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil _) <| by positivity)
  -- Using `Nat.log_mul_le`, `log(K * B^n) ≤ log K + log(B^n) + 1`.
  -- Using `Nat.log2_pow_le`, `log(B^n) ≤ n * (log B + 1)`.
  have h_log_bound : ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ Nat.log 2 K + n * (Nat.log 2 B + 1) + 1 := by
    filter_upwards [hB, Filter.eventually_gt_atTop 0] with n hn hn'
    rcases eq_or_ne K 0 with rfl | hK'
    · simp at hn
      simp [hn]
    rcases eq_or_ne B 0 with rfl | hB'
    · simp [hn'] at hn
      simp [hn]
    apply Nat.le_trans (Nat.log_mono_right hn)
    refine Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by positivity) ?_)
    have h_simp : K * B ^ n < 2 ^ (Nat.log 2 K + 1) * 2 ^ (n * (Nat.log 2 B + 1)) := by
      refine mul_lt_mul'' (Nat.lt_pow_succ_log_self one_lt_two _) ?_ (by positivity) (by positivity)
      rw [pow_mul']
      exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by decide) _) (by positivity)
    exact h_simp.trans_le (by rw [← pow_add]; exact pow_le_pow_right₀ (by decide) (by linarith))
  -- Using `exists_le_log_add_const`, there are `C_f, D_f` such that `f(x) ≤ C_f * log x + D_f`.
  obtain ⟨C_f, D_f, hC_f⟩ := exists_le_log_add_const hf
  have h_com : ∀ᶠ n in .atTop, f (g n) ≤ C_f * (Nat.log 2 K + n * (Nat.log 2 B + 1) + 1) + D_f := by
    filter_upwards [h_log_bound] with n hn using (hC_f _).trans (by gcongr)
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ n in .atTop, f (g n) ≤ C * n := by
    use C_f * (Nat.log 2 B + 1) + C_f * Nat.log 2 K + C_f + D_f + 1
    filter_upwards [h_com, Filter.eventually_gt_atTop 0] with n hn hn'
    nlinarith [show 0 ≤ C_f * Nat.log 2 K by positivity, show 0 ≤ C_f * Nat.log 2 B by positivity]
  apply Asymptotics.IsBigO.of_bound (C + 1)
  filter_upwards [hC, Filter.eventually_gt_atTop 0] with n hn hn'
  norm_num
  exact_mod_cast hn.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))

theorem sublinear_comp_linear (hf : f ∈ sublinear) (hg : g ∈ linear) : f ∘ g ∈ sublinear := by
  obtain ⟨c, hc⟩ : ∃ c > 0, ∀ᶠ x in .atTop, |(f x : ℝ)| ≤ c * x := by
    have h_sublinear : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(f n : ℝ)| ≤ ε * n := by
      intro ε hε_pos
      have := hf.def (show 0 < ε by positivity)
      simp_all
    refine ⟨1, zero_lt_one, ?_⟩
    obtain ⟨N, hN⟩ := h_sublinear 1 zero_lt_one
    filter_upwards [Filter.Ici_mem_atTop N] with n hn using hN n hn
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ x in .atTop, |(g x : ℝ)| ≤ C * x := by
    simp only [bigO, linear, id_eq, Asymptotics.isBigO_iff, norm_natCast,
      Filter.eventually_atTop, Set.mem_setOf_eq] at hg
    simp only [Filter.eventually_atTop, Nat.abs_cast]
    exact hg
  have h_sub : ∀ ε > 0, ∃ N_f, ∀ x ≥ N_f, (f x : ℝ) ≤ ε * x := by
    intro ε hε
    have := (hf.congr' (by aesop) (by aesop)).def hε
    aesop
  -- Since `g ∈ linear`, there exists `C > 0` such that for all `x ≥ N_g`, `g(x) ≤ C * x`.
  obtain ⟨C, hC⟩ : ∃ C > 0, ∀ᶠ x in .atTop, |(g x : ℝ)| ≤ C * x := by
    use C ⊔ 1, by positivity
    refine hC.mono fun x hx ↦ ?_
    grw [← le_max_left, hx]
  have h_eps : ∀ ε > 0, ∃ N, ∀ x ≥ N, (f (g x) : ℝ) ≤ ε * x := by
    intro ε hε_pos
    obtain ⟨N_f, hN_f⟩ : ∃ N_f, ∀ x ≥ N_f, (f x : ℝ) ≤ (ε / (C + 1)) * x :=
      h_sub (ε / (C + 1)) (div_pos hε_pos (add_pos hC.1 zero_lt_one))
    obtain ⟨N_g, hN_g⟩ := Filter.eventually_atTop.mp hC.2
    obtain ⟨M, hM⟩ : ∃ M, ∀ x < N_f, (f x : ℝ) ≤ M :=
      ⟨∑ x ∈ .range N_f, (f x : ℝ), fun x hx ↦
        Finset.single_le_sum (fun x _ ↦ Nat.cast_nonneg (f x)) (Finset.mem_range.mpr hx)⟩
    use N_g ⊔ (⌈M / ε⌉₊ + 1)
    intro x hx
    by_cases h_case : g x < N_f
    · apply (hM _ h_case).trans
      nlinarith [Nat.le_ceil (M / ε), mul_div_cancel₀ M hε_pos.ne',
        show (x : ℝ) ≥ ⌈M / ε⌉₊ + 1 by grw [hx, ← le_max_right]; norm_cast]
    · have := hN_f (g x) (by linarith)
      rw [div_mul_eq_mul_div, le_div_iff₀ (by cases hC; positivity)] at this
      specialize hN_g x (le_trans (le_max_left _ _) hx)
      nlinarith [abs_le.mp hN_g, Nat.le_ceil (M / ε), mul_div_cancel₀ M hε_pos.ne']
  refine Asymptotics.isLittleO_iff.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := h_eps ε hε
  filter_upwards [Filter.eventually_ge_atTop N] with x hx
  simpa [abs_of_nonneg, hε.le] using hN x hx

/--
If g is linear, then Nat.log(g(n)) is logarithmic.
-/
private lemma log_comp_linear {g : ℕ → ℕ} (hg : g ∈ linear) : (Nat.log 2 <| g ·) ∈ log := by
  have ⟨C, hC⟩ : ∃ C, ∀ᶠ n in .atTop, g n ≤ C * n := by
    have ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hg
    use ⌈C⌉₊
    filter_upwards [hC, Filter.eventually_gt_atTop 0] with x hx₁ hx₂
    have := (le_abs_self _).trans <| hx₁.trans <|
      mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
    simp only [Int.cast_natCast, id_eq, norm_natCast] at this
    exact_mod_cast this
  have ⟨D, hD⟩  : ∃ D, ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ Nat.log 2 C + Nat.log 2 n + D := by
    refine ⟨2, ?_⟩
    filter_upwards [hC] with n hn
    rcases eq_or_ne (g n) 0 with hn' | hn'
    · simp_all
    simp only [Filter.eventually_atTop] at hC
    refine Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow ?_ ?_)
    · aesop
    · have _ := Nat.lt_pow_succ_log_self one_lt_two C
      have _ := Nat.lt_pow_succ_log_self one_lt_two n
      simp only [ne_eq, Nat.succ_eq_add_one, Nat.pow_succ', Nat.pow_add] at *
      nlinarith
  apply Asymptotics.IsBigO.of_bound (Nat.log 2 C + D + 1)
  norm_num +zetaDelta at *
  obtain ⟨a, ha⟩ := hD
  refine ⟨a + 2, fun n hn ↦ ?_⟩
  norm_cast
  nlinarith [ha n (by linarith), Nat.log_pos one_lt_two (by linarith : 1 < n)]

/-- If g is linear, then g(n) * Nat.log(g(n)) is linearithmic. -/
private lemma linear_mul_log_comp_linear {g : ℕ → ℕ} (hg : g ∈ linear) :
    (fun n ↦ g n * Nat.log 2 (g n)) ∈ linearithmic := by
  exact linearithmic_of_linear_mul hg (log_comp_linear hg)

theorem linearithmic_comp (hf : f ∈ linearithmic) (hg : g ∈ linear) : f ∘ g ∈ linearithmic := by
  unfold linearithmic at *
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, g n ≤ C * n := by
    obtain ⟨C, N, hC⟩ := hg.exists_pos
    simp only [Asymptotics.IsBigOWith, norm_natCast, id_eq, Filter.eventually_atTop] at hC
    rcases hC with ⟨k, hK⟩
    use ⌈C⌉₊, k
    intro n hn
    exact_mod_cast (hK n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  obtain ⟨D, M, hD⟩ : ∃ D M, ∀ x ≥ M, f x ≤ D * x * Nat.log 2 x := by
    simp only [bigO, Nat.cast_mul, Asymptotics.isBigO_iff, norm_natCast, norm_mul,
      Filter.eventually_atTop, Set.mem_setOf_eq] at hf
    rcases hf with ⟨c, a, hc⟩
    refine ⟨⌈c⌉₊, a, fun x hx ↦ ?_⟩
    specialize hc x hx
    rw [← @Nat.cast_le ℝ]
    push_cast
    nlinarith [Nat.le_ceil c, show (x : ℝ) * Nat.log 2 x ≥ 0 by positivity]
  have hfg₀ : ∀ n ≥ N, f (g n) ≤ D * (C * n) * Nat.log 2 (C * n) + ∑ x ∈ .range M, f x := by
    intro n hn
    by_cases hmn : g n < M
    · apply le_add_of_nonneg_of_le (Nat.zero_le _)
      exact Finset.single_le_sum (fun x _ ↦ Nat.zero_le (f x)) (Finset.mem_range.mpr hmn)
    · refine le_add_of_le_of_nonneg ?_ (Nat.zero_le _)
      specialize hC n hn
      exact (hD _ (le_of_not_gt hmn)).trans (by gcongr)
  obtain ⟨K, hK⟩ : ∃ K, ∀ n ≥ N, f (g n) ≤ K * n * Nat.log 2 n + K := by
    use D * C * (Nat.log 2 C + 2) + ∑ x ∈ .range M, f x + 1
    intro n hn
    have hfg₁ : f (g n) ≤ D * C * n * (Nat.log 2 n + Nat.log 2 C + 1) + ∑ x ∈ .range M, f x := by
      specialize hfg₀ n hn
      have h_log_bound : Nat.log 2 (C * n) ≤ Nat.log 2 n + Nat.log 2 C + 1 := by
        by_cases hC : C = 0
        · simp [hC]
        by_cases hn : n = 0
        · simp [hn]
        refine Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow ?_ ?_)
        · positivity
        · have h₁ := Nat.lt_pow_succ_log_self one_lt_two n
          have h₂ := Nat.lt_pow_succ_log_self one_lt_two C
          simp [Nat.pow_succ', Nat.pow_add] at h₁ h₂ ⊢
          nlinarith [Nat.pos_of_ne_zero hC, Nat.pos_of_ne_zero hn]
      exact hfg₀.trans (by nlinarith [show 0 ≤ D * C * n by positivity])
    rcases k : Nat.log 2 n with (_ | k)
    · simp_all only [zero_add, Nat.log_eq_zero_iff, Order.lt_two_iff,
        Nat.not_ofNat_le_one, or_false, mul_zero]
      have _ : 0 ≤ D * C := by positivity
      interval_cases n <;> simp <;> nlinarith
    · simp_all only
      grind
  apply Asymptotics.IsBigO.of_bound (K + K)
  norm_num +zetaDelta at *
  refine ⟨N + 2, fun n hn ↦ ?_⟩
  norm_cast
  specialize hK n (by omega)
  have _ : n ≤ n * Nat.log 2 n := Nat.le_of_lt_succ <|
    by nlinarith [Nat.le_log_of_pow_le one_lt_two <| show 2 ^ 1 ≤ n by linarith]
  nlinarith

private lemma log_quasilinear_bound (D : ℕ) :
    (fun n ↦ (Nat.log 2 (n * (Nat.log 2 n)^D) : ℤ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℤ)) := by
  -- Using the lemma `Nat.log_mul_le_add`, we bound `log₂(n * log₂(n)^D)`.
  have h_log_mul_le_add : ∀ n ≥ 2, Nat.log 2 (n * Nat.log 2 n ^ D) ≤
      Nat.log 2 n + D * (Nat.log 2 (Nat.log 2 n) + 1) + 1 := by
    intro n hn
    have h_log_mul_le_add : Nat.log 2 (n * Nat.log 2 n ^ D) ≤
        Nat.log 2 n + Nat.log 2 (Nat.log 2 n ^ D) + 1 := by
      have h_log_mul_le_add : ∀ a b : ℕ, a ≥ 2 → b ≥ 2 →
          Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
        intro a b ha hb
        refine Nat.le_of_lt_succ <| Nat.log_lt_of_lt_pow ?_ ?_ <;> norm_num
        · aesop
        · have h_log_a : a < 2 ^ (Nat.log 2 a + 1) := by
            exact Nat.lt_pow_succ_log_self (by decide) _
          have h_log_b : b < 2 ^ (Nat.log 2 b + 1) := by
            exact Nat.lt_pow_succ_log_self (by decide) _
          convert mul_lt_mul'' h_log_a h_log_b (by positivity) (by positivity) using 1; ring
      by_cases h₂ : Nat.log 2 n ^ D ≥ 2
      · exact h_log_mul_le_add _ _ hn h₂
      · interval_cases _ : Nat.log 2 n ^ D <;> simp_all
    have h_log_pow_le : Nat.log 2 (Nat.log 2 n ^ D) ≤ D * (Nat.log 2 (Nat.log 2 n) + 1) := by
      have h_log_pow_le : ∀ a k : ℕ, a > 0 → Nat.log 2 (a ^ k) ≤ k * (Nat.log 2 a + 1) := by
        intros a k ha_pos
        have h_log_pow_le : a ^ k ≤ 2 ^ (k * (Nat.log 2 a + 1)) := by
          rw [pow_mul']; gcongr; exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)
        exact Nat.le_trans (Nat.log_mono_right h_log_pow_le) (by rw [Nat.log_pow (by decide)])
      exact h_log_pow_le _ _ (Nat.log_pos one_lt_two hn)
    linarith
  have h_log_mul_le_add' : ∀ n ≥ 2, Nat.log 2 (n * Nat.log 2 n ^ D) ≤
      Nat.log 2 n + D * (Nat.log 2 n + 1) + 1 :=
    fun n hn ↦ (h_log_mul_le_add n hn).trans (by gcongr; exact Nat.log_le_self _ _)
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨D + D + 2, 2, fun n hn ↦ ?_⟩
  norm_cast
  nlinarith [h_log_mul_le_add' n hn, Nat.le_log_of_pow_le one_lt_two (show 2 ^ 1 ≤ n by linarith)]

theorem quasilinear_comp (hf : f ∈ quasilinear) (hg : g ∈ quasilinear) : f ∘ g ∈ quasilinear := by
  obtain ⟨C₁, hC₁⟩ := hf
  obtain ⟨C₂, hC₂⟩ := hg
  obtain ⟨M, hM⟩ : ∃ M, ∀ᶠ n in .atTop, g n ≤ M * n * (Nat.log 2 n)^C₂ := by
    rw [Asymptotics.isBigO_iff'] at hC₂
    norm_num +zetaDelta at *
    obtain ⟨c, hc₀, a, ha⟩ := hC₂
    refine ⟨⌈c⌉₊, a, fun n hn ↦ ?_⟩
    rw [← @Nat.cast_le ℝ]; push_cast
    nlinarith [Nat.le_ceil c, ha n hn, show (0 : ℝ) ≤ n * Nat.log 2 n ^ C₂ by positivity]
  -- Using `log_quasilinear_bound`, `log(g(n)) = O(log n)`.
  have h_log₀ : (fun n ↦ (Nat.log 2 (g n) : ℤ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℤ)) := by
    have h_log₁ : ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ Nat.log 2 (M * n * (Nat.log 2 n)^C₂) := by
      filter_upwards [hM] with n hn using Nat.log_mono_right hn
    -- Using `log_quasilinear_bound`, `log(M * n * (log n)^D) = O(log n)`.
    have h_log₂ : (fun n ↦ (Nat.log 2 (M * n * Nat.log 2 n ^ C₂) : ℤ))
        =O[.atTop] (fun n ↦ (Nat.log 2 n : ℤ)) := by
      rcases M with (_ | M)
      · simpa using Asymptotics.isBigO_zero _ _
      simp only [Nat.cast_mul, Nat.cast_pow, mul_assoc, Filter.eventually_atTop] at *
      -- Bound `log((M + 1) * (n * (log n)^C₂))`.
      have h_log_bound : ∀ᶠ n in .atTop, Nat.log 2 ((M + 1) * (n * (Nat.log 2 n)^C₂)) ≤
          Nat.log 2 (n * Nat.log 2 n ^ C₂) + Nat.log 2 (M + 1) + 1 := by
        refine Filter.eventually_atTop.mpr ⟨2, fun n hn ↦ ?_⟩
        refine Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow ?_ ?_)
        · positivity [Nat.log_pos one_lt_two hn]
        · rw [Nat.pow_succ, pow_add, pow_add]
          have _ := Nat.lt_pow_succ_log_self one_lt_two (n * Nat.log 2 n ^ C₂)
          have _ := Nat.lt_pow_succ_log_self one_lt_two (M + 1)
          norm_num [Nat.pow_succ'] at *
          nlinarith [Nat.zero_le (n * Nat.log 2 n ^ C₂)]
      have hq := log_quasilinear_bound C₂
      rw [Asymptotics.isBigO_iff] at *
      obtain ⟨c, hc⟩ := hq
      use c + Nat.log 2 (M + 1) + 1
      filter_upwards [h_log_bound, hc, Filter.eventually_gt_atTop 1] with n hn₁ hn₂ hn₃
      norm_num at *
      have : (Nat.log 2 ((M + 1) * (n * Nat.log 2 n ^ C₂)) : ℝ) ≤
          Nat.log 2 (n * Nat.log 2 n ^ C₂) + Nat.log 2 (M + 1) + 1 := by exact_mod_cast hn₁
      have : (Nat.log 2 n : ℝ) ≥ 1 := by
        exact_mod_cast Nat.le_log_of_pow_le (by norm_num) (by linarith)
      nlinarith
    refine Asymptotics.IsBigO.trans ?_ h_log₂
    rw [Asymptotics.isBigO_iff]
    exact ⟨1, by filter_upwards [h_log₁] with n hn; simpa using mod_cast hn⟩
  have ⟨K, K', hK⟩ : ∃ K K', ∀ᶠ n in .atTop, f (g n) ≤ K * (g n * (Nat.log 2 (g n))^C₁) + K' := by
    rw [Asymptotics.isBigO_iff'] at *
    obtain ⟨K, hK₁, hK₂⟩ := hC₁
    norm_num +zetaDelta at *
    obtain ⟨a, ha⟩ := hK₂
    -- Let `K'` be such that `f(x) ≤ K * (x * (log x)^C) + K'` for all `x`.
    obtain ⟨K', hK'⟩ : ∃ K', ∀ x, f x ≤ K * (x * (Nat.log 2 x)^C₁) + K' := by
      refine ⟨∑ x ∈ .range a, (f x : ℝ), fun x ↦ ?_⟩
      by_cases hx : x < a
      · exact le_add_of_nonneg_of_le (by positivity)
          (Finset.single_le_sum (fun x _ ↦ Nat.cast_nonneg (f x)) (Finset.mem_range.mpr hx))
      · exact le_add_of_le_of_nonneg (ha x (le_of_not_gt hx)) (by positivity)
    refine ⟨⌈K⌉₊, ⌈K'⌉₊, a, fun n hn ↦ ?_⟩
    specialize hK' (g n)
    exact_mod_cast hK'.trans (add_le_add
      (mul_le_mul_of_nonneg_right (Nat.le_ceil _) <| by positivity) <| Nat.le_ceil _)
  have ⟨K'', hK''⟩ : ∃ K'', ∀ᶠ n in .atTop, f (g n) ≤ K'' * (n * (Nat.log 2 n)^(C₁ + C₂)) + K' := by
    -- Using `h_log₀`, we can bound `(Nat.log 2 (g n))^C₁` by `O((Nat.log 2 n)^C₁)`.
    obtain ⟨L, hL⟩ : ∃ L, ∀ᶠ n in .atTop, (Nat.log 2 (g n))^C₁ ≤ L * (Nat.log 2 n)^C₁ := by
      rw [Asymptotics.isBigO_iff'] at h_log₀
      norm_num +zetaDelta at *
      obtain ⟨c, hc₀, a, ha⟩ := h_log₀
      refine ⟨⌈c ^ C₁⌉₊, a, fun n hn ↦ ?_⟩
      rw [← @Nat.cast_le ℝ]
      push_cast
      apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (ha n hn) _).trans
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
    -- Substitute the bounds from `hM` and `hL` into the inequality from `hK`.
    have h_subst : ∀ᶠ n in .atTop, f (g n) ≤
        K * (M * n * Nat.log 2 n ^ C₂ * (L * Nat.log 2 n ^ C₁)) + K' := by
      filter_upwards [hK, hM, hL] with n hn hn' hn'' using le_trans hn <| by gcongr
    refine ⟨K * M * L, ?_⟩
    filter_upwards [h_subst] with n hn
    convert hn using 1
    ring
  use C₁ + C₂
  simp only [Function.comp_apply, norm_natCast, Asymptotics.isBigO_iff]
  simp only [Filter.eventually_atTop] at hK'' hM ⊢
  obtain ⟨a, ha⟩ := hK''
  use K'' + K' + 1
  refine ⟨a + 2, fun n hn ↦ ?_⟩
  specialize ha n (by linarith)
  norm_cast
  nlinarith [show 0 < n * Nat.log 2 n ^ (C₁ + C₂) from
      mul_pos (by omega) (pow_pos (Nat.log_pos one_lt_two (by omega)) _)]

private lemma exists_bound_of_isBigO {f h : ℕ → ℕ} (hf : (f · : ℕ → ℤ) =O[.atTop] (h · : ℕ → ℤ)) :
    ∃ C : ℕ, ∀ n, f n ≤ C * h n + C := by
  obtain ⟨c, N, hc⟩ : ∃ c N, ∀ n ≥ N, f n ≤ c * h n := by
    rw [Asymptotics.isBigO_iff'] at hf
    simp only [norm_natCast, Filter.eventually_atTop] at hf
    obtain ⟨c, hc, N, hN⟩ := hf
    refine ⟨⌈c⌉₊, N, fun n hn ↦ ?_⟩
    exact_mod_cast (hN n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  have ⟨M, hM⟩ : ∃ M, ∀ n < N, f n ≤ M :=
    ⟨(Finset.range N).sup f, fun n ↦ Finset.le_sup ∘ Finset.mem_range.mpr⟩
  refine ⟨c ⊔ M, fun n ↦ ?_⟩
  nth_grw 1 [← le_max_left c M, ← le_max_right c M]
  rcases lt_or_ge n N with hn | hn
  · specialize hM n hn
    omega
  · specialize hc n hn
    omega

theorem poly_comp_log (hf : f ∈ poly) (hg : g ∈ log) : f ∘ g ∈ polylog := by
  rcases hf with ⟨C, hc⟩
  have ⟨A, hA⟩ : ∃ A : ℕ, ∀ n, f n ≤ A * n ^ C + A := by
    rw [Asymptotics.isBigO_iff'] at hc
    norm_num +zetaDelta at *
    obtain ⟨c, hc₀, a, ha⟩ := hc
    -- Let `A` be a constant such that `f(n) ≤ A * n^C + A` for all `n ≥ a`.
    obtain ⟨A, hA⟩ : ∃ A : ℕ, ∀ n ≥ a, f n ≤ A * n ^ C + A := by
      refine ⟨⌈c⌉₊, fun n hn ↦ ?_⟩
      specialize ha n hn
      suffices (f n : ℝ) ≤ ⌈c⌉₊ * n ^ C + ⌈c⌉₊ from mod_cast this
      nlinarith [Nat.le_ceil c, show 0 ≤ (n : ℝ) ^ C by positivity]
    -- Let `A'` be a constant such that `f(n) ≤ A' * n^C + A'` for all `n < a`.
    obtain ⟨A', hA'⟩ : ∃ A' : ℕ, ∀ n < a, f n ≤ A' * n ^ C + A' := by
      refine ⟨∑ n ∈ .range a, f n + 1, fun n hn ↦ ?_⟩
      nlinarith [Finset.single_le_sum (fun n _ ↦ Nat.zero_le (f n)) (Finset.mem_range.mpr hn),
        pow_nonneg (Nat.zero_le n) C]
    refine ⟨A ⊔ A', fun n ↦ ?_⟩
    rcases lt_or_ge n a with hn | hn
    · specialize hA' n hn
      nth_grw 1 [← le_max_right A A']
      omega
    · specialize hA n hn
      nth_grw 1 [← le_max_left A A']
      omega
  obtain ⟨B, hB⟩ := exists_bound_of_isBigO hg
  have hfg (n) : f (g n) ≤ A * (B * Nat.log 2 n + B) ^ C + A :=
    (hA _).trans (by gcongr; exact hB n)
  -- The term `(B log n + B)^C` is a polynomial in `log n` of degree `C`, so it is `O((log n)^C)`.
  have h_polylog : ∃ D : ℕ, ∀ n, (B * Nat.log 2 n + B) ^ C ≤ D * (Nat.log 2 n) ^ C + D := by
    -- We can bound `(B * log n + B)^C` by `(2B * log n)^C` for large enough `n`.
    have h_bound : ∀ n, (B * Nat.log 2 n + B) ^ C ≤ (2 * B * Nat.log 2 n) ^ C + (2 * B) ^ C := by
      intro n
      rcases eq_or_ne B 0 with rfl | hB₀
      · simp_all
      simp only [two_mul]
      rcases k : Nat.log 2 n with (_ | k)
      · simp_all only [ne_eq, Nat.log_eq_zero_iff, Order.lt_two_iff, Nat.not_ofNat_le_one,
          or_false, mul_zero, zero_add]
        cases C
        · norm_num
        · norm_num
          gcongr
          omega
      · simp only [add_mul]
        apply le_add_of_le_of_nonneg ?_ (by positivity)
        exact Nat.pow_le_pow_left (by nlinarith) C
    use (2 * B) ^ C
    exact fun n ↦ le_trans (h_bound n) (by rw [mul_pow])
  obtain ⟨D, hD⟩ := h_polylog
  have ⟨E, hE⟩ : ∃ E : ℕ, ∀ n, f (g n) ≤ E * (Nat.log 2 n) ^ C + E :=
    ⟨A * D + A, fun n ↦ by nlinarith [hfg n, hD n, pow_nonneg (Nat.zero_le (Nat.log 2 n)) C]⟩
  use C
  apply Asymptotics.IsBigO.of_bound (E + E)
  simp only [Function.comp_apply, norm_natCast, Nat.cast_pow, norm_pow, Filter.eventually_atTop]
  use 2
  intro n hn
  norm_cast
  nlinarith [hE n, Nat.one_le_pow C _ (Nat.log_pos one_lt_two hn)]

private lemma exists_poly_bound_nat {f : ℕ → ℕ} (hf : f ∈ poly) :
    ∃ C K : ℕ, ∀ n, f n ≤ K * (n + 1) ^ C := by
  rcases hf with ⟨C, hC⟩
  rw [Asymptotics.isBigO_iff'] at hC
  simp only [norm_natCast, norm_pow, Filter.eventually_atTop] at hC
  rcases hC with ⟨c, hc_pos, N, hN⟩
  have ⟨K₁, hK₁⟩ : ∃ K : ℕ, ∀ n ≥ N, f n ≤ K * (n + 1) ^ C := by
    use Nat.ceil c + 1
    intro n hn
    specialize hN n hn
    suffices (f n : ℝ) ≤ (⌈c⌉₊ + 1) * (n + 1) ^ C by exact_mod_cast this
    have h : (n : ℝ) ^ C ≤ (n + 1) ^ C := by gcongr; linarith
    grw [hN, ← Nat.le_ceil c, h]
    nlinarith
  have ⟨K₂, hK₂⟩ : ∃ K : ℕ, ∀ n < N, f n ≤ K * (n + 1) ^ C := by
    refine ⟨(Finset.range N).sup f, fun n hn ↦ ?_⟩
    nlinarith [Finset.le_sup (f := f) (Finset.mem_range.mpr hn), pow_pos (Nat.succ_pos n) C]
  refine ⟨C, K₁ ⊔ K₂, fun n ↦ ?_⟩
  rcases lt_or_ge n N with hn | hn
  · specialize hK₂ n hn
    nth_grw 1 [← le_max_right K₁ K₂]
    omega
  · specialize hK₁ n hn
    nth_grw 1 [← le_max_left K₁ K₂]
    omega

theorem poly_comp (hf : f ∈ poly) (hg : g ∈ poly) : f ∘ g ∈ poly := by
  have ⟨C_f, K_f, hf⟩ := exists_poly_bound_nat hf
  have ⟨C_g, K_g, hg⟩ := exists_poly_bound_nat hg
  use C_f * C_g
  have hfg_bound (n) : f (g n) ≤ K_f * (K_g * (n + 1) ^ C_g + 1) ^ C_f :=
    (hf _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by linarith [hg n]) _))
  have ⟨C, K, hfg_poly⟩ : ∃ C K : ℕ, ∀ n, f (g n) ≤ K * (n + 1) ^ (C_f * C_g) := by
    have h (n) : (K_g * (n + 1) ^ C_g + 1) ^ C_f ≤ (K_g + 1) ^ C_f * (n + 1) ^ (C_f * C_g) := by
      rw [pow_mul', ← mul_pow]
      exact Nat.pow_le_pow_left (by nlinarith [pow_pos (Nat.succ_pos n) C_g]) _
    use C_f * C_g, K_f * (K_g + 1) ^ C_f
    exact fun n ↦ (hfg_bound n).trans (by nlinarith [h n])
  rw [Asymptotics.isBigO_iff]
  use K * 2 ^ (C_f * C_g)
  norm_num
  refine ⟨1, fun n hn ↦ le_trans (Nat.cast_le.mpr (hfg_poly n)) ?_⟩; norm_cast; ring_nf
  rw [mul_assoc, ← mul_pow]
  gcongr
  lia

private lemma isBigO_poly_comp_exp {k C : ℕ}
    (hf : (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(n ^ k) : ℕ → ℤ))
    (hg : (g · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(C ^ n) : ℕ → ℤ)) :
    ∃ K : ℕ, (fun n ↦ f (g n) : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(K ^ n) : ℕ → ℤ) := by
  have ⟨N_f, c_f, hM_f⟩ : ∃ N_f c_f, ∀ x, x ≥ N_f → f x ≤ c_f * x ^ k := by
    simp_all only [Nat.cast_pow, Asymptotics.isBigO_iff', norm_natCast, norm_pow,
      Filter.eventually_atTop]
    have ⟨c, hc, a, ha⟩ := hf
    refine ⟨a, ⌈c⌉₊, fun x hx ↦ ?_⟩
    exact_mod_cast (ha x hx).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  -- For all `x`, `f(x) ≤ M_f + c_f * x^k`.
  obtain ⟨M_f, hM_f⟩ : ∃ M_f, ∀ x, f x ≤ M_f + c_f * x ^ k := by
    use (Finset.range N_f).sup f
    intro x
    by_cases hx : x < N_f
    · exact le_add_of_le_of_nonneg (Finset.le_sup (Finset.mem_range.mpr hx)) (Nat.zero_le _)
    · exact le_add_of_nonneg_of_le (Nat.zero_le _) (hM_f x (le_of_not_gt hx))
  -- From `hg`, there exists `c_g > 0` and `N_g` such that for all `n ≥ N_g`, `g(n) ≤ c_g * C^n`.
  obtain ⟨c_g, N_g, hM_g⟩ : ∃ c_g N_g, ∀ n ≥ N_g, g n ≤ c_g * C ^ n := by
    rw [Asymptotics.isBigO_iff'] at hg
    norm_num at *
    have ⟨c, hc₀, N_g, hN_g⟩ := hg
    refine ⟨⌈c⌉₊, N_g, fun n hn ↦ ?_⟩
    exact_mod_cast (hN_g n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  -- So for `n ≥ N_g`, `(g(n))^k ≤ (c_g * C^n)^k = c_g^k * (C^k)^n`.
  have h_bound : ∀ n ≥ N_g, (g n) ^ k ≤ c_g ^ k * (C ^ k) ^ n := by
    intro n hn; convert Nat.pow_le_pow_left (hM_g n hn) k using 1; ring
  -- Let `K = max(2, C^k)`. We claim `f(g(n)) = O(K^n)`.
  use 2 ⊔ C ^ k
  -- Thus `f(g(n)) ≤ M_f + c_f * c_g^k * (C^k)^n`.
  have h_final_bound : ∀ n ≥ N_g, f (g n) ≤ M_f + c_f * c_g ^ k * (C ^ k) ^ n :=
    fun n hn ↦ (hM_f _).trans (by nlinarith [h_bound n hn])
  have h_K_bound : ∀ n ≥ N_g, (C ^ k) ^ n ≤ (max 2 (C ^ k)) ^ n ∧ 1 ≤ (max 2 (C ^ k)) ^ n :=
    fun n hn ↦ ⟨Nat.pow_le_pow_left (le_max_right _ _) _, Nat.one_le_pow _ _ (by positivity)⟩
  rw [Asymptotics.isBigO_iff]
  norm_num +zetaDelta at *
  refine ⟨M_f + c_f * c_g ^ k, N_g, fun n hn ↦ ?_⟩
  erw [Real.norm_of_nonneg (by positivity)]
  exact le_trans (Nat.cast_le.mpr (h_final_bound n hn))
    (by norm_cast; nlinarith [h_K_bound n hn, show 0 ≤ c_f * c_g ^ k by positivity])

theorem poly_comp_exp (hf : f ∈ poly) (hg : g ∈ exp) : f ∘ g ∈ exp := by
  have ⟨k₁, hk₁⟩ := hf.imp fun _ ↦ mod_cast id
  have ⟨k₂, hk₂⟩ := hg.imp fun _ ↦ mod_cast id
  simpa [exp] using isBigO_poly_comp_exp hk₁ hk₂

private lemma log_bound_of_quasipoly {g : ℕ → ℕ} (hg : g ∈ quasipoly) :
    ∃ D : ℕ, (fun n ↦ (Nat.log 2 (g n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℝ) ^ D) := by
  have h := @log_comp_quasipoly
  contrapose! h
  refine ⟨fun n ↦ Nat.log 2 n, g, ?_, hg, ?_⟩
  · apply Asymptotics.isBigO_iff.mpr
    exact ⟨1, Filter.Eventually.of_forall fun n ↦ by norm_num⟩
  · intro H
    obtain ⟨C, hC⟩ := H
    apply h C
    rw [Asymptotics.isBigO_iff'] at *
    aesop

private lemma quasipoly_of_log_bound {f : ℕ → ℕ} (D : ℕ)
    (hf : (fun n ↦ (Nat.log 2 (f n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℝ) ^ D)) :
    f ∈ quasipoly := by
  -- From `hf`, we have `Nat.log 2 (f n) ≤ C * (Nat.log 2 n)^D` for large `n`. Then
  -- `f n ≤ 2^(Nat.log 2 (f n) + 1) ≤ 2^(C * (Nat.log 2 n)^D + 1)`.
  have ⟨C, hC⟩ : ∃ C : ℕ, ∀ᶠ n in .atTop, Nat.log 2 (f n) ≤ C * (Nat.log 2 n) ^ D := by
    rw [Asymptotics.isBigO_iff'] at hf
    norm_num +zetaDelta at *
    have ⟨c, hc, a, ha⟩ := hf
    refine ⟨⌈c⌉₊, a, fun n hn ↦ ?_⟩
    exact_mod_cast Nat.le_of_lt_succ <| by
      rw [← @Nat.cast_lt ℝ]; push_cast
      nlinarith [Nat.le_ceil c, ha n hn,
        pow_nonneg (Nat.cast_nonneg (Nat.log 2 n) : (0 :ℝ) ≤ Nat.log 2 n) D]
  -- We want to show `f n = O(2^((Nat.log 2 n)^K))`. Choose `K > D`. Then `(Nat.log 2 n)^K`
  -- eventually dominates `C * (Nat.log 2 n)^D + 1`.
  have ⟨K, hK₁, hK₂⟩ : ∃ K, K > D ∧ ∀ᶠ n in .atTop, C * Nat.log 2 n ^ D + 1 ≤ Nat.log 2 n ^ K := by
    refine ⟨D + 1, ?_, ?_⟩
    · norm_num
    simp only [Order.add_one_le_iff, Filter.eventually_atTop, pow_succ']
    refine ⟨2 ^ (C + 1), fun n hn ↦ ?_⟩
    have h1 : C < Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
    have h2 : 0 < Nat.log 2 n ^ D := by
      apply pow_pos
      exact Nat.log_pos (by norm_num) (by
        linarith [Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num)
          (show C + 1 ≥ 1 from Nat.le_add_left _ _)])
    nlinarith
  refine ⟨K, ?_⟩
  rw [Asymptotics.isBigO_iff']
  -- Then `f n ≤ 2^(Nat.log 2 (f n) + 1) ≤ 2^(C * (Nat.log 2 n)^D + 1) ≤ 2^((Nat.log 2 n)^K)`.
  have h_bound : ∀ᶠ n in .atTop, f n ≤ 2 ^ ((Nat.log 2 n) ^ K) := by
    filter_upwards [hC, hK₂] with n hn hn'
    exact (Nat.lt_pow_of_log_lt one_lt_two <| by linarith).le
  simp only [Filter.eventually_atTop, norm_natCast, norm_pow] at h_bound ⊢
  rcases h_bound with ⟨M, hM⟩
  refine ⟨1, by norm_num, M, fun n hn ↦ ?_⟩
  simpa [Norm.norm] using mod_cast hM n hn

theorem quasipoly_comp (hf : f ∈ quasipoly) (hg : g ∈ quasipoly) : f ∘ g ∈ quasipoly := by
  have ⟨Df, hDf⟩ := log_bound_of_quasipoly hf
  have ⟨Dg, hDg⟩ := log_bound_of_quasipoly hg
  have ⟨M, C, hM⟩ : ∃ M C : ℕ, ∀ m ≥ M, (Nat.log 2 (f m) : ℝ) ≤ C * Nat.log 2 m ^ Df := by
    rw [Asymptotics.isBigO_iff'] at hDf
    rcases hDf with ⟨c, hc₀, hc⟩
    have ⟨M, hM⟩ := Filter.eventually_atTop.mp hc
    refine ⟨M, ⌈c⌉₊, fun m hm ↦ ?_⟩
    specialize hM m hm; norm_num at *
    exact hM.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  have ⟨K, hK⟩ : ∃ K : ℕ, ∀ n, (Nat.log 2 (f (g n)) : ℝ) ≤ K ∨
      Nat.log 2 (f (g n)) ≤ C * (Nat.log 2 (g n) : ℝ) ^ Df := by
    use Finset.sup (Finset.image (fun m ↦ Nat.log 2 (f m)) (Finset.range M)) id
    exact fun n ↦ if hn : g n < M then
      Or.inl <| mod_cast Finset.le_sup (f := id) <| Finset.mem_image_of_mem _ <|
        Finset.mem_range.mpr hn
      else Or.inr <| hM _ <| le_of_not_gt hn
  -- From (2), `Nat.log 2 (g n) ≤ C' * (Nat.log 2 n)^Dg` for large `n`.
  obtain ⟨C', hC'⟩ : ∃ C' : ℕ, ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ C' * (Nat.log 2 n : ℝ) ^ Dg := by
    rw [Asymptotics.isBigO_iff] at hDg
    simp only [RCLike.norm_natCast, norm_pow, Filter.eventually_atTop] at hDg ⊢
    rcases hDg with ⟨c, a, hc⟩
    refine ⟨⌈c⌉₊, a, fun n hn ↦ ?_⟩
    exact (hc n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  apply quasipoly_of_log_bound (Dg * Df)
  rw [Asymptotics.isBigO_iff]
  have ⟨C, hC⟩ : ∃ C, ∀ᶠ n in .atTop, Nat.log 2 (f (g n)) ≤ C * (Nat.log 2 n : ℝ) ^ (Dg * Df) := by
    use K + C * C' ^ Df
    filter_upwards [hC', Filter.eventually_gt_atTop 1] with n h hn'
    simp only [pow_mul]
    rcases hK n with hK₂ | hK₂ <;> apply hK₂.trans
    · exact (le_add_of_nonneg_right <| by positivity).trans
        (le_mul_of_one_le_right (by positivity) <| one_le_pow₀ <| one_le_pow₀ <|
          mod_cast Nat.le_log_of_pow_le (by norm_num) <| by linarith)
    · apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h _) (by positivity)).trans
      ring_nf
      exact le_add_of_nonneg_right (by positivity)
  use C
  filter_upwards [hC] with n hn
  simpa using hn

/-- If g is O(log n) and C > 1, then C^(g n) is polynomially bounded. -/
private lemma exists_pow_bound_of_exp_comp_log_real {g : ℕ → ℕ} {C : ℝ} (hC : 1 < C)
    (hg : (fun n ↦ (g n : ℝ)) =O[.atTop] (fun n ↦ Real.log (n : ℝ))) :
    ∃ K : ℝ, (fun n ↦ C ^ (g n : ℝ)) =O[.atTop] (fun n ↦ (n : ℝ) ^ K) := by
  have ⟨M, hM⟩ : ∃ M : ℝ, ∀ᶠ n in .atTop, (g n : ℝ) ≤ M * Real.log n := by
    rw [Asymptotics.isBigO_iff'] at hg
    rcases hg with ⟨M, hM₁, hM₂⟩
    refine ⟨M, ?_⟩
    filter_upwards [hM₂, Filter.eventually_gt_atTop 1] with n hn hn'
    rwa [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.log_nonneg <| Nat.one_le_cast.mpr <| pos_of_gt hn')] at hn
  have h_bound : ∀ᶠ n in .atTop, (C : ℝ) ^ (g n : ℝ) ≤ (n : ℝ) ^ (M * Real.log C) := by
    filter_upwards [hM, Filter.eventually_gt_atTop 1] with n hn hn'
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity)]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.log_pos hC])
  refine ⟨M * Real.log C, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [h_bound] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  simpa using hn

/-- If f(n) is O(C^n) with C >= 1, then f(g(n)) is O(C^(g(n))). -/
private lemma isBigO_comp_exp_of_isBigO_exp {f g : ℕ → ℕ} {C : ℝ} (hC : 1 ≤ C)
    (hf : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ C ^ (n : ℝ))) :
    (fun n ↦ (f (g n) : ℝ)) =O[.atTop] (fun n ↦ C ^ (g n : ℝ)) := by
  simp only [Real.rpow_natCast, Asymptotics.isBigO_iff, RCLike.norm_natCast, norm_pow,
    Real.norm_eq_abs, Filter.eventually_atTop] at hf ⊢
  rcases hf with ⟨c, a, hc⟩
  have ⟨M, hM⟩ : ∃ M, ∀ n < a, f n ≤ M :=
    ⟨(Finset.range a).sup f, fun n hn ↦ Finset.le_sup (Finset.mem_range.mpr hn)⟩
  refine ⟨c ⊔ M, a, fun n hn ↦ ?_⟩
  rcases lt_or_ge (g n) a with h | h
  · grw [← hM _ h, ← le_max_right, ← (show 1 ≤ |C| by rw [abs_of_nonneg] <;> linarith)]
    simp
  · grw [← le_max_left, hc _ h]

/-- If f(n) is O(C^n) with 0 <= C <= 1, then f is polynomially bounded.
TODO: Show this holds for any LawfulGrowthRate instead.
-/
private lemma exp_subset_poly_of_le_one {f : ℕ → ℕ} {C : ℝ} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1)
    (hf : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ C ^ (n : ℝ))) : f ∈ poly := by
  use 0
  have h : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ 1 : ℕ → ℝ) := by
    apply hf.trans
    norm_num [Asymptotics.isBigO_iff]
    exact ⟨1, 0, fun n hn ↦ by rw [abs_of_nonneg hC₀]; exact pow_le_one₀ hC₀ hC₁⟩
  simpa [Asymptotics.isBigO_iff] using h

theorem exp_comp_log (hf : f ∈ exp) (hg : g ∈ log) : f ∘ g ∈ poly := by
  by_cases hC : ∃ C : ℝ, 1 < C ∧ (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ C ^ (n : ℝ))
  · -- Apply `isBigO_comp_exp_of_isBigO_exp` to show `f(g(n)) = O(C^{g(n)})`.
    rcases hC with ⟨C, hC₁, hC₂⟩
    have h_f_g_poly : (fun n ↦ (f (g n) : ℝ)) =O[.atTop] (fun n ↦ C ^ (g n : ℝ)) := by
      apply isBigO_comp_exp_of_isBigO_exp hC₁.le hC₂
    -- Apply `exists_pow_bound_of_exp_comp_log_real` to show `C^{g(n)} = O(n^K)` for some `K`.
    have ⟨K, hK⟩ : ∃ K : ℝ, (fun n ↦ C ^ (g n : ℝ)) =O[.atTop] (fun n ↦ (n : ℝ) ^ K) := by
      rw [log_iff_rlog] at hg
      exact exists_pow_bound_of_exp_comp_log_real hC₁ hg
    have h := h_f_g_poly.trans hK
    convert poly_iff_rpow.mpr _
    exact ⟨K, h⟩
  · contrapose! hC
    rcases hf with ⟨(_ | _ | C), hC⟩
    · have h_f_zero : ∀ᶠ n in .atTop, f n = 0 := by
        rw [Asymptotics.isBigO_iff'] at hC
        norm_num +zetaDelta at *
        rcases hC with ⟨c, hc, a, ha⟩
        exact ⟨a + 1, fun n hn ↦ by simpa [show n ≠ 0 by linarith] using ha n (by linarith)⟩
      norm_num +zetaDelta at *
      simp_rw [Asymptotics.isBigO_iff]
      use 2, one_lt_two, 1
      filter_upwards [Filter.eventually_ge_atTop h_f_zero.choose] with n hn
      norm_num [h_f_zero.choose_spec n hn]
    · simp only [zero_add, Nat.cast_one, one_pow, Asymptotics.isBigO_one_iff,
        Filter.IsBoundedUnder, Filter.IsBounded, norm_natCast, Filter.eventually_map,
        Filter.eventually_atTop, ge_iff_le] at hC
      simp only [Real.rpow_natCast, Asymptotics.isBigO_iff, norm_natCast, norm_pow,
        Real.norm_eq_abs, Filter.eventually_atTop] at ⊢
      rcases hC with ⟨b, a, hb⟩
      refine ⟨2, one_lt_two, b, a, fun n hn ↦ ?_⟩
      grw [hb n hn, ← one_le_pow₀ (by simp), mul_one]
      grw [← hb a le_rfl, Nat.cast_nonneg']
    · refine ⟨C + 1 + 1, by linarith, ?_⟩
      norm_cast at *
      rwa [Asymptotics.isBigO_iff] at hC ⊢

lemma exp_bound_nat {f : ℕ → ℕ} (hf : f ∈ exp) :
    ∃ (C : ℕ) (M : ℕ), 1 < C ∧ ∀ n, f n ≤ M * C ^ n := by
  have ⟨C₀, hC₀, N, hN⟩ : ∃ C₀ M₀ N, ∀ n ≥ N, f n ≤ M₀ * C₀ ^ n := by
    rcases hf with ⟨C₀, hC₀⟩
    norm_num [Asymptotics.isBigO_iff] at hC₀
    rcases hC₀ with ⟨c, a, hca⟩
    refine ⟨C₀, ⌈c⌉₊, a, fun n hn ↦ ?_⟩
    specialize hca n hn
    exact_mod_cast (by nlinarith [Nat.le_ceil c, show (C₀ ^ n : ℝ) ≥ 0 by positivity] :
      (f n : ℝ) ≤ ⌈c⌉₊ * C₀ ^ n)
  -- Choose `C = max(C₀, 2)` to ensure `C > 1`.
  set C := C₀ ⊔ 2
  have hC : 1 < C := lt_max_of_lt_right one_lt_two
  refine ⟨C, hC₀ + ∑ n ∈ .range N, f n + 1, hC, fun n ↦ ?_⟩
  by_cases hn : n < N
  · nlinarith [Nat.zero_le (∑ n ∈ .range N, f n),
      Finset.single_le_sum (fun n _ ↦ Nat.zero_le (f n)) (Finset.mem_range.mpr hn),
      pow_pos (zero_lt_one.trans hC) n]
  · exact le_trans (hN n (le_of_not_gt hn))
      (Nat.mul_le_mul (by nlinarith [Nat.zero_le (∑ n ∈ .range N, f n)])
        (Nat.pow_le_pow_left (le_max_left _ _) _))

lemma polylog_bound_nat (hg : g ∈ polylog) :
    ∃ (k : ℕ) (K : ℕ), ∀ᶠ n in .atTop, g n ≤ K * (Nat.log 2 n) ^ k := by
  rcases hg with ⟨k, hk⟩
  have ⟨K, hK⟩ := hk.exists_pos
  simp only [Nat.cast_pow, Asymptotics.IsBigOWith, norm_natCast, norm_pow,
    Filter.eventually_atTop] at hK ⊢
  use k, ⌈K⌉₊
  rcases hK with ⟨hK, a, ha⟩
  refine ⟨a, fun n hn ↦ ?_⟩
  suffices h : (g n : ℝ) ≤ ⌈K⌉₊ * Nat.log 2 n ^ k from mod_cast h
  nlinarith [Nat.le_ceil K, ha n hn, show (Nat.log 2 n : ℝ) ^ k ≥ 0 by positivity]

lemma quasipoly_of_bound_nat {A k M : ℕ}
    (hf : ∀ᶠ n in .atTop, f n ≤ M * A ^ ((Nat.log 2 n) ^ k)) : f ∈ quasipoly := by
  -- Let `L = log₂ A`. Then `A < 2^(L+1)`
  set L := Nat.log 2 A
  have h_bound : ∀ᶠ n in .atTop, (f n : ℝ) ≤ M * 2 ^ ((L + 1) * (Nat.log 2 n) ^ k) := by
    filter_upwards [hf] with n hn
    have hA_le : (A : ℝ) ≤ 2 ^ (L + 1) := by
      exact_mod_cast Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)
    grw [pow_mul, ← hA_le, hn]
    exact_mod_cast le_rfl
  -- We want to bound this by `2 ^ ((log n)^(k+1))`.
  replace h_bound : ∀ᶠ n in .atTop, (f n : ℝ) ≤ M * 2 ^ ((Nat.log 2 n) ^ (k + 1)) := by
    have h_ineq : ∀ᶠ n in .atTop, (L + 1) * (Nat.log 2 n) ^ k ≤ (Nat.log 2 n) ^ (k + 1) := by
      have h_ineq : ∀ᶠ n in .atTop, (L + 1) ≤ Nat.log 2 n := by
        rw [Filter.eventually_atTop]
        exact ⟨2 ^ (L + 1), fun n ↦ Nat.le_log_of_pow_le one_lt_two⟩
      filter_upwards [h_ineq] with n hn using by rw [pow_succ']; exact Nat.mul_le_mul_right _ hn
    filter_upwards [h_bound, h_ineq] with n hn hn' using
      le_trans hn (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hn')
        (Nat.cast_nonneg _))
  refine ⟨k + 1, ?_⟩
  apply Asymptotics.isBigO_iff.mpr
  norm_num at *
  exact ⟨M, h_bound.choose, fun n hn ↦
    le_trans (h_bound.choose_spec n hn) (by norm_num [Norm.norm])⟩

theorem exp_comp_polylog (hf : f ∈ exp) (hg : g ∈ polylog) : f ∘ g ∈ quasipoly := by
  have ⟨C, M_f, hC, hf⟩ := exp_bound_nat hf
  have ⟨k, K, hg⟩ := polylog_bound_nat hg
  set K' := 1 ⊔ K
  apply quasipoly_of_bound_nat (A := C ^ K') (k := k) (M := M_f)
  simp +zetaDelta only [Filter.eventually_atTop, Function.comp_apply] at hg ⊢
  refine ⟨hg.choose, fun n hn ↦ le_trans (hf _) ?_⟩
  simpa only [← pow_mul] using Nat.mul_le_mul_left _ (pow_le_pow_right₀ hC.le <| by
    nlinarith [hg.choose_spec n hn, Nat.le_max_left 1 K, Nat.le_max_right 1 K,
      pow_nonneg (Nat.zero_le (Nat.log 2 n)) k])

theorem exp_comp_linear (hf : f ∈ exp) (hg : g ∈ linear) : f ∘ g ∈ exp := by
  -- From `hf`, we have some `C` such that `f n = O(C^n)`. We can assume `C ≥ 2` WLOG.
  have ⟨C, hC⟩ : ∃ C, (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ C ^ n : ℕ → ℤ) ∧ 2 ≤ C := by
    rcases hf with ⟨C, hC⟩
    generalize_proofs at *
    rcases C with (_ | _ | C) <;> norm_num at *
    · refine ⟨2, ?_, ?_⟩ <;> norm_num
      apply hC.trans
      simpa using Asymptotics.isBigO_of_le _ fun n ↦ by cases n <;> norm_num [pow_succ']
    · refine ⟨2, ?_, ?_⟩ <;> norm_num [Asymptotics.isBigO_iff]
      rcases hC with ⟨c, hc⟩
      norm_num [Norm.norm] at *
      refine ⟨c, hc.choose, fun n hn ↦ ?_⟩
      exact le_trans (hc.choose_spec n hn)
        (le_mul_of_one_le_right (le_trans (Nat.cast_nonneg _) (hc.choose_spec _ le_rfl))
          (one_le_pow₀ (by norm_num)))
    · exact ⟨_, hC, by linarith⟩
  have ⟨K, hK⟩ : ∃ K, ∀ᶠ n in .atTop, g n ≤ K * n := by
    have ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp hg
    norm_num at *
    refine ⟨⌈K⌉₊, hK.choose, fun n hn ↦ ?_⟩
    exact_mod_cast (hK.choose_spec n hn).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  -- Then `f (g n) = O(C^(g n))`.
  have hfg : (fun n ↦ (f (g n) : ℤ)) =O[.atTop] (fun n ↦ C ^ (g n) : ℕ → ℤ) := by
    simp only [Filter.eventually_atTop, Asymptotics.isBigO_iff', norm_natCast, norm_pow] at hK hC ⊢
    rcases hC with ⟨⟨c, hc, a, ha⟩, hC⟩
    use c + ∑ x ∈ .range (a + 1), (f x : ℝ) / ‖C‖ ^ x
    constructor
    · exact add_pos_of_pos_of_nonneg hc (Finset.sum_nonneg fun _ _ ↦
        div_nonneg (Nat.cast_nonneg _) (by positivity))
    refine ⟨a + hK.choose + 1, fun b hb ↦ ?_⟩
    simp only [add_mul]
    rcases lt_or_ge (g b) a with h | h
    · apply le_add_of_nonneg_of_le (by positivity)
      rw [Finset.sum_mul]
      exact le_trans
        (by rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos (norm_pos_iff.mpr (by linarith)) _))])
        (Finset.single_le_sum
          (fun i _ ↦ mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (norm_nonneg _) _))
            (pow_nonneg (norm_nonneg _) _))
          (Finset.mem_range.mpr (by linarith)))
    · grw [← ha _ h, le_add_iff_nonneg_right]
      positivity
  have h_mono : (fun n ↦ C ^ (g n) : ℕ → ℤ) =O[.atTop] (fun n ↦ C ^ (K * n) : ℕ → ℤ) := by
    rw [Asymptotics.isBigO_iff]
    norm_num [Norm.norm]
    have ⟨N, hN⟩ := Filter.eventually_atTop.mp hK
    refine ⟨1, N, fun n hn ↦ ?_⟩
    rw [abs_of_nonneg (by norm_cast; linarith)]
    exact (pow_le_pow_right₀ (by norm_cast; linarith) (hN n hn)).trans (by norm_num)
  have h_comp : (fun n ↦ (f (g n) : ℤ)) =O[.atTop] (fun n ↦ (C^K) ^ n : ℕ → ℤ) := by
    simpa only [pow_mul] using hfg.trans h_mono
  use C.natAbs^K
  simpa [abs_of_nonneg (by linarith : 0 ≤ C)] using h_comp

lemma _root_.Nat.Primrec.sum_range (hf : Nat.Primrec f) :
    Nat.Primrec (∑ i ∈ .range ·, f i) := by
  -- Define g such that g(n, s) = s + f(n)
  let g : ℕ → ℕ → ℕ := fun n s ↦ s + f n
  have hg : Nat.Primrec (fun p ↦ g p.unpair.1 p.unpair.2) := by
    convert Nat.Primrec.add.comp (.pair (.right) (hf.comp .left)) using 1
    simp [g]
  have hS : (fun n ↦ ∑ i ∈ .range n, f i) = fun n ↦ Nat.rec 0 (fun n s ↦ g n s) n := by
    funext n
    induction n
    · rfl
    · simp [*, Finset.sum_range_succ]
      rfl
  rw [hS]
  convert Nat.Primrec.prec1 0 hg using 1
  simp

/--
Every primitive recursive function is bounded by a monotone primitive recursive function.
-/
private lemma exists_monotone_primrec_bound {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ g, Nat.Primrec g ∧ Monotone g ∧ ∀ n, f n ≤ g n := by
  -- Let `S(n) = ∑ i in range (n+1), f i`.
  set S : ℕ → ℕ := fun n ↦ ∑ i ∈ .range (n + 1), f i
  refine ⟨S, ?_, ?_, ?_⟩
  · exact hf.sum_range.comp Nat.Primrec.succ
  · exact fun n m hnm ↦ Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hnm))
  · exact fun n ↦ Finset.single_le_sum (fun i _ ↦ Nat.zero_le (f i))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))

theorem primitiveRecursive_comp (hf : f ∈ primitiveRecursive) (hg : g ∈ primitiveRecursive) :
    f ∘ g ∈ primitiveRecursive := by
  rcases hf with ⟨h_f, hf_primrec, hf_bound⟩
  rcases hg with ⟨h_g, hg_primrec, hg_bound⟩
  -- Apply the lemma that allows bounding a primitive recursive function by a monotone one to `h_f`.
  have ⟨H_f, hH_f_primrec, hH_f_mono, hH_f_bound⟩ := exists_monotone_primrec_bound hf_primrec
  -- Thus `f(g(n)) ≤ C_f H_f(g(n)) + K`.
  have ⟨C_f, N_f, hf_bound⟩ : ∃ C_f N_f, ∀ x ≥ N_f, f x ≤ C_f * H_f x := by
    have ⟨C_f, N_f, hC_f⟩ := hf_bound.exists_pos
    rw [Asymptotics.isBigOWith_iff] at hC_f
    norm_num at *
    have ⟨N_f, hN_f⟩ := hC_f
    refine ⟨⌈C_f⌉₊, N_f, fun x hx ↦ ?_⟩
    specialize hN_f x hx
    exact_mod_cast hN_f.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hH_f_bound x))
      (by positivity)) |> le_trans <| mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _)
  have ⟨C_g, N_g, hg_bound⟩ : ∃ C_g N_g, ∀ n ≥ N_g, g n ≤ C_g * h_g n := by
    rw [bigO, Set.mem_setOf_eq, Asymptotics.isBigO_iff'] at hg_bound
    norm_num at *
    have ⟨c, hc₀, N_g, hc⟩ := hg_bound
    refine ⟨⌈c⌉₊, N_g, fun n hn ↦ ?_⟩
    exact_mod_cast (hc n hn).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  have ⟨K, hK⟩ : ∃ K, ∀ x < N_f, f x ≤ K :=
    ⟨(Finset.range N_f).sup f, fun x hx ↦ Finset.le_sup (Finset.mem_range.mpr hx)⟩
  -- Thus for `n ≥ N_g`, `f(g(n)) ≤ C_f H_f(C_g h_g(n)) + K`.
  have h_comp_bound : ∀ n ≥ N_g, f (g n) ≤ C_f * H_f (C_g * h_g n) + K := by
    intros n hn
    specialize hH_f_mono (hg_bound _ hn)
    rcases lt_or_ge (g n) N_f with hgn | hgn
    · exact le_add_of_nonneg_of_le (Nat.zero_le _) (hK _ hgn)
    · exact le_add_of_le_of_nonneg ((hf_bound _ hgn).trans (mul_le_mul_right hH_f_mono _)) K.zero_le
  -- The function `B(n) = C_f H_f(C_g h_g(n)) + K` is primitive recursive.
  have hB_primrec : Nat.Primrec (fun n ↦ C_f * H_f (C_g * h_g n) + K) := by
    have h_const_mul : Nat.Primrec (fun n ↦ C_g * n) := by
      convert Nat.Primrec.mul.comp (Nat.Primrec.const C_g |>.pair Nat.Primrec.id) using 1
      simp [Nat.unpair_pair]
    have h_Cg_hg : Nat.Primrec (fun n ↦ C_g * h_g n) := h_const_mul.comp hg_primrec
    have h_Hf_comp : Nat.Primrec (fun n ↦ H_f (C_g * h_g n)) := hH_f_primrec.comp h_Cg_hg
    have h_mul_Cf : Nat.Primrec (fun n ↦ C_f * n) := by
      have h_mul_step : ∀ m, Nat.Primrec (fun n ↦ n * m) := by
        intro m
        induction m with
        | zero => simp [Nat.Primrec.const]
        | succ k hk =>
          simp_all only [Nat.mul_succ]
          convert Nat.Primrec.add.comp (hk.pair Nat.Primrec.id) using 1
          exact funext fun n ↦ by simp [Nat.unpair_pair]
      simpa only [mul_comm] using h_mul_step C_f
    have h_Cf_Hf : Nat.Primrec (fun n ↦ C_f * H_f (C_g * h_g n)) := h_mul_Cf.comp h_Hf_comp
    have h_add_K : Nat.Primrec (fun n ↦ n + K) :=
      Nat.recOn K Nat.Primrec.id fun _ ihn ↦ Nat.Primrec.succ.comp ihn
    exact h_add_K.comp h_Cf_Hf
  refine ⟨_, hB_primrec, ?_⟩
  apply Asymptotics.IsBigO.of_bound 1
  simp only [Function.comp_apply, norm_natCast, Nat.cast_add, Nat.cast_mul, one_mul,
    Filter.eventually_atTop]
  refine ⟨N_g, fun n hn ↦ ?_⟩
  grw [h_comp_bound n hn]
  convert le_refl _
  exact Real.norm_of_nonneg (by positivity)

section computable

/-
`max_scan f n` computes the maximum value of `f` on `0..n`.
-/
private def max_scan (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (f 0) (fun k acc ↦ acc ⊔ (f (k + 1))) n

private lemma max_scan_le (n : ℕ) : f n ≤ max_scan f n := by
  induction n <;> simp [*, max_scan]

private lemma max_scan_mono (f : ℕ → ℕ) : Monotone (max_scan f) := by
  exact monotone_nat_of_le_succ fun k ↦ le_max_left ..

private lemma computable_max_scan {f : ℕ → ℕ} (hf : Computable f) : Computable (max_scan f) := by
  open Computable in
  apply nat_rec .id (h := fun _ p ↦ p.2 ⊔ (f (p.1 + 1))) (.const (f 0))
  apply Computable₂.comp₂
      (f := fun (p : ℕ × ℕ) (q : ℕ × ℕ) ↦ p.2 ⊔ q.2)
      (g := fun _ (p : ℕ × ℕ) ↦ (p.1, p.2)) (h := fun _ p ↦ (p.1, f (p.1 + 1)))
  · exact (Primrec₂.to_comp Primrec.nat_max).comp (comp snd fst) (comp snd snd)
  · exact pair (comp fst snd) (comp snd snd)
  · exact pair (comp fst (comp snd .id)) (hf.comp <| succ.comp <| comp fst <| comp snd .id)

lemma bigO_implies_bound {f g : ℕ → ℕ} (h : f ∈ bigO g) :
    ∃ C K, ∀ n, f n ≤ C * g n + K := by
  have ⟨C, hC⟩ := h.exists_pos
  rw [Asymptotics.IsBigOWith] at hC
  simp only [norm_natCast, Filter.eventually_atTop] at hC
  rcases hC with ⟨hC, a, hA⟩
  -- Let `K` be the maximum of `f(n)` for `n < N`.
  have ⟨K, hK⟩ : ∃ K, ∀ n < a, f n ≤ K :=
    ⟨(Finset.range a).sup f, fun n hn ↦ Finset.le_sup (Finset.mem_range.mpr hn)⟩
  refine ⟨⌈C⌉₊, K, fun n ↦ ?_⟩
  rcases lt_or_ge n a with hn | hn
  · exact (hK n hn).trans (by norm_num)
  · specialize hA n hn
    exact_mod_cast (by nlinarith [Nat.le_ceil C, show (g n : ℝ) ≥ 0 by positivity] :
      (f n : ℝ) ≤ ⌈C⌉₊ * g n + K)

lemma bound_implies_bigO {f g : ℕ → ℕ} (C K : ℕ) (h : ∀ n, f n ≤ C * g n + K) :
    f ∈ bigO (fun n ↦ g n + 1) := by
  simp only [bigO, Nat.cast_add, Nat.cast_one, Asymptotics.isBigO_iff, norm_natCast,
    Filter.eventually_atTop, Set.mem_setOf_eq]
  use C + K + 1, 0
  refine fun n hn ↦ ?_
  erw [Real.norm_of_nonneg (by positivity)]
  norm_cast
  nlinarith [h n]

lemma exists_monotone_computable_bound {f : ℕ → ℕ} (hf : Computable f) :
    ∃ F, Computable F ∧ Monotone F ∧ f ∈ bigO F := by
  refine ⟨max_scan f, computable_max_scan hf, max_scan_mono f, ?_⟩
  apply Asymptotics.IsBigO.of_bound 1
  norm_num
  exact ⟨0, fun n hn ↦ max_scan_le n⟩

/--
The function `n ↦ C * n + K` is computable.
-/
private lemma computable_affine (C K : ℕ) : Computable (fun n ↦ C * n + K) := by
  apply Computable.comp (f := fun n ↦ n + K) (g := fun n ↦ C * n)
  · induction K with
    | zero => exact Computable.id
    | succ _ ih =>
      simp only [Nat.add_comm, Nat.add_left_comm] at ih ⊢
      exact ih.comp Computable.succ
  · apply Primrec.to_comp
    induction C with
    | zero => simp [Primrec.const]
    | succ _ ih =>
      simp_rw [Nat.succ_mul]
      exact Primrec.nat_add.comp ih Primrec.id

theorem computable_comp (hf : f ∈ computable) (hg : g ∈ computable) :
    f ∘ g ∈ computable := by
  rcases hf with ⟨f', hf', hf⟩
  rcases hg with ⟨g', hg', hg⟩
  have ⟨F, hF₁, hF₂⟩ := exists_monotone_computable_bound hf'
  have ⟨C₁, K₁, hC₁⟩ := bigO_implies_bound hg
  have ⟨C₂, K₂, hC₂⟩ := bigO_implies_bound (hf.trans hF₂.2)
  -- Define H(n) = C₂ * F(C₁ * g'(n) + K₁) + K₂.
  set H : ℕ → ℕ := fun n ↦ C₂ * F (C₁ * g' n + K₁) + K₂
  refine ⟨H, ?_, ?_⟩
  · exact (computable_affine _ _).comp <| hF₁.comp <| (computable_affine _ _).comp hg'
  have hfg_le_H : ∀ n, f (g n) ≤ H n := fun n ↦
    le_trans (hC₂ _) (add_le_add_left (mul_le_mul_of_nonneg_left (hF₂.1 (hC₁ _)) (Nat.zero_le _)) _)
  simp_rw [bigO, Set.mem_setOf_eq, Asymptotics.isBigO_iff, Filter.eventually_atTop]
  use 1, 0
  exact fun n hn ↦ by simpa using hfg_le_H n

end computable

end closure_comp

end GrowthRate
