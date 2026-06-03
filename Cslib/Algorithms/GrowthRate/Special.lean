/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

module

public import Cslib.Algorithms.GrowthRate.Defs

/-!
# Named Growth Rates

Defining the rate classes, sorted in order of growing more quickly.

```
const       := bigO 1
log         := bigO (Nat.log 2)
polylog     := setOf ...
sqrt        := bigO Nat.sqrt
sublinear   := littleO id
linear      := bigO id
linearithmic := bigO (fun n ↦ n * Nat.log 2 n)
nearLinear  := setOf ...
almostLinear := setOf ...
poly        := setOf ...
quasipoly   := setOf ...
twoPow     := bigO (2 ^ ·)
ePow       := bigO (⌈Real.exp ·⌉₊)
exp         := setOf ...
primitiveRecursive := setOf ...
computable := setOf ...
```

Each of these has a `LawfulGrowthRate` instance, showing that they're reasonably well-behaved.
Several have important alternate characterizations in terms of different functions. For instance,
`GrowthRate.polylog` is defined as `∃ (C : ℤ), O(n * Nat.log 2 n ^ C)`. The theorem
`GrowthRate.polylog_iff_rlog` shows that this is equivalent to `∃ (C : ℝ), O(n * Real.log n ^ C)`,
which is more convenient if your goals involve real numbers and real logarithms. (Also because
`Real.log` satisfies many nice extra properties such as `log (x*y) = log x + log y`.)

There are similar theorems for converting between real vs. integer exponents, `Nat.sqrt` vs.
`Real.sqrt`, and natural number powers vs. `Real.rpow` vs. `Real.exp`.
-/

@[expose] public section

namespace CSLib

open scoped Topology

namespace GrowthRate

variable {f g a b : ℕ → ℕ}

section defs

/-- Logarithmic growth rates: `O(log n)` -/
abbrev log := bigO (Nat.log 2)

/-- Polylogarithmic growth rates: `(log n) ^ O(1)` -/
def polylog : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(Nat.log 2 n ^ C) : ℕ → ℤ)

/-- Square-root growth rates: `O(√n)` -/
abbrev sqrt := bigO Nat.sqrt

/-- linearithmic growth rates: `O(n * log n)` -/
abbrev linearithmic := bigO (fun n ↦ n * Nat.log 2 n)

/-- Near-linear growth rates: `n * (log n)^O(1)` -/
def nearLinear : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(n * Nat.log 2 n ^ C) : ℕ → ℤ)

/-- Almost-linear growth rates: `O(n ^ {1 + o(1)})`, equivalently `O(n^{1+ε})` for every `ε > 0`.

This is a standard complexity class that sits strictly between near-linear (`n · (log n)^O(1)`) and
polynomial (`n^O(1)`) growth. Examples include `n · exp(√(log n))`. -/
def almostLinear : GrowthRate :=
  setOf <| fun f ↦ ∀ ε : ℝ, ε > 0 →
    (f · : ℕ → ℝ) =O[Filter.atTop] (fun n ↦ (n : ℝ) ^ (1 + ε))

/-- Polynomial growth rates: `n ^ O(1)` -/
def poly : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (· ^ C : ℕ → ℤ)

/-- Quasipolynomial growth rates: `2 ^ {log(n) ^ O(1)}` -/
def quasipoly : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ 2 ^ (Nat.log 2 n ^ C) : ℕ → ℤ)

/-- `O(2 ^ n)` growth rates, not to be confused with `exp` which is `2 ^ O(n)`. -/
abbrev twoPow := bigO (2 ^ ·)

/-- `O(e ^ n)` growth rates, not to be confused with `exp` which is `e ^ O(n)`. -/
abbrev ePow := bigO (⌈Real.exp ·⌉₊)

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

section lawful_instances


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

lemma nearLinear_bound_mono (C : ℕ) : Monotone (fun n ↦ n * (Nat.log 2 n) ^ C) := by
  exact fun a b hab ↦ Nat.mul_le_mul hab (Nat.pow_le_pow_left (Nat.log_mono_right hab) _)

lemma isBigO_nearLinear_bound_comp_le_id (C : ℕ) (g : ℕ → ℕ) (hg : g ≤ id) :
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

lemma one_isBigO_nearLinear_bound (C : ℕ) :
    (fun _ ↦ (1 : ℤ)) =O[.atTop] (fun n ↦ (n * (Nat.log 2 n) ^ C : ℤ)) := by
  rw [Asymptotics.isBigO_iff]
  use 1; norm_num
  refine ⟨2, fun n hn ↦ ?_⟩
  exact one_le_mul_of_one_le_of_one_le (by norm_cast; linarith)
    (one_le_pow₀ (mod_cast Nat.log_pos one_lt_two (by linarith)))

instance : LawfulGrowthRate nearLinear where
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
    exact (isBigO_nearLinear_bound_comp_le_id C g hg).add (one_isBigO_nearLinear_bound C)

private lemma almostLinear_comp_le_id {f g : ℕ → ℕ}
    (hf : f ∈ almostLinear) (hg : g ≤ id) : f ∘ g ∈ almostLinear := by
  intro ε hε
  obtain ⟨C, hC⟩ : ∃ C > 0, ∀ᶠ n in Filter.atTop, f n ≤ C * (n : ℝ) ^ (1 + ε) := by
    obtain ⟨C, hC⟩ := hf ε hε |> Asymptotics.isBigO_iff.mp
    use C ⊔ 1, by positivity
    filter_upwards [hC] with n hn
    convert hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) using 2
    · simp
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, f n ≤ C * (n : ℝ) ^ (1 + ε) := by simp_all
  obtain ⟨M, hM⟩ : ∃ M > 0, ∀ n < N, f n ≤ M :=
    ⟨∑ n ∈ Finset.range N, f n + 1, Nat.succ_pos _, fun n hn =>
      Nat.le_succ_of_le <| Finset.single_le_sum (fun n _ => Nat.zero_le (f n)) <|
      Finset.mem_range.mpr hn⟩
  refine Asymptotics.IsBigO.of_bound (C + M) ?_
  simp only [Filter.eventually_atTop, RCLike.norm_natCast, Real.norm_eq_abs] at *
  refine ⟨N, fun n hn => ?_⟩
  by_cases h : g n < N
  · simp only [add_mul]
    apply le_add_of_nonneg_of_le <| mul_nonneg hC.1.le <| abs_nonneg _
    apply le_trans (Nat.cast_le.mpr (hM.2 _ h))
    grind only [Real.one_le_rpow, Nat.one_le_cast, le_mul_of_one_le_right, abs_of_nonneg]
  · simp only [not_lt, add_mul] at h ⊢
    exact le_add_of_le_of_nonneg (le_trans (hN _ h) (mul_le_mul_of_nonneg_left (by
      rw [abs_of_nonneg (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (mod_cast hg n) (by positivity)) hC.1.le))
      (by positivity)

instance : LawfulGrowthRate almostLinear where
  mem_dominating {f g} h hf ε hε := by
    specialize hf ε hε
    simp only [Filter.eventually_atTop, Asymptotics.isBigO_iff] at h hf ⊢
    rcases hf with ⟨C, a, ha⟩
    rcases h with ⟨N, hN⟩
    refine ⟨C, N ⊔ a, fun n hn => ?_⟩
    trans (f n : ℝ)
    · exact mod_cast hN n <| (le_max_left N a).trans hn
    · exact mod_cast ha n <| (le_max_right N a).trans hn
  mem_add hf hg ε h := by
    simpa using (hf ε h).add (hg ε h)
  one_mem ε hε := by
    simp_rw [Asymptotics.isBigO_iff, Filter.eventually_atTop]
    refine ⟨1, 1, fun x hx => ?_⟩
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    simpa using Real.one_le_rpow (mod_cast hx) (by positivity)
  comp_le_id := almostLinear_comp_le_id

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
      simp only [norm_pow, norm_natCast, one_mul, Filter.eventually_atTop]
      use 1
      intro _ hn
      exact_mod_cast pow_le_pow_right₀ hn (by bound)
   )
  one_mem := by
    simp only [poly, Asymptotics.isBigO_iff, Filter.eventually_atTop]
    use 0, 1, 0
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

instance : LawfulGrowthRate twoPow := by
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

instance : LawfulGrowthRate ePow := by
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

/-- The step function for `runningMax` is primitive recursive. -/
private def runningMaxStep (f : ℕ → ℕ) (n res : ℕ) : ℕ := res ⊔ (f (n + 1))

private lemma runningMaxStep_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
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

/-- If `f` is primitive recursive, then `runningMax f` is primitive recursive. -/
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

/--
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

/-- If `h` is monotone and `≥ 1`, and `f = O(h)` and `g ≤ id`, then `f ∘ g = O(h)`. -/
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

end lawful_instances


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

theorem nearLinear_iff_rlog {f : ℕ → ℕ} : f ∈ nearLinear ↔
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
    simpa [nearLinear, Asymptotics.isBigO_iff] using h_nat_log

/-- `almostLinear` is the intersection of `O(n^{1+ε})` over all `ε > 0`. -/
theorem almostLinear_eq_iInter :
    (almostLinear : Set (ℕ → ℕ)) =
      ⋂ (ε : ℝ) (_ : ε > 0), bigO (fun n ↦ ⌈(n : ℝ) ^ (1 + ε)⌉₊) := by
  ext f
  constructor
  · intro hf
    refine Set.mem_iInter₂.2 fun ε hε => ?_
    convert hf ε hε using 1
    constructor <;> intro h <;> rw [Asymptotics.isBigO_iff] at *
    · convert hf ε hε using 1
      norm_num [Asymptotics.isBigO_iff]
    · simp_all only [norm, Nat.abs_cast, Filter.eventually_atTop]
      obtain ⟨c, a, h⟩ := h
      refine Asymptotics.isBigO_iff.mpr ⟨⌈c⌉₊, ?_⟩
      simp only [norm_natCast, Filter.eventually_atTop]
      exact ⟨a, fun n hn => le_trans (h n hn) (by
        rw [abs_of_nonneg (by positivity)]
        exact mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (by positivity) (by positivity))⟩
  · intro hf ε hε_pos
    have h_f_in_bigO : (f · : ℕ → ℝ) =O[Filter.atTop] (fun n ↦ (n : ℝ) ^ (1 + ε)) := by
      have h_f_in_bigO : (f · : ℕ → ℝ) =O[Filter.atTop]
          (fun n ↦ (⌈(n : ℝ) ^ (1 + ε)⌉₊ : ℝ)) := by
        simp only [bigO, Set.mem_iInter, Set.mem_setOf_eq] at hf
        convert hf ε hε_pos using 1
        norm_num [Asymptotics.isBigO_iff]
      refine h_f_in_bigO.trans ?_
      norm_num [Asymptotics.isBigO_iff]
      exact ⟨2, 1, fun n hn => by
        rw [abs_of_nonneg (by positivity)]
        linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ (1 + ε)),
          show (n : ℝ) ^ (1 + ε) ≥ 1 by exact Real.one_le_rpow (by norm_cast) (by positivity)]⟩
    exact h_f_in_bigO

theorem poly_iff_rpow {f : ℕ → ℕ} : f ∈ poly ↔
    ∃ (C : ℝ), (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ n ^ C : ℕ → ℝ) := by
  simp only [poly, Asymptotics.isBigO_iff, Int.norm_natCast, Filter.eventually_atTop,
     Set.mem_setOf_eq, Real.norm_eq_abs, Nat.abs_cast]
  use fun ⟨C, c, a, h⟩ ↦ ⟨C, c, a, fun b hb ↦ by simpa using h b hb⟩
  refine fun ⟨C, c, a, h⟩ ↦ ⟨⌈C⌉₊, c ⊔ 1, a + 1, fun b _ ↦ (h b (by linarith)).trans ?_⟩
  refine mul_le_mul (le_max_left c 1) ?_ (by positivity) (by positivity)
  rw [abs_of_nonneg (by positivity)]
  exact (Real.rpow_le_rpow_of_exponent_le (mod_cast by linarith) (Nat.le_ceil C)).trans (by simp)

lemma bigO_const_pow_log_le_twoPow_log (A : ℝ) (C : ℕ) :
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
  exact (bigO_const_pow_log_le_twoPow_log A C).imp (fun _ ↦ hC.trans)

theorem ePow_iff_rexp {f : ℕ → ℕ} : f ∈ ePow ↔
    (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ Real.exp x) := by
  have h_ceil (n : ℕ) : ⌈(Real.exp n)⌉₊ ≤ 2 * (Real.exp n) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_nonneg n), Real.add_one_le_exp n]
  rw [ePow, bigO, Set.mem_setOf]
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

end GrowthRate

end CSLib
