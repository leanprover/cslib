/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
# Discrete Probability Helpers

This file provides lightweight probability helpers on top of Mathlib's `PMF`,
staying in `ℝ` (not `ℝ≥0∞`). The main definitions support the coin-passing
style used throughout the cryptographic security games.

## Main Definitions

* `boolToReal` — indicator function `Bool → ℝ`
* `uniformExpect` — expected value of `f(c)` when `c` is sampled uniformly
* `uniformProb` — probability of an event under the uniform distribution

## Design Notes

We work in `ℝ` rather than `ℝ≥0∞` to avoid coercion complications in game
definitions. The `ENNReal.toReal` conversion from `PMF.uniformOfFintype` is
safe on finite types since the masses are `1 / |α|`, which is finite.

## References

* [O. Goldreich, *Foundations of Cryptography, Vol. 1*][Goldreich2001]
-/

namespace Cslib.Probability

/-- Convert a `Bool` to `ℝ`: `true ↦ 1`, `false ↦ 0`. -/
def boolToReal (b : Bool) : ℝ := if b then 1 else 0

theorem boolToReal_nonneg (b : Bool) : 0 ≤ boolToReal b := by
  simp [boolToReal]; split <;> norm_num

theorem boolToReal_le_one (b : Bool) : boolToReal b ≤ 1 := by
  simp [boolToReal]; split <;> norm_num

/-- Expected value of `f(c)` when `c` is sampled uniformly from a `Fintype`.

This is `∑ a, (1 / |α|) * f(a)`, i.e., the average of `f` over all elements. -/
noncomputable def uniformExpect (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℝ) : ℝ :=
  ∑ a : α, (PMF.uniformOfFintype α a).toReal * f a

/-- `uniformExpect` equals `(1 / |α|) * ∑ a, f(a)`. -/
theorem uniformExpect_eq (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    uniformExpect α f = (1 / Fintype.card α) * ∑ a : α, f a := by
  unfold uniformExpect
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  rw [Finset.mul_sum]

/-- If `f ≥ 0` pointwise then `uniformExpect α f ≥ 0`. -/
theorem uniformExpect_nonneg (α : Type*) [Fintype α] [Nonempty α]
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ uniformExpect α f := by
  unfold uniformExpect
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (ENNReal.toReal_nonneg) (hf a)

/-- `uniformExpect` of a constant function equals the constant. -/
theorem uniformExpect_const (α : Type*) [Fintype α] [Nonempty α]
    (c : ℝ) : uniformExpect α (fun _ => c) = c := by
  rw [uniformExpect_eq]
  simp [Finset.sum_const, Finset.card_univ]

/-- Probability of a decidable event under the uniform distribution. -/
noncomputable def uniformProb (α : Type*) [Fintype α] [Nonempty α]
    (p : α → Prop) [DecidablePred p] : ℝ :=
  uniformExpect α (fun a => if p a then 1 else 0)

/-- `uniformProb α p ≤ 1`. -/
theorem uniformProb_le_one (α : Type*) [Fintype α] [Nonempty α]
    (p : α → Prop) [DecidablePred p] :
    uniformProb α p ≤ 1 := by
  unfold uniformProb
  rw [uniformExpect_eq]
  have hcard_pos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
  rw [div_mul_eq_mul_div, one_mul]
  rw [div_le_one hcard_pos]
  calc ∑ a : α, (if p a then (1 : ℝ) else 0)
      ≤ ∑ _a : α, (1 : ℝ) :=
        Finset.sum_le_sum fun a _ => by split <;> norm_num
    _ = Fintype.card α := by simp [Finset.sum_const, Finset.card_univ]

/-- `uniformProb α p ≥ 0`. -/
theorem uniformProb_nonneg (α : Type*) [Fintype α] [Nonempty α]
    (p : α → Prop) [DecidablePred p] :
    0 ≤ uniformProb α p :=
  uniformExpect_nonneg α fun a => by split <;> norm_num

/-- `uniformExpect` is additive: `E[f + g] = E[f] + E[g]`. -/
theorem uniformExpect_add (α : Type*) [Fintype α] [Nonempty α]
    (f g : α → ℝ) :
    uniformExpect α (fun a => f a + g a) =
      uniformExpect α f + uniformExpect α g := by
  simp only [uniformExpect_eq]
  rw [← mul_add, Finset.sum_add_distrib]

/-- `uniformExpect` distributes over subtraction: `E[f - g] = E[f] - E[g]`. -/
theorem uniformExpect_sub (α : Type*) [Fintype α] [Nonempty α]
    (f g : α → ℝ) :
    uniformExpect α (fun a => f a - g a) =
      uniformExpect α f - uniformExpect α g := by
  simp only [uniformExpect_eq]
  rw [← mul_sub, Finset.sum_sub_distrib]

/-- `uniformExpect` scales: `E[c * f] = c * E[f]`. -/
theorem uniformExpect_smul (α : Type*) [Fintype α] [Nonempty α]
    (c : ℝ) (f : α → ℝ) :
    uniformExpect α (fun a => c * f a) = c * uniformExpect α f := by
  simp only [uniformExpect_eq, ← Finset.mul_sum]
  ring

/-- Jensen's inequality for absolute value: `|E[f]| ≤ E[|f|]`. -/
theorem uniformExpect_abs_le (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    |uniformExpect α f| ≤ uniformExpect α (fun a => |f a|) := by
  simp only [uniformExpect_eq]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Fintype.card α)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- Fubini for `uniformExpect`: `E_{(a,b)}[f] = E_a[E_b[f(a,b)]]`. -/
theorem uniformExpect_prod (α β : Type*) [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (f : α × β → ℝ) :
    uniformExpect (α × β) f =
      uniformExpect α (fun a => uniformExpect β (fun b => f (a, b))) := by
  simp only [uniformExpect_eq, Fintype.card_prod, Nat.cast_mul]
  rw [Fintype.sum_prod_type f]
  have hα : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  have hβ : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  rw [show (1 : ℝ) / (↑(Fintype.card α) * ↑(Fintype.card β)) =
    (1 / ↑(Fintype.card α)) * (1 / ↑(Fintype.card β)) from by ring]
  rw [mul_assoc, Finset.mul_sum]

/-- Invariance of `uniformExpect` under an equivalence (bijection):
`E[f ∘ σ] = E[f]` for any `σ : α ≃ α`. -/
theorem uniformExpect_equiv (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℝ) (σ : α ≃ α) :
    uniformExpect α (fun a => f (σ a)) = uniformExpect α f := by
  simp only [uniformExpect_eq]
  congr 1
  exact Finset.sum_equiv σ (by simp) (by simp)

/-- Averaging/pigeonhole: `uniformExpect α f ≤ f a` for some `a`.

If the average of `f` exceeds every value, we get a contradiction
since the average of values all strictly below the average is
strictly below the average. -/
theorem uniformExpect_le_exists (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℝ) : ∃ a, uniformExpect α f ≤ f a := by
  by_contra h
  push_neg at h
  have hcard_pos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hsum_lt : ∑ a : α, f a < ∑ _a : α, uniformExpect α f :=
    Finset.sum_lt_sum (fun a _ => le_of_lt (h a))
      ⟨(‹Nonempty α›).some, Finset.mem_univ _, h _⟩
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum_lt
  have key : (Fintype.card α : ℝ) * uniformExpect α f = ∑ a : α, f a := by
    rw [uniformExpect_eq]; field_simp
  linarith

/-- Fubini for `uniformExpect`: swapping the order of expectation.

Both sides equal `(1/(|α|*|β|)) * ∑ a, ∑ b, f a b`. -/
theorem uniformExpect_comm (α β : Type*) [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (f : α → β → ℝ) :
    uniformExpect α (fun a => uniformExpect β (fun b => f a b)) =
    uniformExpect β (fun b => uniformExpect α (fun a => f a b)) := by
  simp only [uniformExpect_eq]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext b; congr 1; ext a; ring

/-- If a function on a product doesn't depend on the second component,
the expectation reduces to the marginal over the first component. -/
theorem uniformExpect_prod_ignore_snd {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (g : α → ℝ) :
    uniformExpect (α × β) (fun p => g p.1) = uniformExpect α g := by
  rw [uniformExpect_prod]
  congr 1; ext a; exact uniformExpect_const β (g a)

/-- If a function on a product doesn't depend on the first component,
the expectation reduces to the marginal over the second component. -/
theorem uniformExpect_prod_ignore_fst {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (g : β → ℝ) :
    uniformExpect (α × β) (fun p => g p.2) = uniformExpect β g := by
  rw [uniformExpect_prod]
  exact uniformExpect_const α (uniformExpect β g)

/-- Factor out unused components from a product expectation. Given a 5-tuple
`A × B × C × D × E`, if the function only uses the `A`, `C`, and `E` components,
the expectation equals the expectation over `A × C × E`. -/
theorem uniformExpect_prod5_ignore_bd {A B C D E : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] [Fintype E] [Nonempty E]
    (g : A → C → E → ℝ) :
    uniformExpect (A × B × C × D × E)
      (fun r => g r.1 r.2.2.1 r.2.2.2.2) =
    uniformExpect (A × C × E)
      (fun r => g r.1 r.2.1 r.2.2) := by
  simp only [uniformExpect_eq, Fintype.card_prod, Nat.cast_mul]
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hB : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hD : (Fintype.card D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  simp_rw [← Finset.mul_sum]
  ring

/-- Factor out unused components from a product expectation. Given a 5-tuple
`A × B × C × D × E`, if the function only uses the `B`, `C`, and `D` components,
the expectation equals the expectation over `B × C × D`. -/
theorem uniformExpect_prod5_ignore_ae {A B C D E : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] [Fintype E] [Nonempty E]
    (g : B → C → D → ℝ) :
    uniformExpect (A × B × C × D × E)
      (fun r => g r.2.1 r.2.2.1 r.2.2.2.1) =
    uniformExpect (B × C × D)
      (fun r => g r.1 r.2.1 r.2.2) := by
  simp only [uniformExpect_eq, Fintype.card_prod, Nat.cast_mul]
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hA : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hE : (Fintype.card E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  simp_rw [← Finset.mul_sum]
  -- Unlike `ignore_bd`, `field_simp` already leaves the goal in normal form here

/-- Monotonicity of `uniformExpect`: if `f ≤ g` pointwise then `E[f] ≤ E[g]`. -/
theorem uniformExpect_mono (α : Type*) [Fintype α] [Nonempty α]
    {f g : α → ℝ} (hle : ∀ a, f a ≤ g a) :
    uniformExpect α f ≤ uniformExpect α g := by
  unfold uniformExpect
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (hle a) ENNReal.toReal_nonneg

/-- Jensen's inequality for squares: `E[f]² ≤ E[f²]`.

Follows from the variance identity: `E[(f - μ)²] ≥ 0` implies
`E[f²] - μ² ≥ 0` where `μ = E[f]`. -/
theorem uniformExpect_sq_le (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    (uniformExpect α f) ^ 2 ≤ uniformExpect α (fun a => f a ^ 2) := by
  set μ := uniformExpect α f
  suffices h : 0 ≤ uniformExpect α (fun a => f a ^ 2) - μ ^ 2 by linarith
  have key : uniformExpect α (fun a => (f a - μ) ^ 2) =
      uniformExpect α (fun a => f a ^ 2) - μ ^ 2 := by
    trans uniformExpect α (fun a => f a ^ 2 + (-2 * μ * f a + μ ^ 2))
    · congr 1; ext a; ring
    rw [uniformExpect_add, uniformExpect_add, uniformExpect_smul, uniformExpect_const]
    ring
  linarith [uniformExpect_nonneg α (fun a => sq_nonneg (f a - μ))]

/-- Transport `uniformExpect` along a type equivalence `α ≃ β`:
`E[f ∘ e] over α = E[f] over β`. -/
theorem uniformExpect_congr {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : α ≃ β) (f : β → ℝ) :
    uniformExpect α (f ∘ e) = uniformExpect β f := by
  simp only [uniformExpect_eq, Fintype.card_congr e]
  congr 1
  exact Finset.sum_equiv e (by simp) (by simp)

/-- Pull a finite sum out of `uniformExpect`:
`E[∑ j, f j a] = ∑ j, E[f j a]`. -/
theorem uniformExpect_finsum {α : Type*} [Fintype α] [Nonempty α]
    {n : ℕ} (f : Fin n → α → ℝ) :
    uniformExpect α (fun a => ∑ j : Fin n, f j a) =
      ∑ j : Fin n, uniformExpect α (f j) := by
  simp only [uniformExpect_eq, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Independence of factors in product expectations:
`E_{(a,b)}[f(a) * g(b)] = E[f] * E[g]`. -/
theorem uniformExpect_prod_mul {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (f : α → ℝ) (g : β → ℝ) :
    uniformExpect (α × β) (fun p => f p.1 * g p.2) =
      uniformExpect α f * uniformExpect β g := by
  rw [uniformExpect_prod]
  have : ∀ a : α, uniformExpect β (fun b => f a * g b) =
      f a * uniformExpect β g :=
    fun a => uniformExpect_smul β (f a) g
  simp_rw [this]
  rw [show (fun a => f a * uniformExpect β g) =
      (fun a => uniformExpect β g * f a) from by ext; ring,
    uniformExpect_smul]; ring

/-- If `acc²/q ≤ ε + acc/C` (with `0 ≤ acc ≤ 1`, `q > 0`, `C > 0`)
then `acc ≤ √(q * ε + q / C)`.

This is the algebraic step that inverts the forking lemma bound. -/
theorem quadratic_sqrt_bound {acc q ε C : ℝ}
    (h_nn : 0 ≤ acc) (h_le1 : acc ≤ 1) (hq : 0 < q) (hC : 0 < C)
    (h : acc ^ 2 / q ≤ ε + acc / C) :
    acc ≤ Real.sqrt (q * ε + q / C) := by
  -- From h: acc² ≤ q * ε + q * acc / C
  have h1 : acc ^ 2 ≤ q * ε + q * (acc / C) := by
    have h_mul := mul_le_mul_of_nonneg_right h (le_of_lt hq)
    have h_cancel : acc ^ 2 / q * q = acc ^ 2 := div_mul_cancel₀ _ (ne_of_gt hq)
    linarith [show (ε + acc / C) * q = q * ε + q * (acc / C) from by ring]
  -- From acc ≤ 1: q * acc / C ≤ q / C
  have h2 : q * (acc / C) ≤ q / C := by
    have h_le : acc / C ≤ 1 / C := div_le_div_of_nonneg_right h_le1 (le_of_lt hC)
    have h_mul : q * (acc / C) ≤ q * (1 / C) := mul_le_mul_of_nonneg_left h_le (le_of_lt hq)
    linarith [show q * (1 / C) = q / C from by ring]
  -- So acc² ≤ q * ε + q / C
  have h3 : acc ^ 2 ≤ q * ε + q / C := by linarith
  -- acc = √(acc²) ≤ √(q * ε + q / C) by monotonicity of sqrt
  calc acc = Real.sqrt (acc ^ 2) := by
        rw [Real.sqrt_sq h_nn]
    _ ≤ Real.sqrt (q * ε + q / C) := by
        exact Real.sqrt_le_sqrt h3

/-- **Fundamental lemma of game hopping**: if two `[0,1]`-valued functions
agree except on a "bad" event, the difference of their expectations is
bounded by the probability of the bad event.

This is the key tool for bounding the gap in game-hopping proofs:
when transitioning from Game 0 to Game 1, the adversary's advantage
changes by at most the probability that the "bad" distinguishing
event occurs. -/
theorem uniformExpect_game_hop (α : Type*) [Fintype α] [Nonempty α]
    (f₀ f₁ : α → ℝ) (bad : α → Prop) [DecidablePred bad]
    (h_agree : ∀ a, ¬bad a → f₀ a = f₁ a)
    (h0_nn : ∀ a, 0 ≤ f₀ a) (h0_le : ∀ a, f₀ a ≤ 1)
    (h1_nn : ∀ a, 0 ≤ f₁ a) (h1_le : ∀ a, f₁ a ≤ 1) :
    |uniformExpect α f₀ - uniformExpect α f₁| ≤
    uniformExpect α (fun a => if bad a then 1 else 0) := by
  -- |E[f₀] - E[f₁]| = |E[f₀ - f₁]| ≤ E[|f₀ - f₁|] ≤ E[1{bad}]
  rw [← uniformExpect_sub]
  refine le_trans (uniformExpect_abs_le α _) ?_
  apply uniformExpect_mono
  intro a
  by_cases h : bad a
  · -- bad a: |f₀ a - f₁ a| ≤ 1
    simp only [h, ite_true]
    rw [abs_le]; exact ⟨by linarith [h0_nn a, h1_le a],
                         by linarith [h0_le a, h1_nn a]⟩
  · -- ¬bad a: f₀ a = f₁ a, so |f₀ a - f₁ a| = 0
    simp only [h, ite_false]
    rw [h_agree a h, sub_self, abs_zero]

/-- Factor out unused components from a product expectation. Given a 5-tuple
`A × B × C × D × E`, if the function only uses the `A`, `B`, and `C` components,
the expectation equals the expectation over `A × B × C`. -/
theorem uniformExpect_prod5_ignore_de {A B C D E : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] [Fintype E] [Nonempty E]
    (g : A → B → C → ℝ) :
    uniformExpect (A × B × C × D × E)
      (fun r => g r.1 r.2.1 r.2.2.1) =
    uniformExpect (A × B × C)
      (fun r => g r.1 r.2.1 r.2.2) := by
  simp only [uniformExpect_eq, Fintype.card_prod, Nat.cast_mul]
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hD : (Fintype.card D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hE : (Fintype.card E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  simp_rw [← Finset.mul_sum]

/-- Factor out unused components from a product expectation. Given a 5-tuple
`A × B × C × D × E`, if the function only uses the `A`, `D`, and `E` components,
the expectation equals the expectation over `A × D × E`. -/
theorem uniformExpect_prod5_ignore_bc {A B C D E : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] [Fintype E] [Nonempty E]
    (g : A → D → E → ℝ) :
    uniformExpect (A × B × C × D × E)
      (fun r => g r.1 r.2.2.2.1 r.2.2.2.2) =
    uniformExpect (A × D × E)
      (fun r => g r.1 r.2.1 r.2.2) := by
  simp only [uniformExpect_eq, Fintype.card_prod, Nat.cast_mul]
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hB : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  simp_rw [← Finset.mul_sum]

/-- Union bound for indicators: `1{∃ i, P i a} ≤ ∑ i, 1{P i a}`. -/
theorem indicator_exists_le_sum {α : Type*} {n : ℕ}
    (P : Fin n → α → Prop) [∀ i, DecidablePred (P i)] (a : α) :
    (if ∃ i, P i a then (1 : ℝ) else 0) ≤ ∑ i : Fin n, (if P i a then 1 else 0) := by
  by_cases h : ∃ i, P i a
  · simp only [h, ite_true]
    obtain ⟨i, hi⟩ := h
    have h_nonneg : ∀ j : Fin n, j ∈ Finset.univ →
        0 ≤ (if P j a then (1 : ℝ) else 0) :=
      fun j _ => ite_nonneg zero_le_one (le_refl 0)
    have h_le := Finset.single_le_sum h_nonneg (Finset.mem_univ i)
    simp only [hi, ite_true] at h_le
    exact h_le
  · simp only [h, ite_false]
    exact Finset.sum_nonneg fun j _ => ite_nonneg zero_le_one (le_refl 0)

/-- Pull a `Finset.univ` sum out of `uniformExpect`:
`E[∑ s ∈ univ, f s a] = ∑ s ∈ univ, E[f s a]`. -/
theorem uniformExpect_finset_sum {α S : Type*} [Fintype α] [Nonempty α] [Fintype S]
    (f : S → α → ℝ) :
    uniformExpect α (fun a => ∑ s : S, f s a) =
      ∑ s : S, uniformExpect α (f s) := by
  unfold uniformExpect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- For a uniform pair of coordinates from `Fin q → T`, the collision
probability is `1/|T|`. -/
theorem uniformExpect_collision_pair {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T]
    {q : ℕ} (i j : Fin q) (hij : i ≠ j) :
    uniformExpect (Fin q → T)
      (fun ts => if ts i = ts j then (1 : ℝ) else 0) =
    1 / Fintype.card T := by
  -- Split at coordinate i: (Fin q → T) ≃ T × ({k // k ≠ i} → T)
  -- After splitting, ts i = p.1 and ts j = p.2 ⟨j, Ne.symm hij⟩
  have h_comp : (fun ts : Fin q → T => if ts i = ts j then (1 : ℝ) else 0) =
      (fun p : T × ({k : Fin q // k ≠ i} → T) =>
        if p.1 = p.2 ⟨j, Ne.symm hij⟩ then 1 else 0) ∘ Equiv.funSplitAt i T := by
    ext ts; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  rw [h_comp, uniformExpect_congr]
  haveI : Nonempty ({k : Fin q // k ≠ i} → T) := ⟨fun _ => ‹Nonempty T›.some⟩
  rw [uniformExpect_prod]
  -- Goal: E_{ti}[E_{rest}[1{ti = rest ⟨j, ...⟩}]] = 1/|T|
  -- Swap to E_{rest}[E_{ti}[1{ti = rest ⟨j, ...⟩}]] so the inner is over T
  rw [uniformExpect_comm]
  -- Now: E_{rest}[E_{ti}[1{ti = rest ⟨j, ...⟩}]] = 1/|T|
  -- For any c, E_{ti}[1{ti = c}] = 1/|T|
  have h_inner : ∀ c : T,
      uniformExpect T (fun ti => if ti = c then (1 : ℝ) else 0) =
      1 / Fintype.card T := by
    intro c
    rw [uniformExpect_eq, Finset.sum_ite_eq', if_pos (Finset.mem_univ c)]
    simp [one_div]
  simp_rw [h_inner, uniformExpect_const]

/-- **Birthday bound**: for `q` uniform i.i.d. samples from a set of size `|T|`,
the probability that any two collide is at most `q² / |T|`. -/
theorem birthday_bound {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T] (q : ℕ) :
    uniformExpect (Fin q → T)
      (fun ts => if ∃ (i j : Fin q), i < j ∧ ts i = ts j then (1 : ℝ) else 0) ≤
    (q : ℝ) ^ 2 / Fintype.card T := by
  -- Step 1: Union bound — indicator of ∃ ≤ sum of indicators over pairs
  have h_union : ∀ ts : Fin q → T,
      (if ∃ (i j : Fin q), i < j ∧ ts i = ts j then (1 : ℝ) else 0) ≤
      ∑ p : Fin q × Fin q,
        if p.1 < p.2 ∧ ts p.1 = ts p.2 then 1 else 0 := by
    intro ts
    split
    · next h =>
      obtain ⟨i, j, hij, heq⟩ := h
      have h_nonneg : ∀ p : Fin q × Fin q, p ∈ Finset.univ →
          0 ≤ (if p.1 < p.2 ∧ ts p.1 = ts p.2 then (1 : ℝ) else 0) :=
        fun p _ => ite_nonneg zero_le_one (le_refl 0)
      have h_le := Finset.single_le_sum h_nonneg (Finset.mem_univ (i, j))
      simp only [hij, heq, and_self, ite_true] at h_le
      exact h_le
    · exact Finset.sum_nonneg fun p _ => ite_nonneg zero_le_one (le_refl 0)
  -- Step 2: E[∑ pair, ...] = ∑ pair, E[...] by linearity, then bound each pair
  calc uniformExpect (Fin q → T)
        (fun ts => if ∃ (i j : Fin q), i < j ∧ ts i = ts j then (1 : ℝ) else 0)
      ≤ uniformExpect (Fin q → T)
          (fun ts => ∑ p : Fin q × Fin q,
            if p.1 < p.2 ∧ ts p.1 = ts p.2 then 1 else 0) :=
        uniformExpect_mono _ h_union
    _ = ∑ p : Fin q × Fin q, uniformExpect (Fin q → T)
          (fun ts => if p.1 < p.2 ∧ ts p.1 = ts p.2 then 1 else 0) :=
        uniformExpect_finset_sum _
    _ ≤ ∑ _p : Fin q × Fin q, (1 / Fintype.card T : ℝ) := by
        apply Finset.sum_le_sum; intro ⟨i, j⟩ _
        by_cases hij : i < j
        · simp only [hij, true_and]
          exact le_of_eq (uniformExpect_collision_pair i j (ne_of_lt hij))
        · -- When ¬(i < j), the indicator is always 0
          calc uniformExpect (Fin q → T)
                (fun ts => if i < j ∧ ts i = ts j then (1 : ℝ) else 0)
              = uniformExpect (Fin q → T) (fun _ => 0) := by
                congr 1; ext ts; simp [hij]
            _ = 0 := uniformExpect_const _ 0
            _ ≤ 1 / Fintype.card T := by positivity
    _ = (Fintype.card (Fin q × Fin q) : ℝ) * (1 / Fintype.card T) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (q : ℝ) ^ 2 / Fintype.card T := by
        simp [Fintype.card_prod, Fintype.card_fin]; ring_nf; exact le_refl _

end Cslib.Probability

end
