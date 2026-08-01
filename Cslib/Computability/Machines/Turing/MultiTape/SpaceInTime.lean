/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Cslib.Computability.Machines.Turing.MultiTape.Classes

import Mathlib.Tactic.Ring

/-!
# From space bounds to time bounds

A deterministic machine that decides a language in space `s` cannot repeat a configuration before
halting, so the number of steps is bounded by the number of reachable configurations. Combined with
the configuration count of `ConfigBound`, this yields the inclusion
`DSPACE(s) ⊆ DTIME(2^{O(s)})`.

Two forms are provided:

* `space_subset_time_general` makes no assumption on `s` and keeps the input-length factor
  `n`, which counts the read-only input-head positions. This factor is essential in general:
  for `s = O(1)` the class is the regular languages, decided in `Θ(n)` time, so the constant base
  `2 ^ (c * s n)` cannot absorb it.
* `space_subset_time` is the textbook statement `DSPACE(s) ⊆ DTIME(2^{O(s)})`, valid under the
  assumption `s(n) ≥ log n`, under which the input-length factor is absorbed into the exponential.

Both are stated as `DSPACE s ⊆ ⋃ c, DTIME (fun n => ... 2 ^ (c * s n))`: the union over the constant
`c` is exactly the `O` in `2^{O(s)}`.

Two inclusions for specific complexity classes are derived from this:

* `logspace_subset_p` shows `L ⊆ P`
* `pspace_subset_exp` shows `PSPACE ⊆ EXP`

-/

@[expose] public section

open Cslib

namespace Turing.MultiTapeTM

open scoped Classical in
/-- A Turing machine that computes `output` in `t` steps using space at most `σ` already computes
it within `(input.length + 2) * storageBound Symbol State k σ` steps, using no more space. -/
lemma ComputesInTimeAndSpace.truncate
    {Symbol State : Type} [Fintype Symbol] [Fintype State]
    {k : ℕ}
    {tm : MultiTapeTM k Symbol State}
    {input output : List Symbol}
    {t s σ : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s)
    (hσ : s ≤ σ) :
    ∃ t' ≤ (input.length + 2) * storageBound Symbol State k σ,
    ∃ s' ≤ s, tm.ComputesInTimeAndSpace input output t' s' := by
  obtain ⟨hhalt, hout, hspace⟩ := h
  obtain ⟨τ, hτcard, hτle, hτhalt⟩ := exists_halt_le_card_image tm input hhalt
  rw [tm.outputString_eq_of_halt (tm.initCfg input) hτle hτhalt] at hout
  exact ⟨τ, hτcard.trans (card_configs_le t σ (hspace.trans_le hσ)),
    tm.spaceUsed (tm.initCfg input) τ, (spaceUsed_mono tm _ hτle).trans hspace.le,
    hτhalt, hout, rfl⟩

/-- General form of the space-to-time inclusion, making no assumption on `s`. The input-length
factor `n` accounts for the read-only input-head positions and cannot be dropped in general. For
`n = 0` the factor vanishes, so the additive constant of `DTIME` covers that single input (its
bound depends on `s 0`, which is fine since `s` is fixed before the constants are chosen). -/
theorem space_subset_time_general
    {Symbol : Type} [Inhabited Symbol]
    (s : ℕ → ℕ) :
    DSPACE s ⊆ ⋃ c, DTIME (Symbol := Symbol) (fun n => n * 2 ^ (c * s n)) := by
  rintro L ⟨c₁, c₂, tBound, kk, sym, state, emb, tm, hcomp⟩
  obtain ⟨a, c, hSB⟩ := storageBound_le_pow (Symbol := Fin sym) (State := Fin state) kk
  -- The same machine witnesses the time bound; the exponent constant is `c * c₁`, while `c₂`
  -- (the additive space constant) and `a` (from `storageBound_le_pow`) are absorbed into the
  -- multiplicative constant of `DTIME` (via `n + 2 ≤ 3 * n` for `n ≥ 1`); the `n = 0` input is
  -- covered by the additive constant.
  refine Set.mem_iUnion.2 ⟨c * c₁,
    3 * (a * 2 ^ (c * c₂)), 2 * (a * 2 ^ (c * c₂)) * 2 ^ (c * c₁ * s 0),
    fun n => c₁ * s n + c₂, kk, sym, state, emb, tm, fun input => ?_⟩
  set n := input.length with hn
  obtain ⟨t, -, σ, hσ, hcomp'⟩ := hcomp input
  -- Truncate the computation to the configuration-count bound...
  obtain ⟨t', ht', s', hs', hc⟩ := hcomp'.truncate (σ := c₁ * s n + c₂) hσ
  refine ⟨t', ?_, s', hs'.trans hσ, hc⟩
  -- ...and bound the configuration count by the exponential.
  have h1 : t' ≤ (n + 2) * (a * 2 ^ (c * c₂) * 2 ^ (c * c₁ * s n)) := by
    calc t'
        ≤ (n + 2) * storageBound (Fin sym) (Fin state) kk (c₁ * s n + c₂) := by simpa [hn] using ht'
      _ ≤ (n + 2) * (a * 2 ^ (c * (c₁ * s n + c₂))) := by gcongr; exact hSB _
      _ = (n + 2) * (a * 2 ^ (c * c₂) * 2 ^ (c * c₁ * s n)) := by
          rw [show c * (c₁ * s n + c₂) = c * c₂ + c * c₁ * s n by ring, pow_add]; ring
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at h1 ⊢
    calc t' ≤ 2 * (a * 2 ^ (c * c₂) * 2 ^ (c * c₁ * s 0)) := h1
      _ ≤ _ := by simp [mul_assoc]
  · calc t' ≤ (n + 2) * (a * 2 ^ (c * c₂) * 2 ^ (c * c₁ * s n)) := h1
      _ ≤ 3 * n * (a * 2 ^ (c * c₂) * 2 ^ (c * c₁ * s n)) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 3 * (a * 2 ^ (c * c₂)) * (n * 2 ^ (c * c₁ * s n)) := by ring
      _ ≤ _ := Nat.le_add_right _ _

/-- If `log₂ n ≤ m` then `n < 2 ^ (m + 1)`. This is the arithmetic core of the `s ≥ log` hypothesis
used to absorb the input-length factor into the exponential. -/
lemma lt_two_pow_succ_of_log2_le {n m : ℕ} (h : Nat.log2 n ≤ m) : n < 2 ^ (m + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact pow_pos (by norm_num) _
  · rw [← Nat.log2_lt (by omega)]; omega

/-- The textbook space-to-time inclusion `DSPACE(s) ⊆ DTIME(2^{O(s)})`, under the standard
assumption `s(n) ≥ log n`, here expressed as `Nat.log2 n ≤ s n`. It follows from
`space_subset_time_general` by absorbing the input-length factor into the exponential
(`n < 2 ^ (s n + 1)`). -/
theorem space_subset_time
    {Symbol : Type} [Inhabited Symbol] (s : ℕ → ℕ) (hs : s ≥ Nat.log2) :
    DSPACE s ⊆ ⋃ c, DTIME (Symbol := Symbol) (fun n => 2 ^ (c * s n)) := by
  intro L hL
  obtain ⟨c, hc⟩ := Set.mem_iUnion.1 (space_subset_time_general s hL)
  obtain ⟨c₁, c₂, s', hd⟩ := hc
  refine Set.mem_iUnion.2 ⟨c + 1, 2 * c₁, c₂, s', hd.mono_time fun n => ?_⟩
  have hlt : n < 2 ^ (s n + 1) := lt_two_pow_succ_of_log2_le (hs n)
  calc c₁ * (n * 2 ^ (c * s n)) + c₂
      ≤ c₁ * (2 ^ (s n + 1) * 2 ^ (c * s n)) + c₂ := by gcongr
    _ = 2 * c₁ * 2 ^ ((c + 1) * s n) + c₂ := by
        rw [← pow_add, show s n + 1 + c * s n = (c + 1) * s n + 1 by ring, pow_succ]; ring

open Classes

/-- `2 ^ log₂ n ≤ n + 1` for all `n`, including `n = 0` (where both sides are `1`). -/
lemma two_pow_log2_le_succ (n : ℕ) : 2 ^ Nat.log2 n ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (Nat.log2_self_le hn.ne').trans n.le_succ

/-- `(n + 1) ^ c ≤ 2 ^ c * n ^ c + 1` for all `n, c`: the `n = 0` case forces the `+ 1`, while for
`n ≥ 1` it follows from `n + 1 ≤ 2 * n`. -/
lemma succ_pow_le (n c : ℕ) : (n + 1) ^ c ≤ 2 ^ c * n ^ c + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · calc (n + 1) ^ c ≤ (2 * n) ^ c := Nat.pow_le_pow_left (by omega) c
      _ = 2 ^ c * n ^ c := mul_pow ..
      _ ≤ 2 ^ c * n ^ c + 1 := Nat.le_succ _

/-- The inclusion `L ⊆ P`: every log-space decidable language is decidable in polynomial time. -/
theorem logspace_subset_p {Symbol : Type} [Inhabited Symbol] :
    L (Symbol := Symbol) ⊆ P := by
  intro L hL
  obtain ⟨c, hc⟩ := Set.mem_iUnion.1 (space_subset_time Nat.log2 le_rfl hL)
  obtain ⟨c₁, c₂, s, hd⟩ := hc
  refine Set.mem_iUnion.2 ⟨c, c₁ * 2 ^ c, c₁ + c₂, s, hd.mono_time fun n => ?_⟩
  calc c₁ * 2 ^ (c * Nat.log2 n) + c₂
      = c₁ * (2 ^ Nat.log2 n) ^ c + c₂ := by rw [mul_comm c, pow_mul]
    _ ≤ c₁ * (n + 1) ^ c + c₂ :=
        Nat.add_le_add_right (Nat.mul_le_mul_left c₁
          (Nat.pow_le_pow_left (two_pow_log2_le_succ n) c)) c₂
    _ ≤ c₁ * (2 ^ c * n ^ c + 1) + c₂ :=
        Nat.add_le_add_right (Nat.mul_le_mul_left c₁ (succ_pow_le n c)) c₂
    _ = c₁ * 2 ^ c * n ^ c + (c₁ + c₂) := by ring

/-- `n ≤ n ^ k` for all `n` when `k ≥ 1`. -/
lemma Nat.le_self_pow_of_pos {n k : ℕ} (hk : 1 ≤ k) : n ≤ n ^ k := by
  rcases n with _ | n
  · simp
  · calc n + 1 ≤ (n + 1) ^ 1 := by rw [pow_one]
      _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (by omega) hk

/-- `c * n ^ k ≤ n ^ (k + 1) + c ^ (k + 1)` for all `n, c, k`: if `n ≥ c` the first summand alone
dominates, and if `n < c` the second summand alone dominates. -/
lemma mul_pow_le_pow_succ_add (c n k : ℕ) : c * n ^ k ≤ n ^ (k + 1) + c ^ (k + 1) := by
  rcases le_total c n with h | h
  · calc c * n ^ k ≤ n * n ^ k := Nat.mul_le_mul_right _ h
      _ = n ^ (k + 1) := by rw [pow_succ']
      _ ≤ n ^ (k + 1) + c ^ (k + 1) := Nat.le_add_right _ _
  · calc c * n ^ k ≤ c * c ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k)
      _ = c ^ (k + 1) := by rw [pow_succ']
      _ ≤ n ^ (k + 1) + c ^ (k + 1) := Nat.le_add_left _ _

/-- The inclusion `PSPACE ⊆ EXP`. For space bound `n ^ 0 = 1` (constant space), the input-length
factor from `space_subset_time_general` is absorbed via `n ≤ 2 ^ n`. For space bound `n ^ (k + 1)`
(`k ≥ 0`), `space_subset_time` applies since `log₂ n ≤ n ≤ n ^ (k + 1)`, and the exponent
`c * n ^ (k + 1)` is absorbed into `n ^ (k + 2)` via `mul_pow_le_pow_succ_add`. -/
theorem pspace_subset_exp {Symbol : Type} [Inhabited Symbol] :
    PSPACE (Symbol := Symbol) ⊆ EXP := by
  intro L hL
  obtain ⟨k, hLk⟩ := Set.mem_iUnion.1 hL
  rcases k with _ | k
  · -- constant space
    simp only [pow_zero] at hLk
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 (space_subset_time_general (fun _ => 1) hLk)
    obtain ⟨c₁, c₂, s, hd⟩ := hc
    refine Set.mem_iUnion.2 ⟨1, c₁ * 2 ^ c, c₂, s, hd.mono_time fun n => ?_⟩
    calc c₁ * (n * 2 ^ (c * 1)) + c₂
        = c₁ * (n * 2 ^ c) + c₂ := by rw [mul_one]
      _ ≤ c₁ * (2 ^ n * 2 ^ c) + c₂ :=
          Nat.add_le_add_right (Nat.mul_le_mul_left c₁
            (Nat.mul_le_mul_right _ n.lt_two_pow_self.le)) c₂
      _ = c₁ * 2 ^ c * 2 ^ (n ^ 1) + c₂ := by rw [pow_one]; ring
  · -- space bound `n ^ (k + 1)`
    have hlog : Nat.log2 ≤ (fun n => n ^ (k + 1)) :=
      fun n => (Nat.log2_le_self n).trans (Nat.le_self_pow_of_pos (by omega))
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 (space_subset_time (fun n => n ^ (k + 1)) hlog hLk)
    obtain ⟨c₁, c₂, s, hd⟩ := hc
    refine Set.mem_iUnion.2 ⟨k + 2, c₁ * 2 ^ (c ^ (k + 2)), c₂, s, hd.mono_time fun n => ?_⟩
    have key : c * n ^ (k + 1) ≤ n ^ (k + 2) + c ^ (k + 2) := mul_pow_le_pow_succ_add c n (k + 1)
    calc c₁ * 2 ^ (c * n ^ (k + 1)) + c₂
        ≤ c₁ * 2 ^ (n ^ (k + 2) + c ^ (k + 2)) + c₂ :=
          Nat.add_le_add_right (Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_right (by norm_num) key)) c₂
      _ = c₁ * 2 ^ (c ^ (k + 2)) * 2 ^ (n ^ (k + 2)) + c₂ := by rw [pow_add]; ring

end Turing.MultiTapeTM
