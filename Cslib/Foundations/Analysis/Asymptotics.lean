/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Init
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Asymptotic bounds for exponentials

A natural exponent negligible compared with `log g` gives a power negligible compared with `g`.
This can be applied repeatedly to bound iterated exponentials.
-/

@[expose] public section

open Filter Asymptotics

/-- If `f = o(log g)` and `g` tends to infinity, then `b ^ f = o(g)` for a fixed positive base. -/
lemma Asymptotics.IsLittleO.natCast_const_pow {α : Type*} {l : Filter α}
    {f : α → ℕ} {g : α → ℝ}
    (h : (fun x => (f x : ℝ)) =o[l] (fun x => Real.log (g x)))
    (hg : Tendsto g l atTop) {b : ℕ} (hb : 0 < b) :
    (fun x => ((b ^ f x : ℕ) : ℝ)) =o[l] g := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hexp : (fun x => Real.exp (Real.log b * (f x : ℝ))) =o[l]
      (fun x => Real.exp (Real.log (g x))) := by
    rw [Real.isLittleO_exp_comp_exp_comp]
    exact (IsEquivalent.refl.sub_isLittleO (h.const_mul_left (Real.log b))).symm.tendsto_atTop
      (Real.tendsto_log_atTop.comp hg)
  exact hexp.congr'
    (Eventually.of_forall fun x => by simp [mul_comm, Real.exp_nat_mul, Real.exp_log hb'])
    ((hg.eventually_gt_atTop 0).mono fun x hx => Real.exp_log hx)
