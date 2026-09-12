/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.InputShortening
public import Cslib.Foundations.Analysis.Asymptotics

/-!
# Subloglog space equals constant space

A halting deterministic machine whose space usage is `o(log log n)` uses uniformly bounded
space. The proof shortens an input while preserving a chosen storage, using the visit sequences
from `InputShortening` and the storage count from `ConfigBound`. A shortest input witnessing a
large work-head displacement must therefore lie below a fixed length threshold.

`exists_spaceUsed_le_of_isLittleO_log_log` bounds the space of the same machine on all inputs.
`loglogn_equals_no_space` gives `SPACE(o(log log n)) = SPACE(1)` for languages over finite
alphabets, using `DecidableInSpace` with a bound on space by input length.
-/

@[expose] public section

open Filter Asymptotics

namespace Turing.MultiTapeTM

/-- For `s(n) = o(log log n)`, sufficiently long inputs exceed the shortening threshold. -/
private lemma eventually_visit_bound_lt {Symbol State : Type*} [Fintype Symbol] [Fintype State]
    (k : ℕ) {s : ℕ → ℕ}
    (hs : (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log (Real.log (n : ℝ)))) :
    ∀ᶠ n in atTop, 2 * Fintype.card Symbol *
      (storageBound Symbol State k (s n) + 1) ^ storageBound Symbol State k (s n) < n := by
  obtain ⟨a, c, hbound⟩ := storageBound_pow_le_pow_pow (Symbol := Symbol) (State := State) (k := k)
    (2 * Fintype.card Symbol)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc : (fun _ : ℕ => (a : ℝ)) =o[atTop] (fun n => Real.log (Real.log (n : ℝ))) :=
    Real.isLittleO_const_log_atTop.comp_tendsto hlog
  have hlin : (fun n => ((a + c * s n : ℕ) : ℝ)) =o[atTop]
      (fun n => Real.log (Real.log (n : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hc.add (hs.const_mul_left (c : ℝ))
  have hsmall : (fun n => ((2 ^ (2 ^ (a + c * s n)) : ℕ) : ℝ)) =o[atTop]
      (fun n => (n : ℝ)) :=
    (hlin.natCast_const_pow hlog (by decide)).natCast_const_pow
      tendsto_natCast_atTop_atTop (by decide)
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖(n : ℝ)‖ := by
    simpa using eventually_gt_atTop (0 : ℕ)
  filter_upwards [hsmall.eventuallyLT_norm_of_eventually_pos hpos] with n hn
  exact (hbound (s n)).trans_lt (by simpa only [Real.norm_natCast, Nat.cast_lt] using hn)

/-- A halting machine whose space usage is `o(log log n)` has a uniform constant space bound.
The bound applies to the same machine, on every input and at every time. -/
theorem exists_spaceUsed_le_of_isLittleO_log_log {k : ℕ} {Symbol State : Type*}
    [Finite Symbol] [Finite State] {tm : MultiTapeTM k Symbol State} {s : ℕ → ℕ}
    (hhalt : ∀ input : List Symbol, ∃ T, (tm.runFrom (tm.initCfg input) T).Halted)
    (hspace : ∀ (input : List Symbol) t, tm.spaceUsed (tm.initCfg input) t ≤ s input.length)
    (hs : (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log (Real.log (n : ℝ)))) :
    ∃ C : ℕ, ∀ (input : List Symbol) t, tm.spaceUsed (tm.initCfg input) t ≤ C := by
  classical
  let : Fintype Symbol := Fintype.ofFinite Symbol
  let : Fintype State := Fintype.ofFinite State
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_visit_bound_lt (Symbol := Symbol) (State := State) k hs)
  let R := (Finset.range N).sup s
  have hhead : ∀ (input : List Symbol) t i,
      ((tm.runFrom (tm.initCfg input) t).workTapePos i).natAbs ≤ R := by
    by_contra! hex
    let P := fun n => ∃ input : List Symbol, input.length = n ∧
      ∃ t i, R < ((tm.runFrom (tm.initCfg input) t).workTapePos i).natAbs
    have hP : ∃ n, P n := by
      obtain ⟨input, t, i, hi⟩ := hex
      exact ⟨input.length, input, rfl, t, i, hi⟩
    obtain ⟨input, hlen, t, i, hi⟩ := Nat.find_spec hP
    have hlarge : N ≤ input.length := by
      by_contra hn
      have hpos := tm.natAbs_le_spaceUsedByTape_of_mem_visited
        (tm.mem_visitedByTapeHead_self (tm.initCfg input) t i)
      simp only [initCfg, Cfg.init, sub_zero] at hpos
      have hsinput := (hpos.trans (tm.spaceUsedByTape_le_spaceUsed (tm.initCfg input) t i)).trans
        (hspace input t)
      have hsmall : s input.length ≤ R := Finset.le_sup (Finset.mem_range.mpr (by omega))
      exact hi.not_ge (hsinput.trans hsmall)
    obtain ⟨input', hshort, u, hstore⟩ := tm.exists_shorter_input_storage
      (hhalt input) (hspace input) (hN input.length hlarge) t
    have heq := congrArg (fun st => st.workTapePos i) hstore
    change (tm.runFrom (tm.initCfg input') u).workTapePos i =
      (tm.runFrom (tm.initCfg input) t).workTapePos i at heq
    have hi' : R < ((tm.runFrom (tm.initCfg input') u).workTapePos i).natAbs := by
      rwa [heq]
    have hmin := Nat.find_min' hP (show P input'.length from ⟨input', rfl, u, i, hi'⟩)
    omega
  exact ⟨k * (2 * R + 1), fun input t =>
    tm.spaceUsed_le_of_workTapePos_natAbs_le (tm.initCfg input) t R
      (fun u _ i => hhead input u i)⟩

/-- A language decidable in subloglog space is decidable in constant space. -/
theorem DecidableInSpace.exists_const_space {Symbol : Type*} [Finite Symbol]
    {L : Language Symbol} {s : ℕ → ℕ} (h : DecidableInSpace L s)
    (hs : (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log (Real.log (n : ℝ)))) :
    ∃ C : ℕ, DecidableInSpace L (fun _ => C) := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  let : Finite State := hfinite
  have hhalt : ∀ input : List Symbol, ∃ T, (tm.runFrom (tm.initCfg input) T).Halted := by
    intro input
    obtain ⟨T, _, hT, _⟩ := htm input
    exact ⟨T + 1, hT⟩
  have hspace : ∀ (input : List Symbol) t, tm.spaceUsed (tm.initCfg input) t ≤ s input.length := by
    intro input t
    obtain ⟨T, _, hT, hs⟩ := htm input
    exact tm.spaceUsed_le_of_halt hT hs t
  obtain ⟨C, hC⟩ := tm.exists_spaceUsed_le_of_isLittleO_log_log hhalt hspace hs
  refine ⟨C, k, State, hfinite, tm, fun input => ?_⟩
  obtain ⟨T, hdecision, hT, _⟩ := htm input
  exact ⟨T, hdecision, hT, hC input (T + 1)⟩

/-- `SPACE(o(log log n)) = SPACE(1)` for languages over any finite alphabet. -/
theorem loglogn_equals_no_space {Symbol : Type*} [Finite Symbol] (L : Language Symbol) :
    (∃ s : ℕ → ℕ,
      (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log (Real.log (n : ℝ))) ∧
      DecidableInSpace L s) ↔
    (∃ C : ℕ, DecidableInSpace L (fun _ => C)) := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact h.exists_const_space hs
  · rintro ⟨C, h⟩
    refine ⟨fun _ => C, ?_, h⟩
    exact Real.isLittleO_const_log_atTop.comp_tendsto
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

end Turing.MultiTapeTM
