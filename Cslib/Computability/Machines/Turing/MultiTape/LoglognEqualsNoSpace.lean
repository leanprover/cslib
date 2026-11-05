/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.InputShortening
public import Cslib.Foundations.Analysis.Asymptotics
public import Mathlib.Computability.Language

/-!
# Subloglog space equals constant space

A halting deterministic machine whose space usage is `o(log log n)` uses uniformly bounded space.
The proof idea follows [Katz2007], §1.2, Theorem 4. Its main ingredient is formalized in
`Cslib.Computability.Machines.Turing.MultiTape.InputShortening`.

## Main results

* `exists_const_space_of_isLittleO_log_log`: the same machine uses constant space on every input.
* `ComputableInSpace.exists_const_space`: a function computable in subloglog space is computable in
  constant space.
* `DecidableInSpace.exists_const_space`: a language decidable in subloglog space is decidable in
  constant space.
* `loglogn_equals_no_space`: `SPACE(o(log log n)) = SPACE(1)` for binary languages.

## References

* [Jonathan Katz, *Notes on Complexity Theory, Lecture 5*][Katz2007],
  §1.2, Theorem 4, pp. 5-2–5-4.
-/

@[expose] public section

open Filter Asymptotics

namespace Turing.MultiTapeTM

/-- For `s(n) = o(log log n)`, sufficiently long inputs exceed the shortening threshold. -/
private lemma eventually_visit_bound_lt {Symbol State : Type*} [Fintype Symbol] [Fintype State]
    (k : ℕ) {s : ℕ → ℕ}
    (hs : (fun n ↦ (s n : ℝ)) =o[atTop] (fun n ↦ Real.log (Real.log (n : ℝ)))) :
    ∀ᶠ n in atTop, 2 * Fintype.card Symbol *
      (storageBound Symbol State k (s n) + 1) ^ storageBound Symbol State k (s n) + 1 < n := by
  obtain ⟨a, c, hbound⟩ := storageBound_pow_le_pow_pow (Symbol := Symbol) (State := State) (k := k)
    (2 * Fintype.card Symbol)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc : (fun _ : ℕ ↦ (a : ℝ)) =o[atTop] (fun n ↦ Real.log (Real.log (n : ℝ))) :=
    Real.isLittleO_const_log_atTop.comp_tendsto hlog
  have hlin : (fun n ↦ ((a + c * s n : ℕ) : ℝ)) =o[atTop]
      (fun n ↦ Real.log (Real.log (n : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hc.add (hs.const_mul_left (c : ℝ))
  have hsmall : (fun n ↦ ((2 ^ (2 ^ (a + c * s n)) : ℕ) : ℝ)) =o[atTop]
      (fun n ↦ (n : ℝ)) :=
    (hlin.natCast_const_pow hlog (by decide)).natCast_const_pow
      tendsto_natCast_atTop_atTop (by decide)
  have hsmall' := hsmall.add ((isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
    tendsto_natCast_atTop_atTop)
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖(n : ℝ)‖ := by
    simpa using eventually_gt_atTop (0 : ℕ)
  filter_upwards [hsmall'.eventuallyLT_norm_of_eventually_pos hpos] with n hn
  have hn' : 2 ^ (2 ^ (a + c * s n)) + 1 < n := by
    simpa only [Function.comp_apply, ← Nat.cast_add_one, Real.norm_natCast, Nat.cast_lt] using hn
  exact (Nat.add_le_add_right (hbound (s n)) 1).trans_lt hn'

/-- A halting machine whose space usage is `o(log log n)` has a uniform constant space bound.
The bound applies to the same machine on every input. -/
theorem exists_const_space_of_isLittleO_log_log {k : ℕ} {Symbol State : Type*}
    [Finite Symbol] [Finite State] {tm : MultiTapeTM k Symbol State} {s : ℕ → ℕ}
    (hhalt : ∀ input, ∃ p : tm.ComputationPath input, p.last.Halted)
    (hspace : ∀ input, tm.RunsInSpace input (s input.length))
    (hs : (fun n ↦ (s n : ℝ)) =o[atTop] (fun n ↦ Real.log (Real.log (n : ℝ)))) :
    ∃ C : ℕ, ∀ input, tm.RunsInSpace input C := by
  classical
  let : Fintype Symbol := Fintype.ofFinite Symbol
  let : Fintype State := Fintype.ofFinite State
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_visit_bound_lt (Symbol := Symbol) (State := State) k hs)
  let R := (Finset.range N).sup s
  have hhead : ∀ input (p : tm.ComputationPath input) i,
      (p.last.storage.workTapePos i).natAbs ≤ R := by
    intro input
    induction input using (measure List.length).wf.induction with
    | h input ih =>
      intro p i
      by_cases hsmall : input.length < N
      · have hw := MultiTapeNTM.RunPath.inWindow_of_space_le (p := p.toRunPath)
          (fun i ↦ by simp [p.head_eq, Cfg.init]) (hspace input p)
        exact (mem_window.mp (hw _ (RelSeries.last_mem _) i)).trans
          (Finset.le_sup (Finset.mem_range.mpr hsmall))
      obtain ⟨q, hq⟩ := hhalt input
      obtain ⟨input', hshort, p', hstore⟩ := tm.exists_shorter_input_storage
        (hspace input) hq (hN input.length (by omega)) (p.last_mem_of_halted hq)
      rw [← hstore]
      exact ih input' hshort p' i
  refine ⟨k * (2 * R + 1), fun input p ↦ MultiTapeNTM.RunPath.InWindow.space_le ?_⟩
  rintro c ⟨j, rfl⟩ i
  exact mem_window.mpr (hhead input ⟨p.take j, by simpa using p.head_eq⟩ i)

/-- A function computable in subloglog space is computable in constant space. -/
theorem ComputableInSpace.exists_const_space {β : Type*} {f : List Bool → β}
    {encOut : β ↪ List Bool} {s : ℕ → ℕ}
    (h : ComputableInSpace f (.refl _) encOut (fun input ↦ s input.length))
    (hs : (fun n ↦ (s n : ℝ)) =o[atTop] (fun n ↦ Real.log (Real.log (n : ℝ)))) :
    ∃ C : ℕ, ComputableInSpace f (.refl _) encOut (fun _ ↦ C) := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  let : Finite State := hfinite
  have hhalt : ∀ input, ∃ p : tm.ComputationPath input, p.last.Halted := by
    intro input
    obtain ⟨t, ht, _⟩ := (htm input).1
    exact ⟨.ofDeterministic tm input t, ht⟩
  obtain ⟨C, hC⟩ := tm.exists_const_space_of_isLittleO_log_log hhalt (fun input ↦ (htm input).2) hs
  exact ⟨C, k, State, hfinite, tm, fun input ↦ ⟨(htm input).1, hC input⟩⟩

/-- A language decidable in subloglog space is decidable in constant space. -/
theorem DecidableInSpace.exists_const_space {L : Language Bool} {s : ℕ → ℕ}
    (h : DecidableInSpace L (.refl _) (fun input ↦ s input.length))
    (hs : (fun n ↦ (s n : ℝ)) =o[atTop] (fun n ↦ Real.log (Real.log (n : ℝ)))) :
    ∃ C : ℕ, DecidableInSpace L (.refl _) (fun _ ↦ C) :=
  ComputableInSpace.exists_const_space h hs

/-- `SPACE(o(log log n)) = SPACE(1)` for binary languages. -/
theorem loglogn_equals_no_space (L : Language Bool) :
    (∃ s : ℕ → ℕ,
      (fun n ↦ (s n : ℝ)) =o[atTop] (fun n ↦ Real.log (Real.log (n : ℝ))) ∧
      DecidableInSpace L (.refl _) (fun input ↦ s input.length)) ↔
    (∃ C : ℕ, DecidableInSpace L (.refl _) (fun _ ↦ C)) := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact h.exists_const_space hs
  · rintro ⟨C, h⟩
    refine ⟨fun _ ↦ C, ?_, h⟩
    exact Real.isLittleO_const_log_atTop.comp_tendsto
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

end Turing.MultiTapeTM
