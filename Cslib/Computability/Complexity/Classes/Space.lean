/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Complexity.Classes.Time

@[expose] public section

/-!
# Space Complexity Classes

This file defines space-bounded computation and the complexity class **PSPACE**.

## Main Definitions

* `OutputsWithinSpace` — TM outputs on input using at most `s` additional work cells
* `SpaceBoundedComputable f s` — `f` is computable within space `s`
* `PSPACE` — languages decidable in polynomial space

## Main Results

* `P_subset_PSPACE` — P ⊆ PSPACE

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

open Turing SingleTapeTM Polynomial Relation

variable {Symbol : Type}

namespace Cslib.Complexity

/-- The work space used by a configuration on input `l`: total tape space
minus the initial input footprint `max 1 l.length`. -/
def Cfg.work_space_used (tm : SingleTapeTM Symbol) (l : List Symbol) (cfg : tm.Cfg) : ℕ :=
  SingleTapeTM.Cfg.space_used tm cfg - max 1 l.length

/-- A TM `tm` **outputs** `l'` on input `l` using at most `s` additional work cells
throughout the computation. This combines the time-based reachability
with a space bound: every configuration along the computation path
uses at most `s` work space beyond the initial input footprint. -/
def OutputsWithinSpace (tm : SingleTapeTM Symbol)
    (l l' : List Symbol) (s : ℕ) : Prop :=
  ∃ t : ℕ, tm.OutputsWithinTime l l' t ∧
    ∀ cfg : tm.Cfg,
      ReflTransGen tm.TransitionRelation (tm.initCfg l) cfg →
      Cfg.work_space_used tm l cfg ≤ s

/-- A function `f` is **space-bounded computable** with space bound `s`
if there exists a TM computing `f` that uses at most `s(|x|)` additional
work cells on input `x`. -/
structure SpaceBoundedComputable
    (f : List Symbol → List Symbol) (s : ℕ → ℕ) where
  /-- The underlying Turing machine -/
  tm : SingleTapeTM Symbol
  /-- Proof that the machine computes `f` within space `s` -/
  outputsInSpace : ∀ a,
    OutputsWithinSpace tm a (f a) (s a.length)

/-- **PSPACE** is the class of languages decidable by a Turing machine
using polynomial work space. -/
def PSPACE : Set (Set (List Symbol)) :=
  { L | ∃ f : List Symbol → List Symbol,
    ∃ p : Polynomial ℕ,
    Nonempty (SpaceBoundedComputable f (fun n => p.eval n)) ∧
    Decides f L }

-- TODO: Define L (LOGSPACE) using multi-tape Turing machines with a
-- read-only input tape. The single-tape model allows overwriting input
-- cells, giving O(n) writable space instead of O(log n).

/-- Any configuration reachable during a halting computation has its space
bounded by the initial space plus the halting time. -/
private lemma space_bounded_of_time_bounded (tm : SingleTapeTM Symbol)
    (l l' : List Symbol) (t : ℕ)
    (htime : tm.OutputsWithinTime l l' t)
    (cfg : tm.Cfg)
    (hreach : ReflTransGen tm.TransitionRelation (tm.initCfg l) cfg) :
    Cfg.space_used tm cfg ≤ max 1 l.length + t := by
  -- Convert ReflTransGen to RelatesInSteps.
  obtain ⟨m, hm⟩ := ReflTransGen.relatesInSteps hreach
  -- Extract the halting computation.
  obtain ⟨t', ht'_le, ht'⟩ := htime
  -- `haltCfg` has no successors.
  have hhalt : ∀ cfg', ¬tm.TransitionRelation (tm.haltCfg l') cfg' :=
    fun cfg' => no_step_from_halt tm _ cfg' rfl
  -- By determinism, m ≤ t' ≤ t.
  have hm_le := reachable_steps_le_halting_steps tm ht' hhalt hm
  -- Space grows by at most 1 per step.
  have hspace := RelatesInSteps.apply_le_apply_add hm (Cfg.space_used tm)
    fun a b hstep => Cfg.space_used_step a b (Option.mem_def.mp hstep)
  rw [Cfg.space_used_initCfg] at hspace
  omega

/-- Any configuration reachable during a halting computation uses at most `t`
work cells beyond the initial input footprint. -/
private lemma work_space_bounded_of_time_bounded (tm : SingleTapeTM Symbol)
    (l l' : List Symbol) (t : ℕ)
    (htime : tm.OutputsWithinTime l l' t)
    (cfg : tm.Cfg)
    (hreach : ReflTransGen tm.TransitionRelation (tm.initCfg l) cfg) :
    Cfg.work_space_used tm l cfg ≤ t := by
  have htotal := space_bounded_of_time_bounded tm l l' t htime cfg hreach
  apply (Nat.sub_le_iff_le_add).2
  simpa [Cfg.work_space_used, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using htotal

/-- **P ⊆ PSPACE**: every language decidable in polynomial time is also
decidable in polynomial space.

A TM running in time `t` can use at most `t` additional work cells
beyond the initial input footprint (at most one new cell per step).
So a polynomial time bound gives a polynomial work-space bound. -/
public theorem P_subset_PSPACE :
    P (Symbol := Symbol) ⊆ PSPACE := by
  intro L ⟨f, ⟨hf⟩, hDecides⟩
  refine ⟨f, hf.poly, ⟨{
    tm := hf.tm
    outputsInSpace := fun a =>
      ⟨hf.time_bound a.length, hf.outputsFunInTime a, fun cfg hreach =>
        le_trans
          (work_space_bounded_of_time_bounded hf.tm a (f a) (hf.time_bound a.length)
            (hf.outputsFunInTime a) cfg hreach)
          (hf.bounds a.length)⟩
  }⟩, hDecides⟩

end Cslib.Complexity
