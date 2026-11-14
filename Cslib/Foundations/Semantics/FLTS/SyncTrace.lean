/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.FLTS.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Synchronising traces

This module defines synchronising traces for `FLTS`.

For finite state spaces, `hasSyncTrace_iff_pairwise` characterises synchronisation by the
ability to merge each pair of states, possibly using a different trace for each pair.
The label type need not be finite.

## References

* [M. V. Volkov, *Synchronization of finite automata*][Volkov2022], Proposition 2.1.
-/

@[expose] public section

namespace Cslib.FLTS

variable {State Label : Type*}

/-- A trace `μs` is synchronising if following it from any two states leads to the same state. -/
def IsSyncTrace (flts : FLTS State Label) (μs : List Label) : Prop :=
  ∀ s₁ s₂ : State, flts.mtr s₁ μs = flts.mtr s₂ μs

/-- `flts` is synchronising, i.e., it has at least one synchronising trace. -/
def HasSyncTrace (flts : FLTS State Label) : Prop :=
  ∃ μs : List Label, flts.IsSyncTrace μs

/-- Pairwise merging suffices to merge any finite set of states with a reference state. -/
private theorem exists_mtr_eq_on_finset (flts : FLTS State Label)
    (h : ∀ s₁ s₂, ∃ μs, flts.mtr s₁ μs = flts.mtr s₂ μs) (s₁ : State) (S : Finset State) :
    ∃ μs, ∀ s₂ ∈ S, flts.mtr s₂ μs = flts.mtr s₁ μs := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨[], by simp⟩
  | insert s₂ S hs₂ ih =>
    obtain ⟨μs, hμs⟩ := ih
    obtain ⟨νs, hνs⟩ := h (flts.mtr s₂ μs) (flts.mtr s₁ μs)
    refine ⟨μs ++ νs, ?_⟩
    grind

/-- A finite-state `FLTS` has a synchronising trace iff every pair of states can be merged
by some trace. This is the pairwise synchronisation criterion of Liu and Černý;
see [Volkov2022], Proposition 2.1. -/
theorem hasSyncTrace_iff_pairwise [Finite State] (flts : FLTS State Label) :
    flts.HasSyncTrace ↔ ∀ s₁ s₂, ∃ μs, flts.mtr s₁ μs = flts.mtr s₂ μs := by
  classical
  constructor
  · rintro ⟨μs, hμs⟩ s₁ s₂
    exact ⟨μs, hμs s₁ s₂⟩
  · intro h
    cases isEmpty_or_nonempty State with
    | inl he => exact ⟨[], fun s₁ => isEmptyElim s₁⟩
    | inr he =>
      let := Fintype.ofFinite State
      obtain ⟨s₁⟩ := he
      obtain ⟨μs, hμs⟩ := exists_mtr_eq_on_finset flts h s₁ Finset.univ
      exact ⟨μs, fun s₂ s₃ => (hμs s₂ (Finset.mem_univ s₂)).trans
        (hμs s₃ (Finset.mem_univ s₃)).symm⟩

/-- Černý conjecture: for any synchronising `FLTS` with `n` states, there exists a synchronising
trace of length at most `(n-1)^2`. -/
proof_wanted cerny_bound [Finite State] (flts : FLTS State Label) (h : flts.HasSyncTrace) :
    ∃ μs, flts.IsSyncTrace μs ∧ μs.length ≤ (Nat.card State - 1) ^ 2

end Cslib.FLTS
