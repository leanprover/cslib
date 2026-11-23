/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.FLTS.Basic
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Synchronising traces

This module defines synchronising traces for `FLTS`.

For finite state spaces, `hasSyncTrace_iff_pairwiseHasSyncTrace` characterises synchronisation by
the ability to merge each pair of states, possibly using a different trace for each pair.
The label type need not be finite.

`HasSyncTrace.exists_isSyncTrace_length_le` bounds the length of a shortest synchronising trace of
an `FLTS` with `n` states by `(n - 1) * n.choose 2 = n * (n - 1) ^ 2 / 2`, by greedily merging
pairs of states with traces of length at most `n.choose 2` (`exists_mtr_eq_length_le_choose`).
The Černý conjecture (`cerny_bound`) asserts the much stronger bound `(n - 1) ^ 2`.

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

/-- Every pair of states can be merged by some trace, which may depend on the pair. -/
def PairwiseHasSyncTrace (flts : FLTS State Label) : Prop :=
  ∀ s₁ s₂ : State, ∃ μs : List Label, flts.mtr s₁ μs = flts.mtr s₂ μs

/-- Pairwise merging suffices to merge any finite set of states with one another. -/
private theorem exists_mtr_eq_on_finset (flts : FLTS State Label)
    (h : flts.PairwiseHasSyncTrace) (S : Finset State) :
    ∃ μs, ∀ s₁ ∈ S, ∀ s₂ ∈ S, flts.mtr s₁ μs = flts.mtr s₂ μs := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨[], by simp⟩
  | insert s₂ S hs₂ ih =>
    obtain ⟨μs, hμs⟩ := ih
    rcases S.eq_empty_or_nonempty with (rfl | ⟨s₁, h₁⟩)
    · simp
    · obtain ⟨νs, hνs⟩ := h (flts.mtr s₁ μs) (flts.mtr s₂ μs)
      refine ⟨μs ++ νs, ?_⟩
      simp; grind

/-- A finite-state `FLTS` has a synchronising trace iff every pair of states can be merged
by some trace. This is the pairwise synchronisation criterion of Liu and Černý;
see [Volkov2022], Proposition 2.1. -/
theorem hasSyncTrace_iff_pairwiseHasSyncTrace [Finite State] (flts : FLTS State Label) :
    flts.HasSyncTrace ↔ flts.PairwiseHasSyncTrace := by
  constructor
  · rintro ⟨μs, hμs⟩ s₁ s₂
    exact ⟨μs, hμs s₁ s₂⟩
  · intro h
    obtain ⟨μs, hμs⟩ := flts.exists_mtr_eq_on_finset h Set.finite_univ.toFinset
    use μs
    simpa [IsSyncTrace] using hμs

/-- Two states that can be merged can be merged by a trace of length at most `n.choose 2`, where
`n` is the number of states. Along a shortest merging trace, the unordered pairs of current states
are pairwise distinct (otherwise the trace can be shortened) and never on the diagonal. -/
theorem exists_mtr_eq_length_le_choose [Finite State] (flts : FLTS State Label) {s₁ s₂ : State}
    {μs : List Label} (h : flts.mtr s₁ μs = flts.mtr s₂ μs) :
    ∃ νs : List Label, flts.mtr s₁ νs = flts.mtr s₂ νs ∧
      νs.length ≤ (Nat.card State).choose 2 := by
  classical
  have : Fintype State := Fintype.ofFinite State
  suffices key : ∀ L (μs : List Label), μs.length = L → flts.mtr s₁ μs = flts.mtr s₂ μs →
      ∃ νs : List Label, flts.mtr s₁ νs = flts.mtr s₂ νs ∧
        νs.length ≤ (Nat.card State).choose 2 from key _ μs rfl h
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro μs hL h
  by_cases hle : L ≤ (Nat.card State).choose 2
  · exact ⟨μs, h, hL ▸ hle⟩
  push Not at hle
  -- If a proper prefix already merges the two states, recurse on it.
  by_cases hpre : ∃ i < L, flts.mtr s₁ (μs.take i) = flts.mtr s₂ (μs.take i)
  · obtain ⟨i, hi, hmerge⟩ := hpre
    exact ih i hi _ (by simp [hL, hi.le]) hmerge
  push Not at hpre
  -- Otherwise the `L` pairs of states reached by the prefixes are off-diagonal, so two coincide.
  let f : Fin L → {z : Sym2 State // ¬ z.IsDiag} := fun i =>
    ⟨s(flts.mtr s₁ (μs.take i), flts.mtr s₂ (μs.take i)),
      Sym2.mk_isDiag_iff.not.mpr (hpre i i.isLt)⟩
  have hcard : Fintype.card {z : Sym2 State // ¬ z.IsDiag} < Fintype.card (Fin L) := by
    rwa [Sym2.card_subtype_not_diag, Fintype.card_fin, ← Nat.card_eq_fintype_card]
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hfij.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  -- Cutting out the segment between the two prefixes gives a shorter merging trace.
  have hj : (j : ℕ) ≤ μs.length := hL ▸ j.isLt.le
  have hsplit := h
  rw [← List.take_append_drop j μs, mtr_append_eq, mtr_append_eq] at hsplit
  have hpair := Sym2.eq_iff.mp (congrArg Subtype.val hfij)
  refine ih (i + (L - j)) (by omega) (μs.take i ++ μs.drop j) ?_ ?_
  · simp only [List.length_append, List.length_take, List.length_drop, hL]
    omega
  · rw [mtr_append_eq, mtr_append_eq]
    rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]; exact hsplit
    · rw [h₁, h₂]; exact hsplit.symm

/-- Pairwise merging with short traces merges a finite set `S` of states with a trace of length
at most `(S.card - 1) * n.choose 2`, where `n` is the number of states. -/
private theorem exists_mtr_eq_on_finset_length_le [Finite State] (flts : FLTS State Label)
    (h : flts.PairwiseHasSyncTrace) (S : Finset State) :
    ∃ μs, (∀ s₁ ∈ S, ∀ s₂ ∈ S, flts.mtr s₁ μs = flts.mtr s₂ μs) ∧
      μs.length ≤ (S.card - 1) * (Nat.card State).choose 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp⟩
  | insert s₂ S hs₂ ih =>
    obtain ⟨μs, hμs, hlen⟩ := ih
    rcases S.eq_empty_or_nonempty with (rfl | ⟨s₁, h₁⟩)
    · exact ⟨[], by simp, by simp⟩
    · obtain ⟨νs₀, hνs₀⟩ := h (flts.mtr s₁ μs) (flts.mtr s₂ μs)
      obtain ⟨νs, hνs, hνlen⟩ := flts.exists_mtr_eq_length_le_choose hνs₀
      refine ⟨μs ++ νs, ?_, ?_⟩
      · simp only [Finset.mem_insert, mtr_append_eq]
        grind
      · have hS : S.card = (S.card - 1) + 1 :=
          (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨s₁, h₁⟩)).symm
        rw [List.length_append, Finset.card_insert_of_notMem hs₂, Nat.add_sub_cancel, hS,
          Nat.add_one_mul]
        exact Nat.add_le_add hlen hνlen

/-- A synchronising `FLTS` with `n` states has a synchronising trace of length at most
`(n - 1) * n.choose 2`, that is, `n * (n - 1) ^ 2 / 2`. This cubic bound comes from greedily merging
pairs of states (`exists_mtr_eq_length_le_choose`); compare the Černý conjecture `cerny_bound`. -/
theorem HasSyncTrace.exists_isSyncTrace_length_le [Finite State] {flts : FLTS State Label}
    (h : flts.HasSyncTrace) :
    ∃ μs, flts.IsSyncTrace μs ∧ μs.length ≤ (Nat.card State - 1) * (Nat.card State).choose 2 := by
  classical
  have : Fintype State := Fintype.ofFinite State
  obtain ⟨μs, hμs, hlen⟩ := flts.exists_mtr_eq_on_finset_length_le
    ((hasSyncTrace_iff_pairwiseHasSyncTrace flts).mp h) Finset.univ
  refine ⟨μs, fun s₁ s₂ => hμs s₁ (Finset.mem_univ _) s₂ (Finset.mem_univ _), ?_⟩
  rwa [Finset.card_univ, ← Nat.card_eq_fintype_card] at hlen

/-- Černý conjecture: for any synchronising `FLTS` with `n` states, there exists a synchronising
trace of length at most `(n-1)^2`. -/
proof_wanted cerny_bound [Finite State] (flts : FLTS State Label) (h : flts.HasSyncTrace) :
    ∃ μs, flts.IsSyncTrace μs ∧ μs.length ≤ (Nat.card State - 1) ^ 2

end Cslib.FLTS
