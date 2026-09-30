/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.Consistency.Specification
public import Cslib.Foundations.Relation.Basic
public import Mathlib.Data.Set.Finite.Basic

/-! # Consistency hierarchy

We prove a number of results about the various notions of consistency for replicated data types.
In paricular, we prove that:

  Linearizability → SequentialConsistency → CausalConsistency → BasicEventualConsistency

Our proofs follow closely the proof of Proposition 5.1 of [Burckhardt2014].

## References

* [*Principles of Eventual Consistency*][Burckhardt2014]
-/

@[expose] public section

namespace Cslib.DistributedConsistency

open Relation AbstractExecution

variable {Event Operation Value Session : Type*}
  {d : ReplicatedDataType Event Operation Value}
  {a : AbstractExecution Event Operation Value Session}

instance isTrans_ar : IsTrans Event a.ar :=
  ⟨a.ar_strict_total_order.trans⟩

lemma so_iff_se_rb (s : Session) (x y : Event) :
    a.so s x y ↔ a.se x = s ∧ a.se y = s ∧ a.rb x y := by
  simp only [BaseHistory.so, restrict]
  grind

lemma so_le_rb (s : Session) : a.so s ≤ a.rb := by
  intro x y
  simp [so_iff_se_rb]

lemma se_rval_eq_none {s : Session} {x : Event} (h1 : a.se x = s) (h2 : a.rval x = none) :
    {y | a.se y = s} = {y | a.se y = s ∧ a.rb y x } ∪ {x} := by
  ext y
  apply Iff.intro
  · intro h_se
    by_cases x = y
    · grind
    · by_contra h_contra
      suffices a.rb x y by grind [a.rb_rval_ne_none]
      obtain ⟨_, h_tri⟩ := a.so_strict_total_order s
      specialize h_tri x y
      grind [so_iff_se_rb]
  · grind

lemma singleOrder_vis_ar_rval_ne_none (h : a.SingleOrder) (x y : Event) :
    (a.vis x y → a.ar x y) ∧ (a.ar x y → a.rval x ≠ none → a.vis x y) := by
  obtain ⟨_, _, _⟩ := h
  grind

lemma singleOrder_realTime_imp_readMyWrites
    (h1 : a.SingleOrder) (h2 : a.RealTime) : a.ReadMyWrites := by
  rintro s x y h_so
  have h_so_ar : a.so s ≤ a.ar := by grind [RealTime, so_le_rb]
  grind [singleOrder_vis_ar_rval_ne_none, a.rb_rval_ne_none,
    so_le_rb s x y h_so, h_so_ar x y h_so]

theorem linearizability_imp_sequentialConsistency
    (h : a.Linearizability d) : a.SequentialConsistency d := by
  grind [Linearizability, SequentialConsistency, singleOrder_realTime_imp_readMyWrites]

lemma readMyWrites_imp_hb_le_trans_vis
    (h : a.ReadMyWrites) (s : Session) : a.hb s ≤ TransGen a.vis := by
  apply TransGen.mono
  rintro x y (h1 | h2)
  · exact h s x y h1
  · exact h2

lemma singleOrder_readMyWrites_imp_causalArbitration
    (h1 : a.SingleOrder) (h2 : a.ReadMyWrites) : a.CausalArbitration := by
  intro s
  suffices TransGen a.vis ≤ a.ar by grind [readMyWrites_imp_hb_le_trans_vis h2 s]
  have h_ar : TransGen a.ar = a.ar := by exact transGen_eq_self
  rw [← h_ar]
  apply TransGen.mono
  obtain ⟨_, _, _⟩ := h1
  intro _ _ _
  grind

lemma causalVisibility_imp_readMyWrites
    (h : a.CausalVisibility) : a.ReadMyWrites := by
  intro s x y h_so
  exact h s x y <| TransGen.single (Or.inl h_so)

lemma causalVisibility_imp_monotonicReads
    (h : a.CausalVisibility) : a.MonotonicReads := by
  intro s x y z h_vis h_so
  exact h s x z <| TransGen.tail (TransGen.single (Or.inr h_vis)) (Or.inl h_so)

lemma causalVisibility_imp_noCircularCausality
    (h : a.CausalVisibility) : a.NoCircularCausality := by
  intro s
  have : a.hb s ≤ a.vis := by grind [CausalVisibility]
  grind [a.vis_acyclic, acyclic_le]

lemma singleOrder_readMyWrites_imp_causalVisibility
    (h1 : a.SingleOrder) (h2 : a.ReadMyWrites) : a.CausalVisibility := by
  intro s
  suffices TransGen a.vis ≤ a.vis by grind [readMyWrites_imp_hb_le_trans_vis h2 s]
  suffices IsTrans Event a.vis by grind
  obtain ⟨_, _, _⟩ := h1
  grind [IsTrans, isTrans_ar]

lemma singleOrder_imp_eventualVisibility
    (h : a.SingleOrder) : a.EventualVisibility := by
  intro x s
  by_cases a.rval x = none
  · have h_rb : ∀ y, ¬ a.rb x y := by grind [a.rb_rval_ne_none]
    simp [nonVisibleEvents, h_rb]
  · by_cases h_y : ∃ y, a.se y = s ∧ a.rval y = none
    · obtain ⟨y, h_y1, h_y2⟩ := h_y
      have h_ss1 : a.nonVisibleEvents x s ⊆ {z | a.se z = s} := by grind [nonVisibleEvents]
      refine Set.Finite.subset ?_ h_ss1
      simp only [se_rval_eq_none h_y1 h_y2, Set.union_singleton, Set.finite_insert]
      have h_ss2 : {z | a.se z = s ∧ a.rb z y} ⊆ predecessors a.rb y := by simp
      exact Set.Finite.subset (a.rb_pred_finite y) h_ss2
    · simp only [not_exists, not_and] at h_y
      suffices h_ss : a.nonVisibleEvents x s ⊆ predecessors a.vis x by
        exact Set.Finite.subset (a.vis_pred_finite x) h_ss
      rintro y ⟨_, _, _⟩
      have : x ≠ y := by grind [a.rb_strict_order.irrefl]
      have : ¬ a.ar x y := by grind [singleOrder_vis_ar_rval_ne_none]
      have : a.ar y x := by grind [a.ar_strict_total_order.trichotomous]
      grind [singleOrder_vis_ar_rval_ne_none]

theorem sequentialConsistency_imp_causalConsistency
    (h : a.SequentialConsistency d) : a.CausalConsistency d := by
  grind [SequentialConsistency, CausalConsistency, Causality, singleOrder_imp_eventualVisibility,
    singleOrder_readMyWrites_imp_causalArbitration, singleOrder_readMyWrites_imp_causalVisibility]

theorem causalConsistency_imp_basicEventualConsistency
    (h : a.CausalConsistency d) : a.BasicEventualConsistency d := by
  grind [CausalConsistency, BasicEventualConsistency,
    Causality, causalVisibility_imp_noCircularCausality]

end Cslib.DistributedConsistency
