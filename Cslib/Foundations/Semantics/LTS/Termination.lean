/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Relation.Confluence
public import Cslib.Foundations.Semantics.LTS.Relation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Chain

/-!
# Termination of LTS

This module relates global execution bounds, well-founded termination, and acyclicity.
-/

@[expose] public section

namespace Cslib.LTS

universe u v

variable {State : Type u} {Label : Type v} (lts : LTS State Label) (Terminated : State → Prop)

/-- A multistep transition admits a chain of its visited states. -/
private theorem exists_state_chain (h : lts.MTr s1 μs s2) :
    ∃ states : List State,
      (s1 :: states).length = μs.length + 1 ∧
        (s1 :: states).IsChain lts.toRelation := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | @stepL s1 μ s2 μs s3 htr hmtr ih =>
      obtain ⟨states, hlength, hchain⟩ := ih
      exact ⟨s2 :: states, by simp [hlength], .cons_cons ⟨μ, htr⟩ hchain⟩

/-- Bounded LTSs are terminating. -/
theorem Bounded.toTerminating (h : lts.Bounded) : lts.Terminating := by
  constructor
  change WellFounded (fun a b => lts.toRelation b a)
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨f, hf⟩
  change ∀ n, lts.toRelation (f n) (f (n + 1)) at hf
  obtain ⟨bound, hbound⟩ := h.bounded
  have hpaths : ∀ n, ∃ μs, μs.length = n ∧ lts.MTr (f 0) μs (f n) := by
    intro n
    induction n with
    | zero => exact ⟨[], rfl, .refl⟩
    | succ n ih =>
        obtain ⟨μs, hlength, hmtr⟩ := ih
        obtain ⟨μ, htr⟩ := hf n
        exact ⟨μs ++ [μ], by simp [hlength], hmtr.stepR lts htr⟩
  obtain ⟨μs, hlength, hmtr⟩ := hpaths bound
  have := hbound (f 0) μs (f bound) hmtr
  omega

/-- A bounded LTS is available as a terminating LTS through typeclass inference. -/
instance bounded_terminating [lts.Bounded] : lts.Terminating :=
  (inferInstance : lts.Bounded).toTerminating

/-- Terminating LTSs are acyclic. -/
theorem Terminating.toAcyclic (h : lts.Terminating) : lts.Acyclic where
  acyclic := h.terminating.toAcyclic

/-- A terminating LTS is available as an acyclic LTS through typeclass inference. -/
instance terminating_acyclic [lts.Terminating] : lts.Acyclic :=
  (inferInstance : lts.Terminating).toAcyclic

/-- On a finite state space, acyclic LTSs are bounded. -/
theorem Acyclic.toBounded [Finite State] (h : lts.Acyclic) : lts.Bounded := by
  classical
  letI := Fintype.ofFinite State
  refine ⟨Fintype.card State, ?_⟩
  intro s1 μs s2 hmtr
  obtain ⟨states, hlength, hchain⟩ := exists_state_chain lts hmtr
  have htransChain : (s1 :: states).IsChain (Relation.TransGen lts.toRelation) :=
    hchain.imp_of_mem_imp fun _ _ _ _ htr => .single htr
  letI : Std.Irrefl (Relation.TransGen lts.toRelation) := h.acyclic
  have hnodup : (s1 :: states).Nodup := htransChain.pairwise.nodup
  have hcard := hnodup.length_le_card
  omega

/-- On a finite state space, acyclic LTSs are terminating. -/
theorem Acyclic.toTerminating [Finite State] (h : lts.Acyclic) : lts.Terminating :=
  h.toBounded.toTerminating

/-- An LTS is acyclic exactly when it has no nonempty multistep cycle. -/
theorem acyclic_iff_no_nonempty_mTr :
    lts.Acyclic ↔ ¬ ∃ s μs, lts.MTr s μs s ∧ 0 < μs.length := by
  constructor
  · rintro h ⟨s, μs, hmtr, hlength⟩
    exact h.acyclic.irrefl s (hmtr.toTransGen lts (List.ne_nil_of_length_pos hlength))
  · intro h
    refine { acyclic := ⟨fun s hcycle => ?_⟩ }
    obtain ⟨μs, hne, hmtr⟩ := (transGen_toRelation_iff lts).mp hcycle
    exact h ⟨s, μs, hmtr, List.length_pos_of_ne_nil hne⟩

/-- Finite LTSs are bounded. -/
instance finiteLTS_bounded [Finite State] [lts.FiniteLTS] : lts.Bounded :=
  (inferInstance : lts.Acyclic).toBounded

/-- A state 'may terminate' if it can reach a terminated state. The definition of `Terminated`
is a parameter. -/
def MayTerminate (s : State) : Prop := ∃ s', Terminated s' ∧ lts.CanReach s s'

/-- A state 'is stuck' if it is not terminated and cannot go forward. The definition of `Terminated`
is a parameter. -/
def Stuck (s : State) : Prop :=
  ¬Terminated s ∧ ¬∃ μ s', lts.Tr s μ s'

end Cslib.LTS
