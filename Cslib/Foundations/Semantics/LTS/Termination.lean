/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Relation.Confluence
public import Cslib.Foundations.Semantics.LTS.Execution
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Chain
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Termination of LTS

This module relates global execution bounds, well-founded termination, and acyclicity.
-/

@[expose] public section

namespace Cslib.LTS

universe u v

variable {State : Type u} {Label : Type v} (lts : LTS State Label) (Terminated : State → Prop)

/-- Bounded LTSs are terminating. -/
theorem Bounded.toTerminating (h : lts.Bounded) : lts.Terminating := by
  constructor
  rw [Relation.Terminating.iff_isEmpty_chain]
  constructor
  rintro ⟨f, hf⟩
  change ∀ n, lts.UnlabelledTr (f n) (f (n + 1)) at hf
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

/-- On a finite state space, an acyclic LTS has execution length strictly less than the number of
states. -/
theorem Acyclic.toBoundedUpTo [Finite State] (h : lts.Acyclic) :
    lts.BoundedUpTo (Nat.card State) := by
  classical
  let := Fintype.ofFinite State
  rw [Nat.card_eq_fintype_card]
  intro s1 μs s2 hmtr
  obtain ⟨states, hexec⟩ := Execution.of_mTr hmtr
  have hchain : states.IsChain (Relation.TransGen lts.UnlabelledTr) :=
    hexec.isChain.imp_of_mem_imp fun _ _ _ _ htr => .single htr
  let : Std.Irrefl (Relation.TransGen lts.UnlabelledTr) := h.acyclic
  have hcard := hchain.pairwise.nodup.length_le_card
  grind [Execution]

/-- On a finite state space, acyclic LTSs are bounded. -/
theorem Acyclic.toBounded [Finite State] (h : lts.Acyclic) : lts.Bounded :=
  ⟨Nat.card State, h.toBoundedUpTo⟩

/-- On a finite state space, acyclic LTSs are terminating. -/
theorem Acyclic.toTerminating [Finite State] (h : lts.Acyclic) : lts.Terminating :=
  h.toBounded.toTerminating

/-- A state 'may terminate' if it can reach a terminated state. The definition of `Terminated`
is a parameter. -/
def MayTerminate (s : State) : Prop := ∃ s', Terminated s' ∧ lts.CanReach s s'

/-- A state 'is stuck' if it is not terminated and cannot go forward. The definition of `Terminated`
is a parameter. -/
def Stuck (s : State) : Prop :=
  ¬Terminated s ∧ ¬∃ μ s', lts.Tr s μ s'

end Cslib.LTS
