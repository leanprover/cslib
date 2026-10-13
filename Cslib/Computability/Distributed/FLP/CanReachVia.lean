/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.FLP.Algorithm
public import Cslib.Foundations.Relation.Confluence

/-! # Reachability via a subset of processes

This file develops a theory of reachability via a subset of processes, that is, what happens
when only a subset of processes can receive messages and take steps.  It culminates with two
"diamond properties" of this more refined reachability relation.

## References

* [Volzer2004] H. Völzer, A constructive proof for FLP.
  Information Processing Letters 92(2), (October 2004) 83–87.
-/

@[expose] public section

namespace Cslib.FLP

open Function Set Sum Multiset

variable {P M S : Type*} [DecidableEq P] [DecidableEq M]

/-- `a.CanReachVia ps s1 s2` means that state `s2` is reachable from state `s1` via a finite
execution of algorithm `a` in which all messages received have destinations in `ps`. -/
def Algorithm.CanReachVia (a : Algorithm P M S) (ps : Set P) (s1 s2 : State P M S) : Prop :=
  Relation.ReflTransGen (fun s t ↦ ∃ x, DestIn ps x ∧ a.lts.Tr s x t) s1 s2

namespace CanReachVia

variable {a : Algorithm P M S}

/-- Restricted reachability is witnessed by a finite trace whose destinations lie in `ps`. -/
theorem iff_exists_mTr {ps : Set P} {s s' : State P M S} :
    a.CanReachVia ps s s' ↔ ∃ xs, a.lts.MTr s xs s' ∧ xs.Forall (DestIn ps) := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], .refl, by simp⟩
    | head h _ ih =>
      obtain ⟨x, hx, htr⟩ := h
      obtain ⟨xs, hmtr, hxs⟩ := ih
      exact ⟨x :: xs, hmtr.stepL htr, (List.forall_cons _ _ _).mpr ⟨hx, hxs⟩⟩
  · rintro ⟨xs, hmtr, hxs⟩
    induction hmtr with
    | refl => exact .refl
    | stepL htr _ ih =>
      obtain ⟨hx, hxs⟩ := (List.forall_cons _ _ _).mp hxs
      exact (ih hxs).head ⟨_, hx, htr⟩

/-- `a.CanReachVia ps s s'` implies `a.lts.CanReach s s'` for any `ps`. -/
theorem canReach {ps : Set P} {s s' : State P M S}
    (h : a.CanReachVia ps s s') : a.lts.CanReach s s' := by
  obtain ⟨xs, hmtr, _⟩ := iff_exists_mTr.mp h
  exact ⟨xs, hmtr⟩

/-- `a.CanReachVia ps s s` is true for any `ps`. -/
theorem refl (ps : Set P) (s : State P M S) :
    a.CanReachVia ps s s := .refl

/-- Extending `CanReachVia` on the left by one step. -/
theorem stepL {ps : Set P} {x : Action P M} {s1 s2 s3 : State P M S}
    (hx : DestIn ps x) (h1 : a.lts.Tr s1 x s2) (h2 : a.CanReachVia ps s2 s3) :
    a.CanReachVia ps s1 s3 := h2.head ⟨x, hx, h1⟩

/-- A diamond property for `CanReachVia`. This theorem formalizes Proposition 1 of [Volzer2004]. -/
theorem diamond {ps : Set P} {s s1 s2 : State P M S}
    (h1 : a.CanReachVia ps s s1) (h2 : a.CanReachVia psᶜ s s2) :
    ∃ s', a.CanReachVia psᶜ s1 s' ∧ a.CanReachVia ps s2 s' := by
  refine Relation.DiamondCommute.to_commute ?_ h1 h2
  rintro _ _ _ ⟨x, hx, htr⟩ ⟨y, hy, htr'⟩
  obtain ⟨t, ht, ht'⟩ := Algorithm.tr_diamond hx htr hy htr'
  exact ⟨t, ⟨y, hy, ht⟩, ⟨x, hx, ht'⟩⟩

/-- If inputs `inp1` and `inp2` agree on all processes in `ps` and state `s` is reachable from
the initial state determined by `inp1` by receiving messages with destinations in `ps` only,
then there exists a state `s2` that agrees with `s` on the states of all processes and is
reachable from the initial state determined by `inp2` by receiving messages with destinations
in `ps` only. This theorem is implicitly used in the proof of Lemma 1 of [Volzer2004]. -/
theorem subset_inp [Fintype P] {ps : Set P} {inp1 inp2 : P → Bool} {s1 : State P M S}
    (he : EqOn inp1 inp2 ps) (hr : a.CanReachVia ps (a.start inp1) s1) :
    ∃ s2, a.CanReachVia ps (a.start inp2) s2 ∧ s2.proc = s1.proc := by
  suffices ∃ s2, a.CanReachVia ps (a.start inp2) s2 ∧ s2.proc = s1.proc ∧
      ∀ m, m.dest ∈ ps → s2.msgs.count m = s1.msgs.count m by
    obtain ⟨s2, hr, hp, _⟩ := this
    exact ⟨s2, hr, hp⟩
  induction hr with
  | refl =>
    refine ⟨a.start inp2, .refl, rfl, ?_⟩
    intro m h_m
    simp only [Algorithm.start, count_map, Message.ext_iff]
    congr
    grind [EqOn]
  | tail _ htr ih =>
    obtain ⟨s2, hr, h_proc, h_msgs⟩ := ih
    obtain ⟨x, hx, htr⟩ := htr
    cases x with
    | none =>
      obtain rfl := Algorithm.tr_none htr
      exact ⟨s2, hr, h_proc, h_msgs⟩
    | some m =>
      obtain ⟨hm, rfl⟩ := htr
      refine ⟨a.recvMsg m s2, hr.tail ⟨some m, hx, ?_⟩, ?_, ?_⟩
      · exact ⟨by grind [DestIn, one_le_count_iff_mem], rfl⟩
      · simp [Algorithm.recvMsg, h_proc]
      · intro m1 h_m1
        by_cases h1 : m1 = m
        · simp [Algorithm.recvMsg, h_proc, h1, count_erase_self]
          grind
        · simp [Algorithm.recvMsg, h_proc, count_erase_of_ne h1]
          grind

end CanReachVia

end Cslib.FLP
