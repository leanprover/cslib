/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.FLP.Algorithm

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
  ∃ xs, a.lts.MTr s1 xs s2 ∧ xs.Forall (DestIn ps)

/-- `InpEqOn ps inp1 inp2` means that inputs `inp1` and `inp2` agree on all processes in `ps`. -/
def InpEqOn (ps : Set P) (inp1 inp2 : P → Bool) : Prop :=
  ∀ p, p ∈ ps → inp1 p = inp2 p

namespace CanReachVia

variable {a : Algorithm P M S}

/-- `a.CanReachVia ps s s'` implies `a.lts.CanReach s s'` for any `ps`. -/
theorem canReach {ps : Set P} {s s' : State P M S}
    (h : a.CanReachVia ps s s') : a.lts.CanReach s s' := by
  obtain ⟨xs, h_mtr, _⟩ := h
  use xs

/-- `a.CanReachVia ps s s` is true for any `ps`. -/
theorem refl (ps : Set P) (s : State P M S) :
    a.CanReachVia ps s s := by
  use []
  simp

/-- Extending `CanReachVia` on the left by one step. -/
theorem stepL {ps : Set P} {x : Action P M} {s1 s2 s3 : State P M S}
    (hx : DestIn ps x) (h1 : a.lts.Tr s1 x s2) (h2 : a.CanReachVia ps s2 s3) :
    a.CanReachVia ps s1 s3 := by
  obtain ⟨xs, _, _⟩ := h2
  use (x :: xs)
  grind [LTS.MTr.stepL, List.forall_cons]

private lemma diamond_helper
    {ps : Set P} {x : Action P M} {s s1 s2 : State P M S}
    (hx : DestIn ps x) (h1 : a.lts.Tr s x s1) (h2 : a.CanReachVia psᶜ s s2) :
    ∃ s', a.CanReachVia psᶜ s1 s' ∧ a.lts.Tr s2 x s' := by
  obtain ⟨xs2, h_mtr2, h_via2⟩ := h2
  induction h_mtr2 generalizing s1
  case refl s =>
    use s1
    simp_all [refl]
  case stepL s y t2 ys s2 h_tr2 h_mtr2 h_ind =>
    obtain ⟨h_y, h_ys⟩ := (List.forall_cons (DestIn psᶜ) y ys).mp h_via2
    obtain ⟨t1, h_tr1, h_tr21⟩ := Algorithm.tr_diamond hx h1 h_y h_tr2
    obtain ⟨s', h_crv1, h_tr2'⟩ := h_ind h_tr21 h_ys
    use s', ?_, h_tr2'
    exact stepL h_y h_tr1 h_crv1

/-- A diamond property for `CanReachVia`. This theorem formalizes Proposition 1 of [Volzer2004]. -/
theorem diamond {ps : Set P} {s s1 s2 : State P M S}
    (h1 : a.CanReachVia ps s s1) (h2 : a.CanReachVia psᶜ s s2) :
    ∃ s', a.CanReachVia psᶜ s1 s' ∧ a.CanReachVia ps s2 s' := by
  obtain ⟨xs1, h_mtr1, h_via1⟩ := h1
  induction h_mtr1 generalizing s2
  case refl s =>
    use s2
    simp_all [refl]
  case stepL s x t1 xs s1 h_tr1 h_mtr1 h_ind =>
    obtain ⟨h_x, h_xs⟩ := (List.forall_cons (DestIn ps) x xs).mp h_via1
    obtain ⟨t2, h_crv, h_tr2⟩:= diamond_helper h_x h_tr1 h2
    obtain ⟨s', h_crv1, h_crv2⟩ := h_ind h_crv h_xs
    use s', h_crv1
    exact stepL h_x h_tr2 h_crv2

/-- If inputs `inp1` and `inp2` agree on all processes in `ps` and state `s` is reachable from
the initial state determined by `inp1` by receiving messages with destinations in `ps` only,
then there exists a state `s2` that agrees with `s` on the states of all processes and is
reachable from the initial state determined by `inp2` by receiving messages with destinations
in `ps` only. This theorem is implicitly used in the proof of Lemma 1 of [Volzer2004]. -/
theorem subset_inp [Fintype P] {ps : Set P} {inp1 inp2 : P → Bool} {s1 : State P M S}
    (he : InpEqOn ps inp1 inp2) (hr : a.CanReachVia ps (a.start inp1) s1) :
    ∃ s2, a.CanReachVia ps (a.start inp2) s2 ∧ s2.proc = s1.proc := by
  obtain ⟨xs, h_mtr, h_xs⟩ := hr
  obtain ⟨ss, _, h_ss0, _, _⟩ := LTS.Execution.of_mTr h_mtr
  suffices h_inv : ∀ k, (_ : k ≤ xs.length) →
    ∃ s2, a.lts.MTr (a.start inp2) (xs.take k) s2 ∧ s2.proc = ss[k].proc ∧
      ∀ m, m.dest ∈ ps → s2.msgs.count m = ss[k].msgs.count m by
    obtain ⟨s2, _⟩ := h_inv xs.length (by simp)
    use s2, ?_, by grind
    use xs, by grind
  intro k h_k
  induction k
  case zero =>
    use a.start inp2, by grind [LTS.MTr], by grind [Algorithm.start]
    intro m h_m
    simp only [h_ss0, Algorithm.start, count_map, Message.ext_iff]
    congr
    grind [InpEqOn]
  case succ k h_ind =>
    obtain ⟨s2, h_mtr, h_proc, h_msgs⟩ := h_ind (by grind)
    obtain (_ | ⟨m, h_m⟩) := Option.eq_none_or_eq_some xs[k]
    · use s2, ?_, ?_, ?_
      · have h_tr : a.lts.Tr s2 xs[k] s2 := by grind [Algorithm.lts]
        grind [List.take_add_one, LTS.MTr.stepR (lts := a.lts) h_mtr h_tr]
      · grind [Algorithm.tr_none]
      · grind [Algorithm.tr_none]
    · obtain ⟨_, h_k1⟩ : m ∈ ss[k].msgs ∧ ss[k + 1] = a.recvMsg m ss[k] := by grind [Algorithm.lts]
      use a.recvMsg m s2, ?_, ?_, ?_
      · have := List.forall_mem_iff_forall_getElem.mp <| List.forall_iff_forall_mem.mp h_xs
        have h_tr : a.lts.Tr s2 xs[k] (a.recvMsg m s2) := by
          grind [Algorithm.lts, DestIn, one_le_count_iff_mem]
        grind [List.take_add_one, LTS.MTr.stepR (lts := a.lts) h_mtr h_tr]
      · grind [Algorithm.recvMsg]
      · intro m1 h_m1
        by_cases h1 : m1 = m
        · simp [h_k1, Algorithm.recvMsg, h_proc, h1, count_erase_self]
          grind
        · simp [h_k1, Algorithm.recvMsg, h_proc, count_erase_of_ne h1]
          grind

end CanReachVia

end Cslib.FLP
