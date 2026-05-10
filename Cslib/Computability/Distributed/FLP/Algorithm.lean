/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-! # Distributed algorithms for solving the consensus problem

In the consensus problem, each process of a distributed algorithm is given a boolean value
at the beginning.  Then by exchanging messages asynchronously, they are supposed to agree on
one of the initial boolean values. This file contains a very general definition of such
a distributed algorithm.

Borrowing an idea from Leslie Lamport, we allow the LTS defined by such an algorithm to
"stutter" at any time, in the sense of taking a dummy step without changing the
global state of the distributed algorithm.  This idea enables us to focus on infinite
executions alone without loss of generality, because an algorithm that has run out of
useful steps to take can always take the stuttering step.  Pathological executions in which
the stuttering step is taken forever when there is useful work to be done are outlawed by
the fairness assumptions defined in `Consensus.lean`.

The types `P`, `M`, and `S` below are the types of processes (more precisely, process identifiers),
messages contents, and process states.  Eventually `P` will be assumed to be finite in the form of
`[Fintype P]`, but that assumption will be added only where necessary.  No assumption whatsoever
will be made about `M` and `S`.  In particular, they could be infinite.
-/

@[expose] public section

namespace Cslib.FLP

open Function Set Sum Multiset

variable {P M S : Type*} [DecidableEq P] [DecidableEq M]

/-- The type of messages that processes send to each other. -/
@[ext]
structure Message (P M : Type*) where
  /-- The destination of a message. -/
  dest : P
  /-- The content of the message, where the `Bool` option is used to carry to the
      initial boolean value to each process. -/
  msg : Bool ⊕ M
deriving DecidableEq

/-- The type of a process's local state. -/
structure ProcState (S : Type*) where
  /-- The internal state of a process. -/
  state : S
  /-- The state component used by a process to signal the boolean value it decides on. -/
  out : Option Bool

/-- The global state of the distributed algorithm. -/
structure State (P M S : Type*) where
  /-- A multiset containing all messages that are in-flight (namely, they have been sent but
  not yet received. Note that being a multiset implies that the messages are not ordered. -/
  msgs : Multiset (Message P M)
  /-- A map giving the local states of all processes. -/
  proc : P → ProcState S

/-- The specification of a distributed algorithm for solving the consensus problem.
Note that each field below can depend on a process's identifier (recall that each `Message`
contains its destination's identifier), so the algorithm is not required to be uniform
across processes. -/
structure Algorithm (P M S : Type*) where
  /-- A map specifying the initial state of each process. -/
  init : P → S
  /-- A map specifying how a process changes its internal state upon receiving a message. -/
  next : Message P M → ProcState S → S
  /-- A map specifying what messages a process sends out upon receiving a message. -/
  send : Message P M → ProcState S → Multiset (Message P M)
  /-- A map specifying the boolean decision a process makes upon receiving a message,
      where `none` means that no decision is made. -/
  out : Message P M → ProcState S → Option Bool

/-- The type of labels of the LTS defined by an `Algorithm`, where `some m` denotes
the reception of message `m` and `none` denotes a stuttering step. -/
abbrev Action (P M : Type*) := Option (Message P M)

/-- `Dest ps x` means that if `x ≠ none`, then `x = some m` with `m.dest ∈ ps`. -/
def DestIn (ps : Set P) : Action P M → Prop
  | some m => m.dest ∈ ps
  | none => True

/-- Given `inp : P → Bool`, the initial state of the algorithm `a` contains a single message
carrying the boolean value `inp p` to each process `p`, where the initial internal state is
`a.init p` and no decision has been made.  The assumption `[Fintyep P]` is made because
a multiset may contain only finitely many elements. -/
def Algorithm.start [Fintype P] (a : Algorithm P M S) (inp : P → Bool) : State P M S where
  msgs := Multiset.map (fun p ↦ ⟨p, inl (inp p)⟩) Finset.univ.val
  proc := fun p ↦ ⟨a.init p, none⟩

/-- The specification of how the global state of the algorithm is changed when one of its
processes `p` receives a message `m`.  Note that once `p` has made a boolean decision in
its `out` field, it is not allowed to "change its mind" later. -/
def Algorithm.recvMsg (a : Algorithm P M S) (m : Message P M) (s : State P M S) : State P M S :=
  let p := m.dest
  { msgs := s.msgs.erase m + a.send m (s.proc p)
    proc := fun q ↦
      if q = p then
        ⟨ a.next m (s.proc p),
          if (s.proc p).out.isNone then a.out m (s.proc p) else (s.proc p).out ⟩
      else s.proc q }

/-- The transition relation of the LTS defined by the algorithm `a`.
Note that the stuttering step is always allowed. -/
def Algorithm.LTS (a : Algorithm P M S) : LTS (State P M S) (Action P M) where
  Tr s x s' := match x with
    | some m => m ∈ s.msgs ∧ s' = a.recvMsg m s
    | none => s' = s

/-- `a.Reachable inp s` means that `s` is a reachable state of `a` given the initial `inp`. -/
def Algorithm.Reachable [Fintype P]
    (a : Algorithm P M S) (inp : P → Bool) (s : State P M S) : Prop :=
  a.LTS.CanReach (a.start inp) s

/-- `s.ProcDecided p b` means that process `p` is decided on the boolean value `b`
in the state `s`. -/
abbrev State.ProcDecided (s : State P M S) (p : P) (b : Bool) : Prop :=
  (s.proc p).out = some b

/-- `s.Decided b` means that at least one process is decided on the boolean value `b`
in the state `s`. -/
def State.Decided (s : State P M S) (b : Bool) : Prop :=
  ∃ p, s.ProcDecided p b

/-- `s.Agreed` says that all boolean values decided on in state `s` must agree with each other. -/
def State.Agreed (s : State P M S) : Prop :=
  ∀ b b', s.Decided b ∧ s.Decided b' → b = b'

/-- `a.SafeConsensus` says that in any reachable state of `a`, (1) all boolean values decided on
in that state must agree with each other and (2) that boolean value (if it exists) must be
one of the boolean values given by `inp` at the beginning.  `a.SafeConsensus` is the minimal
correctness requirement on `a` and is a safety property (hence its name). -/
def Algorithm.SafeConsensus [Fintype P] (a : Algorithm P M S) : Prop :=
  ∀ inp s, a.Reachable inp s → s.Agreed ∧ ∀ b, s.Decided b → ∃ p, inp p = b

namespace Algorithm

variable {a : Algorithm P M S} {inp : P → Bool}

/-- The stuttering step does not change the global state. -/
theorem tr_none {s s' : State P M S} (h : a.LTS.Tr s none s') : s = s' := by
  grind [Algorithm.LTS]

/-- The initial state is reachable. -/
theorem reachable_start [Fintype P] :
    a.Reachable inp (a.start inp) := by
  simp [Algorithm.Reachable, LTS.CanReach.refl]

/-- If `s` is reachable from the initial state and `s'` is reachable from `s`,
then `s'` is reachable from the initial state. -/
theorem reachable_stable [Fintype P] {s s' : State P M S}
    (hr : a.Reachable inp s) (hc : a.LTS.CanReach s s') : a.Reachable inp s' := by
  obtain ⟨xs, _⟩ := hr
  obtain ⟨xs', _⟩ := hc
  use xs ++ xs'
  grind [LTS.MTr.comp]

/-- If `p` is decided on the boolean value `b` in `s` and `s'` is reachable from `s`,
then `p` is still decided on `b` in `s'`. -/
theorem procDecided_stable {s s' : State P M S} {p : P} {b : Bool}
    (hd : s.ProcDecided p b) (hc : a.LTS.CanReach s s') : s'.ProcDecided p b := by
  obtain ⟨xs, h_mtr⟩ := hc
  induction h_mtr <;> grind [Algorithm.LTS, Algorithm.recvMsg]

/-- If at least one process is decided on the boolean value `b` in `s` and `s'` is reachable
from `s`, then at least one process is still decided on `b` in `s'`. -/
theorem decided_stable {s s' : State P M S} {b : Bool}
    (hd : s.Decided b) (hc : a.LTS.CanReach s s') : s'.Decided b := by
  obtain ⟨p, _⟩ := hd
  use p
  grind [procDecided_stable]

/-- If `m1` and `m2` are both inflight and they have different destinations,
then receiving them in either order produces the same end state. -/
theorem recvMsg_comm {m1 m2 : Message P M} {s : State P M S}
    (hd : m1.dest ≠ m2.dest) (h1 : m1 ∈ s.msgs) (h2 : m2 ∈ s.msgs) :
    m2 ∈ (a.recvMsg m1 s).msgs ∧ m1 ∈ (a.recvMsg m2 s).msgs ∧
    a.recvMsg m2 (a.recvMsg m1 s) = a.recvMsg m1 (a.recvMsg m2 s) := by
  rw [State.mk.injEq]
  split_ands
  · grind [Algorithm.recvMsg, mem_erase_of_ne]
  · grind [Algorithm.recvMsg, mem_erase_of_ne]
  · have he1 (x) : (s.msgs.erase m1 + x).erase m2 = (s.msgs.erase m1).erase m2 + x := by
      grind [erase_add_left_pos, mem_erase_of_ne]
    have he2 (x) : (s.msgs.erase m2 + x).erase m1 = (s.msgs.erase m1).erase m2 + x := by
      grind [erase_add_left_pos, mem_erase_of_ne, erase_comm]
    simp [Algorithm.recvMsg, hd, hd.symm, he1, he2, add_assoc]
    grind [add_comm]
  · ext p
    by_cases h_p1 : p = m1.dest <;> by_cases h_p2 : p = m2.dest <;>
      simp [Algorithm.recvMsg, h_p1, h_p2, hd, hd.symm]

/-- A diamond property for the transition relation `a.LTS.Tr`. -/
theorem tr_diamond {ps : Set P} {x1 x2 : Action P M} {s s1 s2 : State P M S}
    (hx1 : DestIn ps x1) (hs1 : a.LTS.Tr s x1 s1)
    (hx2 : DestIn psᶜ x2) (hs2 : a.LTS.Tr s x2 s2) :
    ∃ s', a.LTS.Tr s1 x2 s' ∧ a.LTS.Tr s2 x1 s' := by
  cases x1 <;> cases x2 <;> try grind [Algorithm.LTS]
  case some m1 m2 =>
    have hd : m1.dest ≠ m2.dest := by grind [DestIn]
    obtain ⟨h_m1, rfl⟩ := hs1
    obtain ⟨h_m2, rfl⟩ := hs2
    simp only [Algorithm.LTS, exists_eq_right_right]
    grind [recvMsg_comm (a := a) hd h_m1 h_m2]

/-- A message that is in-flight stays in-flight as long as it is not received
(finite execution version). -/
theorem mTr_notRcvd_enabled {s t : State P M S} {xl : List (Action P M)} {m : Message P M}
    (hst : a.LTS.MTr s xl t) (hs : m ∈ s.msgs) (hxl : ¬ some m ∈ xl) : m ∈ t.msgs := by
  induction hst
  case refl _ => assumption
  case stepL s x s1 xl t h_tr h_mtr h_ind =>
    rcases Option.eq_none_or_eq_some x <;>
      grind [Algorithm.LTS, Algorithm.recvMsg, mem_erase_of_ne]

/-- A message that is in-flight stays in-flight as long as it is not received
(infinite execution version). -/
theorem omega_notRcvd_enabled
    {ss : ωSequence (State P M S)} {xs : ωSequence (Action P M)} {k : ℕ} {m : Message P M}
    (he : a.LTS.OmegaExecution ss xs) (hm : m ∈ (ss k).msgs) (hn : ∀ j, k ≤ j → xs j ≠ some m) :
    ∀ j, k ≤ j → m ∈ (ss j).msgs := by
  intro j h_j
  obtain ⟨i, rfl⟩ : ∃ i, j = k + i := by use j - k; grind
  induction i
  case zero => grind
  case succ i _ =>
    rcases Option.eq_none_or_eq_some (xs (k + i)) <;>
      grind [he (k + i), Algorithm.LTS, Algorithm.recvMsg, mem_erase_of_ne]

end Algorithm

end Cslib.FLP
