/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.FLP.Consensus
public import Cslib.Foundations.Data.OmegaSequence.Temporal

/-! # Asynchronous distributed consensus in the absence of faults

This file presents an asynchronous distributed consensus algorithm and proves that it does achieve
consensus when there is no fault.  Assume that there are `n` processes numbered 0, 1, ..., `n - 1`.
The algorithm works as follows:
(1) Process 0 receives its input value and sends that value to all processes (including itself).
    All other processes ignore their inputs upon receiving them.
(2) Upon receiving the value sent by process 0 in the previpus step, every process (including
    process 0) decides on that value.
Clearly, if there is no fault and all messages are eventually delivered, every process will
eventually decide on the same value, namely, the input value at process 0.

The contents of this file are not needed for proving the FLP impossibility result, but do show
that the notion of an `Algorithm` is not vacuous, in the sense that it allows a working
asynchronous consensus algorithm when there is no fault.
-/

@[expose] public section

namespace Cslib.FLP.ZeroFaultAlg

open Set Sum Option Multiset ωSequence

/-- The payload of a message is of type `Bool ⊕ Bool`, where `inl b` denotes an input value `b`
ane `inr b` denotes a value `b` sent by process 0 to all processes (including itself). -/
abbrev M := Bool

/-- The local state of a process is trivial. -/
abbrev S := Unit

variable {n : ℕ} (npos : 0 < n)

/-- `alg` is the asynchronous distributed consensus algorithm described above. -/
def alg : Algorithm (Fin n) M S where
  init _ := ()
  next _ _ := ()
  send m _ := match m.msg with
    | inl b =>
      if m.dest = ⟨0, npos⟩ then Multiset.map (fun p ↦ ⟨p, inr b⟩) Finset.univ.val else 0
    | inr _ => 0
  out m _ := match m.msg with
    | inl _ => none
    | inr b => some b

/-- `Inv` is an invariant for `alg`. -/
def Inv (inp : Fin n → Bool) (s : State (Fin n) M S) : Prop :=
  (∀ m, m ∈ s.msgs → m.msg = inl (inp m.dest) ∨ m.msg = inr (inp ⟨0, npos⟩)) ∧
  (∀ p, (s.proc p).out = none ∨ (s.proc p).out = some (inp ⟨0, npos⟩))

/-- `Inv` is true at any initial state. -/
theorem inv_start (inp : Fin n → Bool) :
    Inv npos inp ((alg npos).start inp) := by
  simp [alg, Inv, Algorithm.start]

/-- What happens when an `inl` message is received. -/
theorem inv_tr_left (inp : Fin n → Bool) {s t : State (Fin n) M S} {m : Message (Fin n) M}
    (hs : Inv npos inp s) (htr : (alg npos).lts.Tr s (some m) t) (hm : m.msg.isLeft) :
    t.msgs = s.msgs.erase m +
      ( if m.dest = ⟨0, npos⟩ then Multiset.map (fun p ↦ ⟨p, inr (inp ⟨0, npos⟩)⟩) Finset.univ.val
        else 0 ) ∧
    ∀ p, (t.proc p).out = (s.proc p).out := by
  simp only [alg] at htr
  split_ands <;> grind [Inv, Algorithm.lts, Algorithm.recvMsg]

/-- What happens when an `inr` message is received. -/
theorem inv_tr_right (inp : Fin n → Bool) {s t : State (Fin n) M S} {m : Message (Fin n) M}
    (hs : Inv npos inp s) (htr : (alg npos).lts.Tr s (some m) t) (hm : m.msg.isRight) :
    t.msgs = s.msgs.erase m ∧ (t.proc m.dest).out = some (inp ⟨0, npos⟩) ∧
    ∀ p, p ≠ m.dest → (t.proc p).out = (s.proc p).out := by
  simp only [alg] at htr
  grind [Inv, Algorithm.lts, Algorithm.recvMsg]

/-- The truth of `Inv` is preserved by every transition of `alg`. -/
theorem trInv_inv (inp : Fin n → Bool) : (alg npos).lts.TrInv (Inv npos inp) := by
  intro s x t htr hs
  rcases eq_none_or_eq_some x with _ | ⟨m, rfl⟩
  · grind [Algorithm.lts]
  · have h1 : m.msg = inl (inp m.dest) ∨ m.msg = inr (inp ⟨0, npos⟩) := by
      grind [Inv, Algorithm.lts]
    rcases h1
    · have := inv_tr_left npos inp hs htr
      grind [Inv, erase_le, mem_of_le, Multiset.mem_map]
    · have := inv_tr_right npos inp hs htr
      grind [Inv, erase_le, mem_of_le]

/-- `Inv` is true in all reachable state of `alg`. -/
theorem reachable_inv (inp : Fin n → Bool) {s : State (Fin n) M S}
    (hr : (alg npos).Reachable inp s) : Inv npos inp s := by
  obtain ⟨xs, _⟩ := hr
  have := LTS.mtrInv_of_trInv <| trInv_inv npos inp
  grind [LTS.MTrInv, inv_start npos inp]

/-- `alg` satisfies the `SafeConsensus` property. -/
theorem safeConsensus : (alg npos).SafeConsensus := by
  intro inp s hr
  grind [reachable_inv npos inp hr, Inv, State.Agreed, State.Decided]

/-- `Inv` is true at every state in an admissible run of `alg`. -/
theorem always_inv (inp : Fin n → Bool)
    {ss : ωSequence (State (Fin n) M S)} {xs : ωSequence (Action (Fin n) M)}
    (ha : (alg npos).AdmissibleRun inp 0 ss xs) (k : ℕ) : Inv npos inp (ss k) := by
  apply reachable_inv
  apply Algorithm.reachable_stable <| Algorithm.reachable_start
  use xs.extract 0 k
  grind [AdmissibleRun.fault_zero, LTS.OmegaExecution.extract_mTr]

/-- The message carrying the input value for process 0 is enabled in the initial state. -/
theorem init_left (inp : Fin n → Bool)
    {ss : ωSequence (State (Fin n) M S)} {xs : ωSequence (Action (Fin n) M)}
    (ha : (alg npos).AdmissibleRun inp 0 ss xs) :
    ss 0 ∈ {s | ⟨⟨0, npos⟩, inl (inp ⟨0, npos⟩)⟩ ∈ s.msgs} := by
  obtain ⟨hi, _, _⟩ := AdmissibleRun.fault_zero.mp ha
  simp [hi, Algorithm.start]

/-- Whenever the message carrying the input value for process 0 is enabled in a state,
a message carrying that value is eventually sent to every process `p` by process 0. -/
theorem left_leadsTo_right (inp : Fin n → Bool)
    {ss : ωSequence (State (Fin n) M S)} {xs : ωSequence (Action (Fin n) M)}
    (ha : (alg npos).AdmissibleRun inp 0 ss xs) (p : Fin n) :
    ss.LeadsTo {s | ⟨⟨0, npos⟩, inl (inp ⟨0, npos⟩)⟩ ∈ s.msgs}
      {s | ⟨p, inr (inp ⟨0, npos⟩)⟩ ∈ s.msgs} := by
  let m : Message (Fin n) M := ⟨⟨0, npos⟩, inl (inp ⟨0, npos⟩)⟩
  intro k _
  have : m ∈ (ss k).msgs := by grind
  obtain ⟨_, _, hf⟩ := AdmissibleRun.fault_zero.mp ha
  obtain ⟨j, _, _⟩ : ∃ j, k ≤ j ∧ xs j = some m := by grind [hf ⟨0, npos⟩, ProcFair]
  use j + 1
  have hj := always_inv npos inp ha j
  have htr : (alg npos).lts.Tr (ss j) (some m) (ss (j + 1)) := by grind [LTS.OmegaExecution]
  have h1 : k ≤ j + 1 := by grind
  simp [h1, m, inv_tr_left npos inp hj htr rfl]

/-- Whenever a message carrying a value sent by process 0 is enabled at a process `p`,
`p` eventually decides on that value. -/
theorem right_leadsTo_out (inp : Fin n → Bool)
    {ss : ωSequence (State (Fin n) M S)} {xs : ωSequence (Action (Fin n) M)}
    (ha : (alg npos).AdmissibleRun inp 0 ss xs) (p : Fin n) :
    ss.LeadsTo {s | ⟨p, inr (inp ⟨0, npos⟩)⟩ ∈ s.msgs}
      {s | (s.proc p).out = some (inp ⟨0, npos⟩)} := by
  let m : Message (Fin n) M := ⟨p, inr (inp ⟨0, npos⟩)⟩
  intro k _
  have : m ∈ (ss k).msgs := by grind
  obtain ⟨_, _, hf⟩ := AdmissibleRun.fault_zero.mp ha
  obtain ⟨j, _, _⟩ : ∃ j, k ≤ j ∧ xs j = some m := by grind [hf p, ProcFair]
  use j + 1
  have hj := always_inv npos inp ha j
  have htr : (alg npos).lts.Tr (ss j) (some m) (ss (j + 1)) := by grind [LTS.OmegaExecution]
  grind [inv_tr_right npos inp hj htr]

/-- `alg` is a correct asynchronous distributed consensus algorithm when there is no fault. -/
theorem consensus_zero : (alg npos).Consensus 0 := by
  use safeConsensus npos
  intro inp ss xs ha p
  right
  have hlt1 := left_leadsTo_right npos inp ha p
  have hlt2 := right_leadsTo_out npos inp ha p
  have := leadsTo_trans hlt1 hlt2 0 <| init_left npos inp ha
  grind

end Cslib.FLP.ZeroFaultAlg
