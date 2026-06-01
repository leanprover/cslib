/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.FLP.Algorithm
public import Mathlib.Data.Set.Card

/-! # Fault-tolerant consensus

Roughly speaking, a distributed consensus algorithm can tolerate `f` faults if up to `f`
processes can be "faulty" and yet the non-faulty processes can still reach a consensus.
The fault we consider here is limited to the crash fault, in which a process stops responding
to messages from some point onward.  We do not consider Byzantine faults.
-/

@[expose] public section

namespace Cslib.FLP

open Function Set Multiset Fintype ωSequence

variable {P M S : Type*}

/-- A process `p` is faulty in an infinite execution iff there is a time `k` from which onward
there is a message in-flight to `p` but `p` has stopped receiving messages. -/
def ProcFaulty (p : P) (ss : ωSequence (State P M S)) (xs : ωSequence (Action P M)) : Prop :=
  ∃ k, (∃ m, m ∈ (ss k).msgs ∧ m.dest = p) ∧ ∀ j, k ≤ j → ∀ m', xs j = some m' → m'.dest ≠ p

/-- A process `p` is fair in an infinite execution iff every message in-flight to `p` is
received by `p`. -/
def ProcFair (p : P) (ss : ωSequence (State P M S)) (xs : ωSequence (Action P M)) : Prop :=
  ∀ m, m.dest = p → ∀ k, m ∈ (ss k).msgs → ∃ j, k ≤ j ∧ xs j = some m

/-- A process `p` cannot be both faulty and fair in an infinite execution.  Note, however, that
it is possible for `p` to be neither faulty nor fair, because `p` can keep on receiving messages
but at the same time keep ignoring some messages sent to it. -/
theorem not_procFaulty_and_procFair (p : P)
    (ss : ωSequence (State P M S)) (xs : ωSequence (Action P M)) :
    ¬ (ProcFaulty p ss xs ∧ ProcFair p ss xs) := by
  grind [ProcFaulty, ProcFair]

/-- An infinite execution is fair iff every process is either faulty or fair
(cf. the comment for the theorem `not_procFaulty_and_procFair`). -/
def FairRun (ss : ωSequence (State P M S)) (xs : ωSequence (Action P M)) : Prop :=
  ∀ p, ProcFaulty p ss xs ∨ ProcFair p ss xs

/-- The number of faulty processes in an infinite execution. -/
noncomputable def numProcFaulty (ss : ωSequence (State P M S)) (xs : ωSequence (Action P M)) : ℕ :=
  {p | ProcFaulty p ss xs}.ncard

/-- If the number of faulty processes in an infinite execution is less than the total number
of processes, then at least one process is not faulty. -/
theorem not_procFaulty_of_numProcFaulty [Fintype P]
    {ss : ωSequence (State P M S)} {xs : ωSequence (Action P M)}
    (h : numProcFaulty ss xs < card P) : ∃ p, ¬ ProcFaulty p ss xs := by
  let nf := {p | ProcFaulty p ss xs}ᶜ
  have h1 : 0 < nf.ncard := by
    rw [ncard_compl]
    grind [numProcFaulty, card_eq_nat_card]
  obtain ⟨p, _⟩ := (ncard_pos (s := nf)).mp h1
  grind

/-- If every process in a set `ps` is fair, then the number of faulty processes is bounded by
the total number of processes minus the cardinality of `ps`. -/
theorem numProcFaulty_le_not_procFair [Fintype P]
    {ss : ωSequence (State P M S)} {xs : ωSequence (Action P M)} {ps : Set P}
    (h : ∀ p, p ∈ ps → ProcFair p ss xs) : numProcFaulty ss xs ≤ card P - ps.ncard := by
  rw [numProcFaulty, card_eq_nat_card, ← ncard_compl]
  suffices h1 : {p | ProcFaulty p ss xs} ⊆ psᶜ by exact ncard_le_ncard h1
  grind [not_procFaulty_and_procFair]

variable [DecidableEq P] [DecidableEq M]

/-- The notion of an infinite admissible execution for an algorithm `a` with input `inp`
and containing at most `f` faulty processes. -/
def Algorithm.AdmissibleRun [Fintype P] (a : Algorithm P M S) (inp : P → Bool) (f : ℕ)
    (ss : ωSequence (State P M S)) (xs : ωSequence (Action P M)) : Prop :=
  ss 0 = a.start inp ∧ a.lts.OmegaExecution ss xs ∧
  FairRun ss xs ∧ numProcFaulty ss xs ≤ f

/-- A process terminates in an infinite execution iff either it crashes or it decides on
a boolean value at some point. -/
def ProcTermination (p : P) (ss : ωSequence (State P M S)) (xs : ωSequence (Action P M)) : Prop :=
  ProcFaulty p ss xs ∨ ∃ k b, (ss k).ProcDecided p b

/-- An algorithm `a` terminates with up to `f` faulty processes iff all its processes terminate
in every infinite admissible execution containing at most `f` faulty processes. -/
def Algorithm.Termination [Fintype P] (a : Algorithm P M S) (f : ℕ) : Prop :=
  ∀ inp ss xs, a.AdmissibleRun inp f ss xs → ∀ p, ProcTermination p ss xs

/-- An algorithm `a` is a consensus algorithm tolerating up to `f` faulty processes iff
it both satisfies the consensus safety property `a.SafeConsensus` and terminates
with up to `f` faulty processes. -/
def Algorithm.Consensus [Fintype P] (a : Algorithm P M S) (f : ℕ) : Prop :=
  a.SafeConsensus ∧ a.Termination f

variable {a : Algorithm P M S} {inp : P → Bool}

/-- If an infinite execution is admissible with up tp `f` faulty processes,
then it is also admissible with with up tp `f' ≥ f` faulty processes. -/
theorem AdmissibleRun.fault_mono [Fintype P] {f f' : ℕ}
    {xs : ωSequence (Action P M)} {ss : ωSequence (State P M S)}
    (hle : f ≤ f') (ha : a.AdmissibleRun inp f ss xs) : a.AdmissibleRun inp f' ss xs := by
  grind [Algorithm.AdmissibleRun]

/-- If `a` is a consensus algorithm tolerating up to `f` faulty processes,
then it is also a consensus algorithm tolerating up to `f' ≤ f` faulty processes. -/
theorem Consensus.fault_mono [Fintype P] {f f' : ℕ}
    (hle : f ≥ f') (hc : a.Consensus f) : a.Consensus f' := by
  obtain ⟨h_sc, h_f⟩ := hc
  use h_sc
  intro inp
  grind [h_f inp, AdmissibleRun.fault_mono]

/-- If a process `p` is not fair in an infinite execution of an algorithm `a`, then there is
a message that is in-flight to, but never received, by `p` from some point onward. -/
theorem Algorithm.not_fair_stay_enabled
    {ss : ωSequence (State P M S)} {xs : ωSequence (Action P M)} {p : P}
    (he : a.lts.OmegaExecution ss xs) (hnf : ¬ ProcFair p ss xs) :
    ∃ m, m.dest = p ∧ ∃ k, m ∈ (ss k).msgs ∧ ∀ j, k ≤ j → m ∈ (ss j).msgs ∧ (xs j) ≠ some m := by
  simp only [ProcFair, not_forall, not_exists, not_and] at hnf
  grind only [omega_notRcvd_enabled]

/-- In an infinite execution of an algorithm `a`, a process `p` is fair iff `p` is fair in
all suffixes of the execution. -/
theorem Algorithm.drop_procFair_iff
    {ss : ωSequence (State P M S)} {xs : ωSequence (Action P M)}
    (he : a.lts.OmegaExecution ss xs) (p : P) (n : ℕ) :
    ProcFair p (ss.drop n) (xs.drop n) ↔ ProcFair p ss xs := by
  constructor <;> intro h
  · by_contra h_contra
    obtain ⟨m, h_m, k, h_k, h_ge⟩ := Algorithm.not_fair_stay_enabled he h_contra
    have := h m h_m k
    grind
  · intro m h_m k h_k
    obtain ⟨j, _, _⟩ := h m h_m (n + k) (by grind)
    use j - n
    grind

end Cslib.FLP
