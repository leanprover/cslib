/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.FLP.OnePseudoConsensus
public import Cslib.Foundations.Data.OmegaSequence.InfOcc

/-! # Impossibility of asynchronous distributed consensus in the presence of a single fault

This file formalizes the main theorem (Theorem 1) of [Volzer2004] and uses it to prove the
impossibility of asynchronous distributed consensus in the presence of a single fault.
-/

@[expose] public section

namespace Cslib.FLP

open Function Set Multiset Fintype Filter ωSequence

variable {P M S : Type*} [DecidableEq P] [DecidableEq M]

variable {a : Algorithm P M S}

/-- `a.ReachableNonUniform inp s` means that `s` is a reachable and non-uniform state of
algorithm `a` on input `inp`. -/
abbrev Algorithm.ReachableNonUniform [Fintype P]
    (a : Algorithm P M S) (inp : P → Bool) (s : State P M S) : Prop :=
  a.Reachable inp s ∧ a.NonUniform s

/-- Choose an arbitrary non-uniform input. -/
noncomputable def Algorithm.nonUniformInp [Fintype P] (a : Algorithm P M S)
    (hpc1 : a.PseudoConsensus 1) (hc : card P ≥ 2) : P → Bool :=
  Classical.choose (OnePseudoConsensus.nonUniform_inp hpc1 hc)

/-- Assuming `a.PseudoConsensus 1` and there are at least 2 processes, the input chosen by
`a.nonUniformInp` does indeed give rise to a non-uniform initial state. -/
theorem OnePseudoConsensus.nonUniform_init [Fintype P]
    (hpc1 : a.PseudoConsensus 1) (hc : card P ≥ 2) :
    let inp := a.nonUniformInp hpc1 hc
    a.ReachableNonUniform inp (a.start inp) := by
  grind [Algorithm.nonUniformInp, Algorithm.reachable_start]

/-- Assuming `a.PseudoConsensus 1`, starting from any reachable non-uniform state of `a` and
any message `m` that is in-flight in `s`, there exists a finite execution of `a` in which `m`
is received and which ends in another non-uniform state. -/
theorem OnePseudoConsensus.nonUniform_step_exists [Fintype P] {inp : P → Bool}
    (hpc1 : a.PseudoConsensus 1) {s : State P M S} {m : Message P M}
    (hs : a.ReachableNonUniform inp s) (hm : m ∈ s.msgs) :
    ∃ xl t, a.lts.MTr s xl t ∧ some m ∈ xl ∧ a.ReachableNonUniform inp t := by
  obtain ⟨hr, hn⟩ := hs
  obtain ⟨s', ⟨xl, h_mtr⟩, _⟩ := nonUniform_step hpc1 hr hn m.dest
  by_cases h_xl : some m ∈ xl
  · use xl, s'
    split_ands
    · assumption
    · assumption
    · grind [Algorithm.reachable_stable, LTS.CanReach]
    · intro b
      use m.dest
      grind
  · have := Algorithm.mTr_notRcvd_enabled h_mtr hm h_xl
    have h_tr : a.lts.Tr s' (some m) (a.recvMsg m s') := by grind [Algorithm.lts]
    have : a.lts.MTr s (xl ++ [some m]) (a.recvMsg m s') := by grind [LTS.MTr.stepR]
    use xl ++ [some m], a.recvMsg m s'
    split_ands
    · assumption
    · simp
    · grind [Algorithm.reachable_stable, LTS.CanReach]
    · intro b
      use m.dest
      grind [canDecideWithout_dest]

lemma OnePseudoConsensus.nonUniform_step_aux [Fintype P] (inp : P → Bool)
    (hpc1 : a.PseudoConsensus 1) (s : State P M S) (m : Message P M) :
    ∃ xl_t, m ∈ s.msgs ∧ a.ReachableNonUniform inp s →
      let (xl, t) := xl_t
      a.lts.MTr s xl t ∧ some m ∈ xl ∧ a.ReachableNonUniform inp t := by
  by_cases h : m ∈ s.msgs ∧ a.ReachableNonUniform inp s
  · obtain ⟨hm, hs⟩ := h
    obtain ⟨xl, t, _⟩ := OnePseudoConsensus.nonUniform_step_exists hpc1 hs hm
    use (xl, t)
    grind
  · use ([], s)
    grind

/-- Choose an arbitrary finite execution guaranteed to exist by the theorem
`OnePseudoConsensus.nonUniform_step_exists`. -/
noncomputable def Algorithm.nonUniformStep [Fintype P] (a : Algorithm P M S) (inp : P → Bool)
    (hpc1 : a.PseudoConsensus 1) : DeliverMsg P M S :=
  fun s m ↦ Classical.choose (OnePseudoConsensus.nonUniform_step_aux inp hpc1 s m)

/-- Assuming `a.PseudoConsensus 1`, `a.nonUniformStep` does have the property guaranteed by
the theorem `OnePseudoConsensus.nonUniform_step_exists`. -/
theorem OnePseudoConsensus.fair_nonUniform_step [Fintype P] (inp : P → Bool)
    (hpc1 : a.PseudoConsensus 1) :
    a.FairDeliverMsg (a.nonUniformStep inp hpc1) univ (a.ReachableNonUniform inp) := by
  intro s m
  grind [Algorithm.nonUniformStep]

/-- Assuming `a.PseudoConsensus 1`, starting from any reachable non-uniform state `s0` of `a`,
use the fair scheduler developed in `FairSchedular.lean` to construct an infinite fair execution
in which there are infinitely many non-uniform states. -/
theorem OnePseudoConsensus.fair_nonUniform [Fintype P] (inp : P → Bool)
    (hpc1 : a.PseudoConsensus 1) (s0 : State P M S) (hs0 : a.ReachableNonUniform inp s0) :
    ∃ ss xs, a.lts.OmegaExecution ss xs ∧ ss 0 = s0 ∧ (∀ p, ProcFair p ss xs) ∧
      ∃ᶠ n in atTop, a.ReachableNonUniform inp (ss n) := by
  obtain ⟨ss', _⟩ := FairScheduler.fair_omegaExecution (fair_nonUniform_step inp hpc1) s0 hs0
  let xls := a.fairSegActions (a.nonUniformStep inp hpc1) univ s0
  use ss', xls.flatten
  split_ands
  · grind
  · grind
  · grind
  · apply frequently_iff_strictMono.mpr
    use xls.cumLen
    grind [cumLen_strictMono]

/-- Assuming `a.PseudoConsensus 1` and there are at least 2 processes, there must exist an
infinite admissible execution in which no process is faulty but no process terminates, either.
This theorem formalizes Theorem 1 of [Volzer2004]. -/
theorem OnePseudoConsensus.not_terminating [Fintype P]
    (hpc1 : a.PseudoConsensus 1) (hc : card P ≥ 2) :
    ∃ inp ss xs, a.AdmissibleRun inp 0 ss xs ∧ ∀ p, ¬ ProcTermination p ss xs := by
  let inp := a.nonUniformInp hpc1 hc
  let s0 := a.start inp
  obtain ⟨ss, xs, _, _, _, h_freq⟩ := fair_nonUniform inp hpc1 s0 (nonUniform_init hpc1 hc)
  use inp, ss, xs
  split_ands
  · assumption
  · assumption
  · grind [FairRun]
  · have := numProcFaulty_le_not_procFair (ps := univ) (ss := ss) (xs := xs)
    grind [ncard_univ, card_eq_nat_card]
  · rintro p (_ | ⟨k, b, h_k⟩)
    · grind [not_procFaulty_and_procFair]
    · have h_r (n : ℕ) : a.Reachable inp (ss n) := by
        use xs.extract 0 n
        grind [LTS.OmegaExecution.extract_mTr]
      have (j : ℕ) (h_j : k ≤ j) : a.Uniform (ss j) b := by
        apply decided_imp_uniform hpc1 (h_r j)
        use p
        apply Algorithm.procDecided_stable (a := a) h_k
        use xs.extract k j
        grind [LTS.OmegaExecution.extract_mTr]
      obtain ⟨n, _⟩ : ∃ n, k ≤ n ∧ a.NonUniform (ss n) := by grind [frequently_atTop.mp h_freq k]
      grind [not_uniform_and_nonUniform]

/-- As long as there are at least 2 processes, there does not exist a distributed consensus
algorithm that can tolerate 1 fault. -/
theorem Consensus.one_not_exists [Fintype P] (hc : card P ≥ 2) :
    ¬ ∃ a : Algorithm P M S, a.Consensus 1 := by
  rintro ⟨a, h_cons⟩
  have hpc1 := PseudoConsensus.of_consensus 1 (show 1 < card P by grind) h_cons
  obtain ⟨inp, ss, xs, h_run, _⟩ := OnePseudoConsensus.not_terminating hpc1 hc
  have h_run' := AdmissibleRun.fault_mono (show 0 ≤ 1 by grind) h_run
  have := Classical.inhabited_of_nonempty <|
    Fintype.card_pos_iff.mp (show 0 < Fintype.card P by grind)
  grind [h_cons.right inp ss xs h_run' (default : P)]

/-- As long as there are at least 2 processes, there does not exist a distributed consensus
algorithm that can tolerate `f` faults for any `f ≥ 1`. -/
theorem Consensus.ge_one_not_exists [Fintype P] {f : ℕ} (hc : card P ≥ 2) (hf : f ≥ 1) :
    ¬ ∃ a : Algorithm P M S, a.Consensus f := by
  rintro ⟨a, h_c⟩
  suffices h1 : ∃ a : Algorithm P M S, a.Consensus 1 by
    exact Consensus.one_not_exists hc h1
  use a
  grind [Consensus.fault_mono]

end Cslib.FLP
