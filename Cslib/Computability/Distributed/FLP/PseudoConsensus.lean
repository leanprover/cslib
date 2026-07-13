/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.FLP.CanReachVia
public import Cslib.Computability.Distributed.FLP.FairScheduler

/-! # Fault-tolerant pseudo-consensus

A central idea of [Volzer2004] is the notion of pseudo-consensus, which weakens the notion of
consensus by replacing the requirement of termination, which is stated in terms of infinite
executions, by that of pseudo-termination, which is stated in terms of finite executions.
This makes the notion of pseudo-consensus easier to work with than consensus.  This file
defines pseudo-consensus and proves that it is implied by consensus.  This resilt is intuitively
obvious and is stated without proof in [Volzer2004], but it turns out to require quite a bit
of formal machinery to prove.
-/

@[expose] public section

namespace Cslib.FLP

open Function Set Multiset Fintype ωSequence FairScheduler

variable {P M S : Type*} [DecidableEq P] [DecidableEq M]

/-- An algorithm `a` satisfies `f`-tolerant pseudo-termination iff for every reachable state `s`
of `a` and every `ps` of at least `card P - f` processes, there exists a state `s'` reachable from
`s` using only messages with destinations in `ps` which has decided on a boolean value.
In other words, from any reachable state of `a`, a decision can be made without the participation
of at most `f` processes. -/
def Algorithm.PseudoTermination [Fintype P] (a : Algorithm P M S) (f : ℕ) : Prop :=
  ∀ inp s, a.Reachable inp s →
    ∀ ps : Set P, ps.ncard ≥ card P - f →
      ∃ s' b, a.CanReachVia ps s s' ∧ s'.Decided b

/-- An algorithm `a` is a pseudo-consensus algorithm tolerating up to `f` faults iff it satisfies
both the consensus safety property `a.SafeConsensus` and `f`-tolerant pseudo-termination. -/
def Algorithm.PseudoConsensus [Fintype P] (a : Algorithm P M S) (f : ℕ) : Prop :=
  a.SafeConsensus ∧ a.PseudoTermination f

open scoped Classical in
/-- `a.simpleDeliver ps` delivers any message that is in-flight and has its destination in `ps`. -/
noncomputable def Algorithm.simpleDeliver (a : Algorithm P M S) (ps : Set P) : DeliverMsg P M S :=
  fun s m ↦ if m ∈ s.msgs ∧ m.dest ∈ ps then
    ([m], a.recvMsg m s)
  else
    ([], s)

namespace PseudoConsensus

variable {a : Algorithm P M S}

lemma simpleDeliver_fair (ps : Set P) :
    a.FairDeliverMsg (a.simpleDeliver ps) ps (fun _ ↦ True) := by
  intro s m h
  simp only [h, Algorithm.simpleDeliver, Algorithm.lts]
  grind [LTS.MTr.single]

lemma simpleDeliver_forallActions (ps : Set P) :
    (a.simpleDeliver ps).ForallActions (DestIn ps) := by
  simp only [DeliverMsg.ForallActions, Algorithm.simpleDeliver]
  intro s m
  by_cases h : m ∈ s.msgs ∧ m.dest ∈ ps <;> simp [h, DestIn]

/-- If an algorithm `a` is a consensus algorithm tolerating up to `f` faults, then `a` is also
a pseudo-consensus algorithm tolerating up to `f` faults.  The main difficulty in the proof of
this theorem is that we need to construct an infinite admissible execution starting from any
reachable state of `a` using any subset of non-faulty processes.  This is achieved using the
fair scheduler developed in `FairSchedular.lean`. -/
theorem of_consensus [Fintype P] (f : ℕ) (hf : f < card P)
    (hc : a.Consensus f) : a.PseudoConsensus f := by
  obtain ⟨h_safe, h_term⟩ := hc
  use h_safe
  rintro inp s ⟨xl, h_xl⟩ ps h_ps
  let xls := a.fairSegActions (a.simpleDeliver ps) ps s
  obtain ⟨ss, h_omega, h_s, _⟩ := fair_omegaExecution (simpleDeliver_fair ps) s trivial
  obtain ⟨ss', h_omega', _, _, _⟩ := LTS.OmegaExecution.append h_xl h_omega h_s
  have h_dest := omega_forall_actions (r := DestIn ps) (d := a.simpleDeliver ps)
      (simpleDeliver_fair ps) s trivial (simpleDeliver_forallActions ps) (by simp [DestIn])
  have : ∀ p, p ∈ ps → ProcFair p ss' (xl ++ω xls.flatten) := by
    intro p h_p
    rw [← Algorithm.drop_procFair_iff h_omega' p xl.length]
    grind [drop_append_of_ge_length]
  have : FairRun ss' (xl ++ω xls.flatten) := by
    intro p
    by_cases h_f : ProcFair p ss' (xl ++ω xls.flatten)
    · grind
    · obtain ⟨m, _, n, _, _⟩ := Algorithm.not_fair_stay_enabled h_omega' h_f
      suffices ProcFaulty p ss' (xl ++ω xls.flatten) by grind
      use n + xl.length, by grind
      intro k h_k m' h_m'
      have : xls.flatten (k - xl.length) = some m' := by grind [get_append_right']
      grind [DestIn]
  have : numProcFaulty ss' (xl ++ω xls.flatten) ≤ f := by
    suffices numProcFaulty ss' (xl ++ω xls.flatten) ≤ card P - ps.ncard by grind
    apply numProcFaulty_le_not_procFair
    grind
  have h_adm : a.AdmissibleRun inp f ss' (xl ++ω xls.flatten) := by grind [Algorithm.AdmissibleRun]
  have hf' : numProcFaulty ss' (xl ++ω xls.flatten) < card P := by grind
  obtain ⟨p, _⟩ := not_procFaulty_of_numProcFaulty hf'
  obtain ⟨n, b, _⟩ : ∃ n b, (ss' n).ProcDecided p b := by
    grind [ProcTermination, h_term inp ss' (xl ++ω xls.flatten) h_adm p]
  let m := n + xl.length
  use ss' m, b
  split_ands
  · use (xl ++ω xls.flatten).extract xl.length m, by grind [LTS.OmegaExecution.extract_mTr]
    simp [extract_append_right_right, extract_eq_take,
      List.forall_iff_forall_mem, List.forall_mem_iff_getElem]
    grind
  · have : (ss' n).Decided b := by use p
    suffices a.lts.CanReach (ss' n) (ss' m) by grind [Algorithm.decided_stable]
    use (xl ++ω xls.flatten).extract n m
    grind [LTS.OmegaExecution.extract_mTr]

end PseudoConsensus

end Cslib.FLP
