/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.FLP.PseudoConsensus

/-! # 1-tolerant pseudo-consensus

This file develops the theory of pseudo-consensus algorithms that can tolerate up to 1 fault.
It formalizes section 3 of [Volzer2004] except Theorem 1.
-/

@[expose] public section

namespace Cslib.FLP

open Function Set Multiset Fintype

variable {P M S : Type*} [DecidableEq P] [DecidableEq M]

/-- `a.OneSilentDecided s p b` means that the boolean value `b` is decided on in a state that
is reachable from `s` without the participation of `p`. In the notation of [Volzer2004], this
is equivalent to `b ∈ val(p,s)`. -/
def Algorithm.OneSilentDecided (a : Algorithm P M S)
    (s : State P M S) (p : P) (b : Bool) : Prop :=
  ∃ s', a.CanReachVia {p}ᶜ s s' ∧ s'.Decided b

/-- `a.Uniform s b` means that for every process `p`, `a.OneSilentDecided s p b` but
not `a.OneSilentDecided s p !b`. -/
def Algorithm.Uniform (a : Algorithm P M S) (s : State P M S) (b : Bool) : Prop :=
  ∀ p, a.OneSilentDecided s p b ∧ ¬ a.OneSilentDecided s p !b

/-- `a.NonUniform s` means that for each boolean value `b`, there is a process `p`
such that `a.OneSilentDecided s p b`. -/
def Algorithm.NonUniform (a : Algorithm P M S) (s : State P M S) : Prop :=
  ∀ b, ∃ p, a.OneSilentDecided s p b

namespace OnePseudoConsensus

variable {a : Algorithm P M S} {inp : P → Bool}

/-- Draw a consequence of `a.PseudoConsensus 1`. -/
theorem pseudoTermination [Fintype P] (hpc1 : a.PseudoConsensus 1)
    {s : State P M S} (hr : a.Reachable inp s) (p : P) :
    ∃ s' b, a.CanReachVia {p}ᶜ s s' ∧ s'.Decided b := by
  apply hpc1.right inp s hr {p}ᶜ
  simp [Set.ncard_compl {p}]

/-- Assuming `a.PseudoConsensus 1`, for any reachable state of `a` and for any process `p`,
there is a boolean value `b` such that `a.OneSilentDecided s p b`. This theorem formalizes
Proposition 2(a) of [Volzer2004]. -/
theorem oneSilentDecided_exists [Fintype P] (hpc1 : a.PseudoConsensus 1)
    {s : State P M S} (hr : a.Reachable inp s) (p : P) :
    ∃ b, a.OneSilentDecided s p b := by
  obtain ⟨s', b, _⟩ := pseudoTermination hpc1 hr p
  use b
  grind [Algorithm.OneSilentDecided]

/-- A state cannot be both uniform and non-uniform. -/
theorem not_uniform_and_nonUniform {s : State P M S} (b : Bool) :
    ¬ (a.Uniform s b ∧ a.NonUniform s) := by
  rintro ⟨_, h_n⟩
  obtain ⟨p, _⟩ := h_n !b
  grind [Algorithm.Uniform]

/-- Assuming `a.PseudoConsensus 1`, any reachable state of `a` is either uniform or non-uniform. -/
theorem uniform_or_nonUniform [Fintype P] (hpc1 : a.PseudoConsensus 1)
    {s : State P M S} (hr : a.Reachable inp s) :
    a.Uniform s false ∨ a.Uniform s true ∨ a.NonUniform s := by
  by_cases h : a.Uniform s false ∨ a.Uniform s true
  · grind
  · suffices a.NonUniform s by grind
    simp only [Algorithm.Uniform, not_or, not_forall, not_and, not_not,
      Bool.not_false, Bool.not_true] at h
    obtain ⟨⟨p, _⟩, ⟨q, _⟩⟩ := h
    rintro (_ | _)
    · use q
      obtain ⟨b, _⟩ := oneSilentDecided_exists hpc1 hr q
      grind [Bool.dichotomy b]
    · use p
      obtain ⟨b, _⟩ := oneSilentDecided_exists hpc1 hr p
      grind [Bool.dichotomy b]

/-- Assuming `a.PseudoConsensus 1`, if a reachable state of `a` has decided on a boolean value `b`
and `a.OneSilentDecided s p b'` for any process `p`, then `b = b'`. -/
theorem decided_eq_oneSilentDecided [Fintype P] (hpc1 : a.PseudoConsensus 1)
    {s : State P M S} (hr : a.Reachable inp s) {b b' : Bool} {p : P}
    (hd : s.Decided b) (hd' : a.OneSilentDecided s p b') : b = b' := by
  obtain ⟨s', hc, _⟩ := hd'
  have hc := CanReachVia.canReach hc
  grind [Algorithm.reachable_stable hr hc, Algorithm.decided_stable hd hc,
    Algorithm.PseudoConsensus, Algorithm.SafeConsensus, State.Agreed]

/-- Assuming `a.PseudoConsensus 1`, if a reachable state of `a` has decided on a boolean value `b`,
then `s` is uniform for `b`. This theorem formalizes Proposition 2(b) of [Volzer2004]. -/
theorem decided_imp_uniform [Fintype P] (hpc1 : a.PseudoConsensus 1)
    {s : State P M S} (hr : a.Reachable inp s) {b : Bool} (hd : s.Decided b) :
    a.Uniform s b := by
  intro p
  obtain ⟨b', _⟩ := oneSilentDecided_exists hpc1 hr p
  grind [decided_eq_oneSilentDecided hpc1 hr hd]

/-- For any message `m`, if state `s'` is reached from state `s` by receiving `m`, then
`a.OneSilentDecided s m.dest b` implies `a.OneSilentDecided s' m.dest b` for any `b`.
This theorem formalizes Proposition 3(b) of [Volzer2004]. -/
theorem oneSilentDecided_dest {s s' : State P M S} {m : Message P M} {b : Bool}
    (ht : a.lts.Tr s (some m) s')
    (hd : a.OneSilentDecided s m.dest b) : a.OneSilentDecided s' m.dest b := by
  obtain ⟨t, h_s, h_t⟩ := hd
  have h_m : a.CanReachVia {m.dest} s s' := by
    use [some m]
    grind [DestIn, LTS.MTr, List.Forall]
  obtain ⟨t', h_s', h_t'⟩ := CanReachVia.diamond h_m h_s
  use t', h_s'
  grind [CanReachVia.canReach h_t', Algorithm.decided_stable]

/-- For any message `m`, if state `s'` is reached from state `s` by receiving `m`, then
`a.OneSilentDecided s' p b` implies `a.OneSilentDecided s p b` for any `b` and any `p ≠ m.dest`.
This theorem formalizes Proposition 3(a) of [Volzer2004]. -/
theorem oneSilentDecided_nondest {s s' : State P M S} {m : Message P M} {b : Bool}
    (ht : a.lts.Tr s (some m) s') {p : P} (hn : p ≠ m.dest)
    (hd' : a.OneSilentDecided s' p b) : a.OneSilentDecided s p b := by
  obtain ⟨t, h_s', h_t⟩ := hd'
  refine ⟨t, ?_, h_t⟩
  have hx : DestIn {p}ᶜ (some m) := by grind [DestIn]
  exact CanReachVia.stepL hx ht h_s'

/-- Assuming `a.PseudoConsensus 1`, if any reachable state `s` of `a` is uniform for `b` and
state `s'` is reached from `s` by receiving a message `m`, then `a.OneSilentDecided s' p b`.
This theorem formalizes Proposition 3(c) of [Volzer2004]. -/
theorem oneSilentDecided_uniform [Fintype P] (hpc1 : a.PseudoConsensus 1)
    {s s' : State P M S} {m : Message P M} {b : Bool}
    (hr : a.Reachable inp s) (ht : a.lts.Tr s (some m) s') {p : P}
    (hd : a.OneSilentDecided s p b) (hdn : ¬ a.OneSilentDecided s p !b) :
    a.OneSilentDecided s' p b := by
  by_cases h_card : p = m.dest
  · obtain ⟨rfl⟩ := h_card
    exact oneSilentDecided_dest ht hd
  · have h_ss'' : a.Reachable inp s' := by
      apply Algorithm.reachable_stable hr
      use [some m]
      grind [LTS.MTr]
    obtain ⟨b', h_s'⟩ := oneSilentDecided_exists hpc1 h_ss'' p
    by_cases h_b : b' = b
    · grind
    · grind [oneSilentDecided_nondest ht h_card h_s', Bool.eq_not_of_ne h_b]

/-- Assuming `a.PseudoConsensus 1`, if any reachable state `s` of `a` that is non-uniform,
then for any process `p`, there exists a state `s'` reachable from `s` such that
`a.OneSilentDecided s' p b` for all `b`. This theorem formalizes Lemma 2 of [Volzer2004]. -/
theorem nonUniform_step [Fintype P] (hpc1 : a.PseudoConsensus 1)
    {s : State P M S} (hr : a.Reachable inp s) (hn : a.NonUniform s) (p : P) :
    ∃ s', a.lts.CanReach s s' ∧ ∀ b, a.OneSilentDecided s' p b := by
  obtain ⟨b, h_s⟩ := oneSilentDecided_exists hpc1 hr p
  obtain ⟨q, s', h_ss', h_s'⟩ := hn !b
  have hr' := Algorithm.reachable_stable hr (CanReachVia.canReach h_ss')
  obtain ⟨xs, h_mtr, h_xs'⟩ := h_ss'
  obtain ⟨ss, h_ss'⟩ := LTS.Execution.of_mTr h_mtr
  have reach_lemma (k : ℕ) (h : k < ss.length) : a.lts.CanReach s ss[k] := by
    use xs.take k
    have := LTS.Execution.split h_ss' k
    grind [LTS.Execution, LTS.Execution.to_mTr]
  have : a.OneSilentDecided s' p !b := by
    obtain ⟨b', h_b'⟩ := oneSilentDecided_exists hpc1 hr' p
    grind [decided_eq_oneSilentDecided hpc1 hr' h_s' h_b']
  have h_nb : ∃ n, ∃ _ : n < ss.length, a.OneSilentDecided ss[n] p !b := by grind [LTS.Execution]
  classical
  let n := Nat.find h_nb
  obtain ⟨_, _⟩ : ∃ _ : n < ss.length, a.OneSilentDecided ss[n] p !b := by grind
  use ss[n], ?_, ?_
  · grind [reach_lemma n]
  · suffices ∀ k, (_ : k ≤ n) → a.OneSilentDecided ss[k] p b by
      intro b'
      by_cases h : b' = !b
      · grind
      · simp only [Bool.not_eq_not] at h
        grind
    intro k
    induction k
    case zero => grind [LTS.Execution]
    case succ k h_ind =>
      intro h_k
      obtain ⟨_, _, _, _⟩ := h_ss'
      have h_tr : a.lts.Tr ss[k] xs[k] ss[k + 1] := by grind
      obtain (_ | ⟨m, h_m⟩) := Option.eq_none_or_eq_some xs[k]
      · grind [Algorithm.tr_none]
      · rw [h_m] at h_tr
        have hr_k : a.Reachable inp ss[k] := by
          apply Algorithm.reachable_stable hr
          grind [reach_lemma k]
        have hnb_k : ¬a.OneSilentDecided ss[k] p !b := by grind [Nat.find_min h_nb (m := k)]
        exact oneSilentDecided_uniform hpc1 hr_k h_tr (h_ind (by grind)) hnb_k

section NonUniformInit

variable [Fintype P]

/-- Given a numbering `pn` of processes and `n : ℕ`, `inpN pn n` assigns `true` to the processes
numbered `0, ..., (n - 1)` and `false` to the rest. -/
def inpN (pn : P ≃ Fin (card P)) (n : ℕ) : P → Bool :=
  fun p ↦ if pn p < n then true else false

omit [DecidableEq P] in
/-- Assuming `0 < n ≤ card P`, the inputs `inpN pn (n - 1)` amd `inpN pn n` agree on all processes
except the one that is numbered `(n - 1)`. -/
theorem inpN_eqOn_except_singleton (pn : P ≃ Fin (card P))
    {n : ℕ} (hn0 : 0 < n) (hnc : n ≤ card P) :
    InpEqOn {pn.symm ⟨n - 1, by grind⟩}ᶜ (inpN pn (n - 1)) (inpN pn n) := by
  intro p h_p
  suffices pn p ≠ n - 1 by
    grind [inpN]
  intro h
  simp [← h] at h_p

lemma inpN_zero_no_true (pn : P ≃ Fin (card P)) (hpc1 : a.PseudoConsensus 1) (p : P) :
    ¬ a.OneSilentDecided (a.start (inpN pn 0)) p true := by
  rintro ⟨s, h_r, h_b⟩
  have h_s : a.Reachable (inpN pn 0) s := by
    have h_i := Algorithm.reachable_start (a := a) (inp := inpN pn 0)
    exact Algorithm.reachable_stable h_i (CanReachVia.canReach h_r)
  obtain ⟨q, h_q⟩ := (hpc1.left (inpN pn 0) s h_s).right true h_b
  simp [inpN] at h_q

/-- Assuming `a.PseudoConsensus 1`, the initial state determined by the all-`false` input
is uniform for `false`. -/
theorem inpN_zero_uniform (pn : P ≃ Fin (card P)) (hpc1 : a.PseudoConsensus 1) (hc : card P ≥ 1) :
    a.Uniform (a.start (inpN pn 0)) false := by
  have h_i := Algorithm.reachable_start (a := a) (inp := inpN pn 0)
  obtain (h | h | h) := uniform_or_nonUniform hpc1 h_i
  · exact h
  · grind [inpN_zero_no_true, h (pn.symm ⟨0, by grind⟩)]
  · grind [inpN_zero_no_true, h true]

lemma inpN_card_not_false (pn : P ≃ Fin (card P)) (hpc1 : a.PseudoConsensus 1) (p : P) :
    ¬ a.OneSilentDecided (a.start (inpN pn (card P))) p false := by
  rintro ⟨s, h_r, h_b⟩
  have h_s : a.Reachable (inpN pn (card P)) s := by
    have h_i := Algorithm.reachable_start (a := a) (inp := inpN pn (card P))
    exact Algorithm.reachable_stable h_i (CanReachVia.canReach h_r)
  obtain ⟨q, h_q⟩ := (hpc1.left (inpN pn (card P)) s h_s).right false h_b
  simp [inpN] at h_q

/-- Assuming `a.PseudoConsensus 1`, the initial state determined by the all-`true` input
is uniform for `true`. -/
theorem inpN_card_uniform (pn : P ≃ Fin (card P)) (hpc1 : a.PseudoConsensus 1) (hc : card P ≥ 1) :
    a.Uniform (a.start (inpN pn (card P))) true := by
  have h_i := Algorithm.reachable_start (a := a) (inp := inpN pn (card P))
  obtain (h | h | h) := uniform_or_nonUniform hpc1 h_i
  · grind [inpN_card_not_false, h (pn.symm ⟨0, by grind⟩)]
  · exact h
  · grind [inpN_card_not_false, h false]

/-- Assuming `a.PseudoConsensus 1` and there are at least 2 processes, there must exist an input
that gives rise to a non-uniform initial state. This theorem formalizes Lemma 1 of [Volzer2004]. -/
theorem nonUniform_inp (hpc1 : a.PseudoConsensus 1) (hc : card P ≥ 2) :
    ∃ inp : P → Bool, a.NonUniform (a.start inp) := by
  let pn := Fintype.equivFin P
  let uniF (n : ℕ) := ¬ a.Uniform (a.start (inpN pn n)) false
  have h_card : uniF (card P) := by
    grind [Algorithm.Uniform, inpN_card_uniform pn hpc1 (by grind) (pn.symm ⟨0, by grind⟩)]
  have h_uniF : ∃ n, uniF n := ⟨card P, h_card⟩
  classical
  let n := Nat.find h_uniF
  use (inpN pn n)
  have h_n : ¬ a.Uniform (a.start (inpN pn n)) false := by grind
  have h_n0 : 0 < n := by grind [inpN_zero_uniform]
  have h_nc : n ≤ card P := by grind [Nat.find_min' h_uniF]
  have h_n1 : a.Uniform (a.start (inpN pn (n - 1))) false := by grind [Nat.find_min h_uniF]
  have : ¬ a.Uniform (a.start (inpN pn n)) true := by
    obtain ⟨⟨s, h_reach, p, _⟩, _⟩ := h_n1 (pn.symm ⟨n - 1, by grind⟩)
    obtain ⟨s', h_reach', _⟩ := CanReachVia.subset_inp
      (inpN_eqOn_except_singleton pn h_n0 h_nc) h_reach
    have : a.OneSilentDecided (a.start (inpN pn n)) (pn.symm ⟨n - 1, by grind⟩) false := by
      use s', h_reach', p
      grind
    grind [Algorithm.Uniform]
  grind [uniform_or_nonUniform, Algorithm.reachable_start (a := a) (inp := inpN pn n)]

end NonUniformInit

end OnePseudoConsensus

end Cslib.FLP
