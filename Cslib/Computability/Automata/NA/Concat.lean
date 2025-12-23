/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.NA.Basic
import Cslib.Foundations.Data.OmegaSequence.Temporal

/-! # Concatenation of nondeterministic automata. -/

namespace Cslib.Automata.NA

open Sum ωSequence Acceptor

variable {Symbol State1 State2 : Type*}

open scoped Classical in
/-- `concat na1 na2` starts by running `na1` and then nondeterministically switches to `na2`
by identifying an accepting state of `na1` with an initial state of `na2`. If `na1` accepts the
empty word, it may also start running `na2` from the beginning. Once it starts running `na2`,
it cannot go back to `na1`. -/
def concat (na1 : FinAcc State1 Symbol) (na2 : NA State2 Symbol) : NA (State1 ⊕ State2) Symbol where
    Tr s x t := match s, t with
      | inl s1, inl t1 => na1.Tr s1 x t1
      | inl s1, inr t2 => ∃ t1, na1.Tr s1 x t1 ∧ t1 ∈ na1.accept ∧ t2 ∈ na2.start
      | inr s2, inr t2 => na2.Tr s2 x t2
      | inr _, inl _ => False
    start := inl '' na1.start ∪ if [] ∈ language na1 then inr '' na2.start else ∅

variable {na1 : FinAcc State1 Symbol} {na2 : NA State2 Symbol}

lemma concat_start_right {xs : ωSequence Symbol} {ss : ωSequence (State1 ⊕ State2)}
    (hc : (concat na1 na2).Run xs ss) (hr : (ss 0).isRight) : [] ∈ language na1 := by
  grind [concat, hc.start]

lemma concat_run_left {xs : ωSequence Symbol} {ss : ωSequence (State1 ⊕ State2)}
    (hc : (concat na1 na2).Run xs ss) (n : ℕ) (hl : ∀ k ≤ n, (ss k).isLeft) :
    ∃ s1 t1, na1.MTr s1 (xs.take n) t1 ∧ s1 ∈ na1.start ∧ ss 0 = inl s1 ∧ ss n = inl t1 := by
  obtain ⟨s1, _⟩ : ∃ s1, s1 ∈ na1.start ∧ ss 0 = inl s1 := by grind [concat, hc.start]
  use s1
  induction n
  case zero => grind [LTS.MTr]
  case succ n h_ind =>
    obtain ⟨t1, h_mtr, _⟩ := h_ind (by grind)
    obtain ⟨t1', h_tr, _⟩ : ∃ t1', na1.Tr t1 (xs n) t1' ∧ ss (n + 1) = inl t1' := by
      grind [concat, hc.trans n]
    use t1'
    grind [LTS.MTr.stepR na1.toLTS h_mtr h_tr]

lemma concat_run_left_right {xs : ωSequence Symbol} {ss : ωSequence (State1 ⊕ State2)}
    (hc : (concat na1 na2).Run xs ss) (n : ℕ) (hn : 0 < n)
    (hl : ∀ k < n, (ss k).isLeft) (hr : (ss n).isRight) : (xs.take n) ∈ language na1 := by
  obtain ⟨s1, t1, h_mtr, _⟩ := concat_run_left hc (n - 1) (by grind)
  obtain ⟨t1', h_tr, _⟩ : ∃ t1', na1.Tr t1 (xs (n - 1)) t1' ∧ t1' ∈ na1.accept := by
    grind [concat, hc.trans (n - 1)]
  use s1, by grind, t1', by grind
  grind [LTS.MTr.stepR na1.toLTS h_mtr h_tr]

lemma concat_run_right {xs : ωSequence Symbol} {ss : ωSequence (State1 ⊕ State2)}
    (hc : (concat na1 na2).Run xs ss) (n : ℕ) (hl : ∀ k < n, (ss k).isLeft) (hr : (ss n).isRight) :
    ∃ ss2, na2.Run (xs.drop n) ss2 ∧ ss.drop n = ss2.map inr := by
  have h2 k : ∃ s2, ss (n + k) = inr s2 := by
     induction k
     case zero => grind [isRight_iff]
     case succ k h_ind => grind [concat, hc.trans (n + k)]
  choose ss2 h_ss2 using h2
  refine ⟨ss2, Run.mk ?_ ?_, by grind⟩
  · by_cases h_n : n = 0
    · grind [concat, hc.start]
    · grind [concat, hc.trans (n - 1)]
  · intro k
    grind [concat, hc.trans (n + k)]

/-- A run of `concat na1 na2` containing at least one `na2` state is the concatenation of
an accepting finite run of `na1` followed by a run of `na2`. -/
theorem concat_run_proj {xs : ωSequence Symbol} {ss : ωSequence (State1 ⊕ State2)}
    (hc : (concat na1 na2).Run xs ss) (hr : ∃ k, (ss k).isRight) :
    ∃ n, xs.take n ∈ language na1 ∧ ∃ ss2, na2.Run (xs.drop n) ss2 ∧ ss.drop n = ss2.map inr := by
  let n := Nat.find hr
  have hl (k) (h_k : k < n) := not_isRight.mp <| Nat.find_min hr h_k
  refine ⟨n, ?_, ?_⟩
  · by_cases h_n : n = 0
    · grind [concat_start_right]
    · grind [concat_run_left_right]
  · have hr : (ss n).isRight := Nat.find_spec hr
    grind [concat_run_right hc n hl hr]

/-- Given an accepting finite run of `na1` and a run of `na2`, there exists a run of
`concat na1 na2` that is the concatenation of the two runs. -/
theorem concat_run_exists {xs1 : List Symbol} {xs2 : ωSequence Symbol} {ss2 : ωSequence State2}
    (h1 : xs1 ∈ language na1) (h2 : na2.Run xs2 ss2) :
    ∃ ss, (concat na1 na2).Run (xs1 ++ω xs2) ss ∧ ss.drop xs1.length = ss2.map inr := by
  by_cases h_xs1 : xs1.length = 0
  · obtain ⟨rfl⟩ : xs1 = [] := List.eq_nil_iff_length_eq_zero.mpr h_xs1
    refine ⟨ss2.map inr, by simp only [concat]; grind [Run, LTS.ωTr], by simp⟩
  · obtain ⟨s0, _, _, _, h_mtr⟩ := h1
    obtain ⟨ss1, _, _, _, _⟩ := LTS.MTr.exists_states h_mtr
    let ss := (ss1.map inl).take xs1.length ++ω ss2.map inr
    refine ⟨ss, Run.mk ?_ ?_, ?_⟩
    · grind [concat, get_append_left]
    · have (k) (h_k : ¬ k < xs1.length) : k + 1 - xs1.length = k - xs1.length + 1 := by grind
      simp only [concat]
      grind [Run, LTS.ωTr, get_append_right', get_append_left]
    · grind [drop_append_of_le_length]

namespace Buchi

open ωAcceptor Filter

/-- The Buchi automaton formed from `concat na1 na2` accepts the ω-language that is
the concatenation of the language of `na1` and the ω-language of `na2`. -/
@[simp]
theorem concat_language_eq {acc2 : Set State2} :
    language (Buchi.mk (concat na1 na2) (inr '' acc2)) =
    language na1 * language (Buchi.mk na2 acc2) := by
  ext xs
  constructor
  · rintro ⟨ss, h_run, h_acc⟩
    have h_ex2 : ∃ k, (ss k).isRight := by grind [Frequently.exists h_acc]
    obtain ⟨n, h_acc1, ss2, h_run2, h_map2⟩ := concat_run_proj h_run h_ex2
    use xs.take n, h_acc1, xs.drop n, ?_, by simp
    use ss2, h_run2
    grind [(drop_frequently_iff_frequently n).mpr h_acc]
  · rintro ⟨xs1, h_xs1, xs2, ⟨ss2, h_run2, h_acc2⟩, rfl⟩
    obtain ⟨ss, h_run, h_map⟩ := concat_run_exists h_xs1 h_run2
    use ss, h_run
    apply (drop_frequently_iff_frequently xs1.length).mp
    grind

end Buchi

end Cslib.Automata.NA
