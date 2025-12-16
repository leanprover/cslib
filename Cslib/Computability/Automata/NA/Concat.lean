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
open scoped Run LTS

variable {Symbol State1 State2 : Type*}

open scoped Classical in
/-- `concat na1 na2` starts by running `na1` and then nondeterministically switches to `na2`
by identifying an accepting state of `na1` with an initial state of `na2`. If `na1` accepts the
empty word, it may also start running `na2` from the beginning. Once it starts running `na2`,
it cannot go back to `na1`. -/
def concat (na1 : FinAcc State1 Symbol) (na2 : NA State2 Symbol) : NA (State1 ⊕ State2) Symbol where
    Tr s x t := match s with
      | inl s1 =>
        ∃ t1, na1.Tr s1 x t1 ∧
          ( inl t1 = t ∨ (t1 ∈ na1.accept ∧ ∃ t2 ∈ na2.start, inr t2 = t) )
      | inr s2 =>
        ∃ t2, na2.Tr s2 x t2 ∧ inr t2 = t
    start := inl '' na1.start ∪ if [] ∈ language na1 then inr '' na2.start else ∅

variable {na1 : FinAcc State1 Symbol} {na2 : NA State2 Symbol}

/-- A run of `concat na1 na2` containing at least one `na2` state is the concatenation of
an accepting finite run of `na1` followed by a run of `na2`. -/
theorem concat_run_proj {xs : ωSequence Symbol} {ss : ωSequence (State1 ⊕ State2)}
    (hc : (concat na1 na2).Run xs ss) (hr : ∃ k, (ss k).isRight) :
    ∃ n, xs.take n ∈ language na1 ∧ ∃ ss2, na2.Run (xs.drop n) ss2 ∧ ss.drop n = ss2.map inr := by
  let n := Nat.find hr
  have h1 (k) (h_k : k < n) : ∃ s1, ss (k) = inl s1 :=
    isLeft_iff.mp <| not_isRight.mp <| Nat.find_min hr h_k
  have h2 (k) : ∃ s2, ss (n + k) = inr s2 := by
    induction k
    case zero => exact isRight_iff.mp <| Nat.find_spec hr
    case succ k h_ind =>
      obtain ⟨s2, _⟩ := h_ind
      have := concat.eq_1 na1 na2 ▸ hc.right (n + k)
      grind
  refine ⟨n, ?_, ?_⟩
  · by_cases h_n : n = 0
    · grind [concat]
    · choose ss1 h_ss1 using h1
      have h_0 : 0 < n := by grind
      have h_init : ss1 0 h_0 ∈ na1.start := by grind [concat]
      have h_mtr (k) (h_k : k < n) : na1.MTr (ss1 0 h_0) (xs.take k) (ss1 k h_k) := by
        induction k
        case zero => grind
        case succ k h_ind =>
          have h_tr : na1.Tr (ss1 k (by grind)) (xs k) (ss1 (k + 1) (by grind)) := by
            have := concat.eq_1 na1 na2 ▸ hc.right k
            grind
          have := LTS.MTr.stepR na1.toLTS (h_ind (by grind)) h_tr
          grind
      obtain ⟨t1, _⟩ : ∃ t1, t1 ∈ na1.accept ∧ na1.MTr (ss1 0 h_0) (xs.take n) t1 := by
        obtain ⟨t1, h_tr, _⟩ :
            ∃ t1, na1.Tr (ss1 (n - 1) (by grind)) (xs (n - 1)) t1 ∧ t1 ∈ na1.accept := by
          have := concat.eq_1 na1 na2 ▸ hc.right (n - 1)
          grind
        use t1, by grind
        have := LTS.MTr.stepR na1.toLTS (h_mtr (n - 1) (by grind)) h_tr
        grind
      use ss1 0 h_0, h_init, t1
  · choose ss2 h_ss2 using h2
    refine ⟨ss2, ⟨?_, ?_⟩, by grind⟩
    · by_cases h_n : n = 0
      · grind [concat]
      · obtain ⟨s1, _⟩ := h1 (n - 1) (by grind)
        have := concat.eq_1 na1 na2 ▸ hc.right (n - 1)
        grind
    · intro k
      have := concat.eq_1 na1 na2 ▸ hc.right (n + k)
      grind

/-- Given an accepting finite run of `na1` and a run of `na2`, there exists a run of
`concat na1 na2` that is the concatenation of the two runs. -/
theorem concat_run_exists {xs1 : List Symbol} {xs2 : ωSequence Symbol} {ss2 : ωSequence State2}
    (h1 : xs1 ∈ language na1) (h2 : na2.Run xs2 ss2) :
    ∃ ss, (concat na1 na2).Run (xs1 ++ω xs2) ss ∧ ss.drop xs1.length = ss2.map inr := by
  by_cases h_xs1 : xs1.length = 0
  · obtain ⟨rfl⟩ : xs1 = [] := List.eq_nil_iff_length_eq_zero.mpr h_xs1
    refine ⟨ss2.map inr, ⟨?_, ?_⟩, by simp⟩
    · grind [concat]
    · intro k
      simp only [concat]
      grind
  · obtain ⟨s0, h_s0, t1, h_t1, h_mtr⟩ := h1
    obtain ⟨ss1, _, _, _, _⟩ := LTS.MTr.exists_states h_mtr
    let ss := (ss1.map inl).take xs1.length ++ω ss2.map inr
    have h_ss1 (k) (_ : k < xs1.length) : ss k = inl (ss1[k]) := by
      simp (disch := grind) [ss, get_append_left]
    have h_ss2 (k) (_ : xs1.length ≤ k) : ss k = inr (ss2 (k - xs1.length)) := by
      simp (disch := grind) [ss, get_append_right']
    have h_ss2' (k) (_ : k = xs1.length) : ss k = inr (ss2 0) := by
      simp (disch := grind) [ss, get_append_right']
    have h_xs1 (k) (_ : k < xs1.length) : (xs1 ++ω xs2) k = xs1[k] := by
      simp (disch := grind) [get_append_left]
    have h_xs2 (k) (_ : xs1.length ≤ k) : (xs1 ++ω xs2) k = xs2 (k - xs1.length) := by
      simp (disch := grind) [get_append_right']
    use ss, ⟨?_, ?_⟩, by simp (disch := grind) [ss, drop_append_of_le_length]
    · suffices ss 0 = inl ss1[0] by grind [concat]
      simp (disch := grind) [ss, get_append_left]
    · intro k
      by_cases h_k : k < xs1.length
      · by_cases h_k' : k = xs1.length - 1
        · have := h_xs1 k (by grind)
          have := h_ss1 k (by grind)
          have := h_ss2' (k + 1) (by grind)
          grind [concat]
        · have := h_xs1 k (by grind)
          have := h_ss1 k (by grind)
          have := h_ss1 (k + 1) (by grind)
          grind [concat]
      · have := h_xs2 k (by grind)
        have := h_ss2 k (by grind)
        have := h_ss2 (k + 1) (by grind)
        have := show k + 1 - xs1.length = k - xs1.length + 1 by grind
        grind [concat]

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
    have h_ex2 : ∃ k, (ss k).isRight := by
      obtain ⟨k, h_k⟩ := Frequently.exists h_acc
      grind
    obtain ⟨n, h_acc1, ss2, h_run2, h_map2⟩ := concat_run_proj h_run h_ex2
    use xs.take n, h_acc1, xs.drop n, ?_, by simp
    use ss2, h_run2
    have := (drop_frequently_iff_frequently n).mpr h_acc
    grind
  · rintro ⟨xs1, h_xs1, xs2, ⟨ss2, h_run2, h_acc2⟩, rfl⟩
    obtain ⟨ss, h_run, h_map⟩ := concat_run_exists h_xs1 h_run2
    use ss, h_run
    apply (drop_frequently_iff_frequently xs1.length).mp
    grind

end Buchi

end Cslib.Automata.NA
