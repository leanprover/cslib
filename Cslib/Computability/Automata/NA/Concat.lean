/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Total
public import Cslib.Foundations.Data.OmegaSequence.Temporal

@[expose] public section

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
theorem concat_run_proj {xs : ωSequence Symbol} {ss : ωSequence (State1 ⊕ State2)} {k : ℕ}
    (hc : (concat na1 na2).Run xs ss) (hr : (ss k).isRight) :
    ∃ n, n ≤ k ∧ xs.take n ∈ language na1 ∧
    ∃ ss2, na2.Run (xs.drop n) ss2 ∧ ss.drop n = ss2.map inr := by
  have hr' : ∃ k, (ss k).isRight := by grind
  let n := Nat.find hr'
  have hl (k) (h_k : k < n) := not_isRight.mp <| Nat.find_min hr' h_k
  refine ⟨n, by grind, ?_, ?_⟩
  · by_cases h_n : n = 0
    · grind [concat_start_right]
    · grind [concat_run_left_right]
  · exact concat_run_right hc n hl (Nat.find_spec hr')

/-- Given an accepting finite run of `na1` and a run of `na2`, there exists a run of
`concat na1 na2` that is the concatenation of the two runs. -/
theorem concat_run_exists {xs1 : List Symbol} {xs2 : ωSequence Symbol} {ss2 : ωSequence State2}
    (h1 : xs1 ∈ language na1) (h2 : na2.Run xs2 ss2) :
    ∃ ss, (concat na1 na2).Run (xs1 ++ω xs2) ss ∧ ss.drop xs1.length = ss2.map inr := by
  by_cases h_xs1 : xs1.length = 0
  · obtain ⟨rfl⟩ : xs1 = [] := List.eq_nil_iff_length_eq_zero.mpr h_xs1
    refine ⟨ss2.map inr, by simp only [concat]; grind [Run, LTS.ωTr], by simp⟩
  · obtain ⟨s0, _, _, _, h_mtr⟩ := h1
    obtain ⟨ss1, _, _, _, _⟩ := LTS.mTr_isExecution h_mtr
    let ss := (ss1.map inl).take xs1.length ++ω ss2.map inr
    refine ⟨ss, Run.mk ?_ ?_, ?_⟩
    · grind [concat, get_append_left]
    · have (k) (h_k : ¬ k < xs1.length) : k + 1 - xs1.length = k - xs1.length + 1 := by grind
      simp only [concat]
      grind [Run, LTS.ωTr, get_append_right', get_append_left, LTS.IsExecution]
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
    obtain ⟨k, h_k⟩ : ∃ k, (ss k).isRight := by grind [Frequently.exists h_acc]
    obtain ⟨n, _, h_acc1, ss2, h_run2, h_map2⟩ := concat_run_proj h_run h_k
    use xs.take n, h_acc1, xs.drop n, ?_, by simp
    use ss2, h_run2
    grind [(drop_frequently_iff_frequently n).mpr h_acc]
  · rintro ⟨xs1, h_xs1, xs2, ⟨ss2, h_run2, h_acc2⟩, rfl⟩
    obtain ⟨ss, h_run, h_map⟩ := concat_run_exists h_xs1 h_run2
    use ss, h_run
    apply (drop_frequently_iff_frequently xs1.length).mp
    grind

end Buchi

namespace FinAcc

/-- `finConcat na1 na2` is the concatenation of the "totalized" versions of `na1` and `na2`. -/
def finConcat (na1 : FinAcc State1 Symbol) (na2 : FinAcc State2 Symbol)
  : NA ((State1 ⊕ Unit) ⊕ (State2 ⊕ Unit)) Symbol :=
  concat ⟨na1.totalize, inl '' na1.accept⟩ na2.totalize

variable {na1 : FinAcc State1 Symbol} {na2 : FinAcc State2 Symbol}

/-- `finConcat na1 na2` is total. -/
instance : (finConcat na1 na2).Total where
  total s x := match s with
    | inl _ => ⟨inl (inr ()), by grind [finConcat, concat, NA.totalize, LTS.totalize]⟩
    | inr _ => ⟨inr (inr ()), by grind [finConcat, concat, NA.totalize, LTS.totalize]⟩

/-- `finConcat na1 na2` accepts the concatenation of the languages of `na1` and `na2`. -/
theorem finConcat_language_eq [Inhabited Symbol] :
    language (FinAcc.mk (finConcat na1 na2) (inr '' (inl '' na2.accept))) =
    language na1 * language na2 := by
  ext xl
  constructor
  · rintro ⟨s, _, t, h_acc, h_mtr⟩
    obtain ⟨xs, ss, h_ωtr, rfl, rfl⟩ := LTS.Total.mTr_ωTr h_mtr
    have hc : (finConcat na1 na2).Run (xl ++ω xs) ss := by grind [Run]
    have hr : (ss xl.length).isRight := by grind
    obtain ⟨n, _⟩ := concat_run_proj hc hr
    refine ⟨xl.take n, ?_, xl.drop n, ?_, ?_⟩
    · grind [totalize_language_eq, take_append_of_le_length]
    · have : ss xl.length = (ss.drop n) (xl.length - n) := by grind
      grind [drop_append_of_le_length, take_append_of_le_length, totalize_run_mtr]
    · exact xl.take_append_drop n
  · rintro ⟨xl1, h_xl1, xl2, h_xl2, rfl⟩
    rw [← totalize_language_eq] at h_xl1
    obtain ⟨_, h_s2, _, _, h_mtr2⟩ := h_xl2
    obtain ⟨_, _, h_run2, _, _⟩ := totalize_mtr_run h_s2 h_mtr2
    obtain ⟨ss, ⟨_, h_ωtr⟩, _⟩ := concat_run_exists h_xl1 h_run2
    grind [
      finConcat, List.length_append, take_append_of_le_length,
      extract_eq_drop_take, =_ append_append_ωSequence, get_drop xl2.length xl1.length ss,
      LTS.ωTr_mTr h_ωtr (zero_le (xl1.length + xl2.length))
    ]

end FinAcc

end Cslib.Automata.NA
