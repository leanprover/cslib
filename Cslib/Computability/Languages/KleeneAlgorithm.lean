/-
Copyright (c) 2026 Brooke Gill and Chi-Yun Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brooke Gill, Chi-Yun Hsu
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.NA.Basic
public import Mathlib.Computability.Language
public import Mathlib.Computability.RegularExpressions

/-!
# Kleene's Algorithm

Kleene's algorithm constructs a regular expresssion by induction on a bound `k` that restricts
which interior states an execution may pass through.
It is used to prove `Cslib.Language.IsRegular.iff_regex`, that every language accepted by
a DFA comprised of finite states is the language of a regular expression.
We implement Kleene's algorithm for the more general case of an NFA instead of DFA,
since `Execution` is developed for `LTS` but not `FLTS`
The special case where the NFA has only one start state and one accept state is proved in
`regex_of_nfa_singleton_start_accept` in this file.

## Main definitions
- `BddPathLTS`: A labelled transition system containing a start state, last state, and
a specific bound on all interior states
- `Regex lts s t r`: The regular expression for the executions from state `s` to state `t`,
whose interior states are all under a specific bound `r`

## Main results
- `regex_of_nfa_singleton_start_accept`: NFA with one start state and one accept state have
a matching regular expression
- `language_bddpath_eq_nfa`: A bound that has reached the total number of states no longer
  constrains anything
- `language_bddpath_eq_regex`: `Regex lts s t r` matches the language of the NFA with
start state `s`, accept state `t`, and interior states below `r`

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

@[expose] public section

namespace List

variable {α : Type*}

def AllButFirstLast (p : α → Bool) (as : List α) : Prop := as.tail.dropLast.all p

theorem all_iff_getElem (p : α → Bool) (as : List α) :
    as.all p ↔ ∀ i (_ : i < as.length), p as[i] = true := by
  simp only [all_eq_true]
  refine ⟨fun h i hi ↦ h as[i] (getElem_mem hi), fun h x hx ↦ ?_⟩
  obtain ⟨i, hi_len, rfl⟩ := getElem_of_mem hx
  exact h i hi_len

theorem allButFirstLast_iff_getElem (p : α → Bool) (as : List α) :
    as.AllButFirstLast p ↔ ∀ i (_ : i < as.length - 1 - 1), p as[i + 1] = true := by
  rw [AllButFirstLast, all_iff_getElem]
  simp

theorem allButFirstLast_reverse (p : α → Bool) (as : List α) :
    as.AllButFirstLast p ↔ as.reverse.AllButFirstLast p := by
  simp only [AllButFirstLast]
  rw [← all_reverse, ← tail_reverse, ← dropLast_reverse, tail_dropLast]

theorem allButFirstLast_iff_getElem_reverse (p : α → Bool) (as : List α) :
    as.AllButFirstLast p ↔
    ∀ i (_ : i < as.length - 1 - 1), p as[as.length - 1 - (i + 1)] = true := by
  rw [allButFirstLast_reverse, allButFirstLast_iff_getElem]
  simp

theorem allButFirstLast_take {p : α → Bool} {as : List α} (h : as.AllButFirstLast p)
    (n : ℕ) : (as.take n).AllButFirstLast p := by
  simp only [AllButFirstLast, all_iff_getElem] at h ⊢
  intro i hi_len
  simp only [length_dropLast, length_tail, length_take] at hi_len
  simp only [length_dropLast, length_tail, getElem_dropLast, getElem_tail] at h
  simp only [getElem_dropLast, getElem_tail, getElem_take]
  exact h i (by omega)

/-- The index of the first element in a list that satisfies a predicate,
excluding the first and last element. -/
def findIdxButFirstLast? (p : α → Bool) (as : List α) : Option ℕ :=
  (as.tail.dropLast.findIdx? p).map (· + 1)

theorem findIdxButFirstLast?_isSome (p : α → Bool) (as : List α) :
    (as.findIdxButFirstLast? p).isSome ↔ (∃ x ∈ as.tail.dropLast, p x = true) := by
  simp [findIdxButFirstLast?]

theorem findIdxButFirstLast?_index {p : α → Bool} {as : List α}
    (h : (as.findIdxButFirstLast? p).isSome) : ∃ i, as.findIdxButFirstLast? p = some (i + 1) := by
  rw [findIdxButFirstLast?, Option.isSome_map, Option.isSome_iff_exists] at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by simpa [findIdxButFirstLast?] using hi⟩

theorem findIdxButFirstLast?_eq {p : α → Bool} {as : List α} {i : ℕ} :
    as.findIdxButFirstLast? p = some (i + 1) ↔
      ∃ _ : i < as.length - 1 - 1, (p as[i + 1] = true ∧
        ∀ (j : ℕ) (_ : j < i), p as[j + 1] = false) := by
  simp [findIdxButFirstLast?, findIdx?_eq_some_iff_getElem]

/-- The index of the last element in a list that satisfies a predicate,
excluding the first and last element. -/
def findIdxButFirstLastRev? (p : α → Bool) (as : List α) : Option ℕ :=
  (as.reverse.findIdxButFirstLast? p).map (as.length - 1 - ·)

theorem findIdxButFirstLastRev?_isSome (p : α → Bool) (as : List α) :
    (as.findIdxButFirstLastRev? p).isSome ↔ (∃ x ∈ as.tail.dropLast, p x = true) := by
  simp [findIdxButFirstLastRev?, findIdxButFirstLast?_isSome, tail_dropLast]

theorem findIdxButFirstLastRev?_index {p : α → Bool} {as : List α}
    (h : (as.findIdxButFirstLastRev? p).isSome) :
    ∃ i, as.findIdxButFirstLastRev? p = some (as.length - 1 - (i + 1)) := by
  rw [findIdxButFirstLastRev?, Option.isSome_map] at h
  obtain ⟨i , hi⟩ := findIdxButFirstLast?_index h
  exact ⟨i, by simp [findIdxButFirstLastRev?, hi]⟩

theorem findIdxButFirstLastRev?_eq {p : α → Bool} {as : List α} {i : ℕ} :
    as.findIdxButFirstLastRev? p = some (as.length - 1 - (i + 1)) ↔
      ∃ _ : i < as.length - 1 - 1, (p as[as.length - 1 - (i + 1)] = true ∧
        ∀ (j : ℕ) (_ : j < i), p as[as.length - 1 - (j + 1)] = false) := by
  simp only [findIdxButFirstLastRev?, Option.map_eq_some_iff]
  refine ⟨fun ⟨a, ha, hai⟩ ↦ ?_, fun ⟨hi_len, hi_spec, hi_min⟩ ↦ ?_⟩
  · obtain ⟨i', hi'⟩ := findIdxButFirstLast?_index (Option.isSome_iff_exists.mpr ⟨a, ha⟩)
    obtain ⟨hi'_len, hi'_spec, hi'_min⟩ := findIdxButFirstLast?_eq.mp hi'
    simp only [length_reverse, getElem_reverse] at hi'_len hi'_spec hi'_min
    have hai' : a = i' + 1 := by simpa [ha] using hi'
    have hi'i : i' = i := by omega
    simp only [hi'i] at hi'_len hi'_spec hi'_min
    exact ⟨hi'_len, hi'_spec, hi'_min⟩
  · refine ⟨i + 1, findIdxButFirstLast?_eq.mpr ?_, rfl⟩
    simpa using ⟨hi_len, hi_spec, hi_min⟩

end List

variable {Symbol : Type*} {n : ℕ}

open List

namespace Cslib.LTS

def BddExec (lts : LTS (Fin n) Symbol) (start : Fin n) (xs : List Symbol) (last : Fin n)
    (ss : List (Fin n)) (bound : ℕ) : Prop :=
  lts.Execution start xs last ss ∧ ss.AllButFirstLast (fun (s : Fin n) ↦ s < bound)

def BddLang (lts : LTS (Fin n) Symbol) (start last : Fin n) (bound : ℕ) : Language Symbol :=
  { xs | ∃ ss, lts.BddExec start xs last ss bound }

open Automata Acceptor

theorem bddLang_eq_language_nfa (lts : LTS (Fin n) Symbol) (s t : Fin n) {r : ℕ} (hk : n ≤ r) :
    lts.BddLang s t r =
      language (NA.FinAcc.mk {Tr := lts.Tr, start := {s}} {t}) := by
  ext xs
  simp only [BddLang, mem_language, Accepts, Set.mem_singleton_iff]
  refine ⟨fun ⟨ss, hex, hbdd⟩ ↦ by simpa using hex.to_mTr, fun ⟨s', hs', t', ht', hmtr⟩ ↦ ?_⟩
  rw [hs', ht'] at hmtr
  obtain ⟨ss, hex⟩ := mTr_iff_execution.mp hmtr
  exact ⟨ss, hex, by grind [AllButFirstLast]⟩

section splitFirst

def splitFirstTake (xs : List Symbol) (ss : List (Fin n)) (r : Fin n) : List Symbol :=
  match ss.findIdxButFirstLast? (· = r) with
  | none => []
  | some i => xs.take i


def splitFirstDrop (xs : List Symbol) (ss : List (Fin n)) (r : Fin n) : List Symbol :=
  match ss.findIdxButFirstLast? (· = r) with
  | none => xs
  | some i => xs.drop i

theorem splitFirst_mem {lts : LTS (Fin n) Symbol} {s t r : Fin n} {xs : List Symbol}
    {ss : List (Fin n)} (hex : lts.Execution s xs t ss)
    (hbdd : ss.AllButFirstLast (· ≤ r)) (hbdd' : ¬ss.AllButFirstLast (· < r)) :
    splitFirstTake xs ss r ∈ lts.BddLang s r r ∧
      splitFirstDrop xs ss r ∈ lts.BddLang r t (r + 1) := by
  have hisSome : (ss.findIdxButFirstLast? (· = r)).isSome := by
    rw [ss.findIdxButFirstLast?_isSome (· = r)]
    by_contra! hne
    simp only [ne_eq, decide_eq_true_eq] at hne
    simp only [AllButFirstLast, all_eq_true, decide_eq_true_eq, not_forall] at hbdd hbdd'
    obtain ⟨u, hu, hnlt⟩ := hbdd'
    have hlt := lt_of_le_of_ne (hbdd u hu) (hne u hu)
    contradiction
  obtain ⟨i, hi⟩ := findIdxButFirstLast?_index hisSome
  obtain ⟨hi_len, hi_spec, hi_min⟩ := findIdxButFirstLast?_eq.mp hi
  have hi_len' : i + 1 ≤ xs.length := by rw [hex.length] at hi_len; omega
  rw [decide_eq_true_eq] at hi_spec
  constructor
  · use ss.take (i + 1 + 1)
    refine ⟨by simpa [splitFirstTake, hi, hi_spec] using (hex.split (i + 1) hi_len').1, ?_⟩
    rw [allButFirstLast_iff_getElem] at hbdd ⊢
    intro j hj
    rw [length_take] at hj
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hbdd hi_min
    simpa using lt_of_le_of_ne (hbdd j (by omega)) (hi_min j (by omega))
  · use ss.drop (i + 1)
    refine ⟨by simpa [splitFirstDrop, hi, hi_spec] using (hex.split (i + 1) hi_len').2, ?_⟩
    rw [allButFirstLast_iff_getElem] at hbdd ⊢
    intro j hj
    rw [length_drop] at hj
    simpa [← add_assoc] using hbdd (i + 1 + j) (by omega)

theorem bddLang_splitFirst (lts : LTS (Fin n) Symbol) (s t r : Fin n) :
    lts.BddLang s t (r + 1) = lts.BddLang s t r + lts.BddLang s r r * lts.BddLang r t (r + 1) := by
  ext xs
  rw [Language.mem_add, Language.mem_mul]
  constructor
  · intro ⟨ss, hex, hbdd⟩
    by_cases hbdd' : AllButFirstLast (· < r) ss
    · exact Or.inl ⟨ss, hex, hbdd'⟩
    right
    simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hbdd
    use splitFirstTake xs ss r, (splitFirst_mem hex hbdd hbdd').1,
      splitFirstDrop xs ss r, (splitFirst_mem hex hbdd hbdd').2
    cases h : ss.findIdxButFirstLast? (· = r) <;>
    simp_all [splitFirstTake, splitFirstDrop]
  · rintro (h_left | ⟨ys, ⟨ssy, hyex, hybdd⟩, ⟨zs, ⟨ssz, hzex, hzbdd⟩, happend⟩⟩)
    · obtain ⟨ss, hex, hbdd⟩ := h_left
      refine ⟨ss, hex, ?_⟩
      rw [allButFirstLast_iff_getElem] at hbdd ⊢
      intro j hj
      simp only [Order.lt_add_one_iff, Fin.val_fin_le, decide_eq_true_eq]
      exact le_of_lt (by simpa using hbdd j hj)
    · refine ⟨ssy ++ ssz.tail, by simpa [happend] using hyex.comp hzex, ?_⟩
      rw [allButFirstLast_iff_getElem] at hybdd hzbdd ⊢
      simp only [Fin.val_fin_lt, decide_eq_true_eq, Order.lt_add_one_iff, Fin.val_fin_le,
        length_append, length_tail] at hybdd hzbdd ⊢
      intro i hi
      rw [List.getElem_append]
      rcases lt_trichotomy (i + 1) (ssy.length - 1) with h | h | h
      · simp only [(by omega : i + 1 < ssy.length), ↓reduceDIte]
        exact le_of_lt (hybdd i (by omega))
      · simp only [(by omega : i + 1 < ssy.length), ↓reduceDIte]
        apply le_of_eq
        simpa [(by omega : i + 1 = ssy.length - 1)] using hyex.last
      · have hlen : ¬i + 1 < ssy.length := by omega
        simp only [hlen, ↓reduceDIte, getElem_tail]
        exact hzbdd (i + 1 - ssy.length) (by omega)

end splitFirst

section splitLast

def splitLastTake (xs : List Symbol) (ss : List (Fin n)) (r : Fin n) : List Symbol :=
  match ss.findIdxButFirstLastRev? (· = r) with
  | none => []
  | some i => xs.take i

def splitLastDrop (xs : List Symbol) (ss : List (Fin n)) (r : Fin n) : List Symbol :=
  match ss.findIdxButFirstLastRev? (· = r) with
  | none => xs
  | some i => xs.drop i

theorem splitLast_mem {lts : LTS (Fin n) Symbol} {t r : Fin n} {xs : List Symbol}
    {ss : List (Fin n)} (hex : lts.Execution r xs t ss)
    (hbdd : ss.AllButFirstLast (· ≤ r)) :
    splitLastTake xs ss r ∈ lts.BddLang r r (r + 1) ∧
      splitLastDrop xs ss r ∈ lts.BddLang r t r := by
  cases h : ss.findIdxButFirstLastRev? (· = r) with
  | none =>
  simp only [splitLastTake, splitLastDrop, h, BddLang, BddExec]
  constructor
  · exact ⟨[r], Execution.refl lts r, by simp [AllButFirstLast]⟩
  · use ss
    refine ⟨hex, ?_⟩
    sorry
  | some a =>
  obtain ⟨i, hi⟩ := findIdxButFirstLastRev?_index (Option.isSome_iff_exists.mpr ⟨a, h⟩)
  obtain ⟨hi_len, hi_spec, hi_min⟩ := findIdxButFirstLastRev?_eq.mp hi
  have hi_len' : ss.length - 1 - (i + 1) ≤ xs.length := by rw [hex.length] at hi_len ⊢; omega
  rw [decide_eq_true_eq] at hi_spec
  constructor
  · use ss.take (ss.length - 1 - (i + 1) + 1)
    refine ⟨by simpa [splitLastTake, hi, hi_spec]
      using (hex.split (ss.length - 1 - (i + 1)) hi_len').1, ?_⟩
    rw [allButFirstLast_iff_getElem] at hbdd ⊢
    intro j hj
    rw [length_take] at hj
    simpa using hbdd j (by omega)
  · use ss.drop (ss.length - 1 - (i + 1))
    refine ⟨by simpa [splitLastDrop, hi, hi_spec]
      using (hex.split (ss.length - 1 - (i + 1)) hi_len').2, ?_⟩
    have drop_eq_reverse_take_reverse (n : ℕ) :
        ss.drop n = (ss.reverse.take (ss.length - n)).reverse := by
      simp [take_reverse]; omega
    rw [drop_eq_reverse_take_reverse]
    rw [← allButFirstLast_reverse, allButFirstLast_iff_getElem]
    intro j hj
    rw [length_take] at hj
    rw [allButFirstLast_iff_getElem_reverse] at hbdd
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hbdd hi_min
    simpa using lt_of_le_of_ne (hbdd j (by omega)) (hi_min j (by omega))

end splitLast

end Cslib.LTS
