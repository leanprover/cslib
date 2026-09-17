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
- `Regex lts i j k`: The regular expression for the executions from state `i` to state `j`,
whose interior states are all under a specific bound `k`

## Main results
- `regex_of_nfa_singleton_start_accept`: NFA with one start state and one accept state have
a matching regular expression
- `language_bddpath_eq_nfa`: A bound that has reached the total number of states no longer
  constrains anything
- `language_bddpath_eq_regex`: `Regex lts i j k` matches the language of the NFA with
start state `i`, accept state `j`, and interior states below `k`

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *InTroduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

@[expose] public section

namespace Cslib.Language

open scoped LTS

variable {Symbol : Type*}

open Automata Acceptor

variable {n : ℕ}

/-- A Bounded Path (`BddPathLTS`) has states `Fin n` and accepts strings (lists of symbols)
starting with state `start` and ending with state `last`
with the interior states less than `bound`. -/
structure BddPathLTS (n : ℕ) (Symbol : Type*) extends LTS (Fin n) Symbol where
  /-- The start state of the path. -/
  start : Fin n
  /-- The last state of the path. -/
  last : Fin n
  /-- The bound for interior states of the path. -/
  bound : ℕ

instance : Acceptor (BddPathLTS n Symbol) Symbol where
  Accepts (p : BddPathLTS n Symbol) (xs : List Symbol) :=
    ∃ ss : List (Fin n),
    p.toLTS.Execution p.start xs p.last ss ∧
    ∀ idx, ∀ _ : 0 < idx ∧ idx + 1 < ss.length, ss[idx] < p.bound
    -- ∀ s ∈ ss.tail.dropLast, s < p.bound

theorem language_bddpath_eq_nfa (lts : LTS (Fin n) Symbol) (i j : Fin n) {k : ℕ} (hk : n ≤ k) :
    language (BddPathLTS.mk lts i j k) =
    language (NA.FinAcc.mk {Tr := lts.Tr, start := {i}} {j}) := by
  simp [language, Accepts]
  grind

open List

section splitLast

/-- Starting at state `i`, the function `splitLast` sends a string to its longest prefix
ending at state `k`. -/
def splitLast {lts : LTS (Fin n) Symbol} {i j : Fin n} {xs : List Symbol} {ss : List (Fin n)}
    (_ : LTS.Execution lts i xs j ss) (k : Fin n) : List Symbol :=
    xs.take (xs.length - (ss.reverse.tail.findIdx (· = k) + 1))

/-- Starting at state `i`, the function `splitLastCompl` sends a string to its shortest suffix
starting at state `k`. -/
def splitLastCompl {lts : LTS (Fin n) Symbol} {i j : Fin n} {xs : List Symbol} {ss : List (Fin n)}
    (_ : LTS.Execution lts i xs j ss) (k : Fin n) : List Symbol :=
    xs.drop (xs.length - (ss.reverse.tail.findIdx (· = k) + 1))

/-- If the execution of `xs` from `i` to `j` has `k` as the largest interior state, then
`splitLast flts i k xs` is a path from `i` to `k` whose interior states are all below `k + 1`. -/
theorem splitLast_mem {lts : LTS (Fin n) Symbol} {i j k : Fin n} {xs : List Symbol}
    {ss : List (Fin n)} (hex : lts.Execution i xs j ss)
    (hbdd : ∀ idx, ∀ _ : 0 < idx ∧ idx + 1 < ss.length, ss[idx] < k.val + 1)
    (hbdd' : ¬(∀ idx, ∀ _ : 0 < idx ∧ idx + 1 < ss.length, ss[idx] < k)) :
    splitLast hex k ∈ language (BddPathLTS.mk lts i k (k + 1)) := by sorry

/-- If the execution of `xs` from `i` to `j` has `k` as the largest interior state, then
`splitLastCompl flts i k xs` is a path from `k` to `j` whose interior states are all below `k`. -/
theorem splitLastCompl_mem {lts : LTS (Fin n) Symbol} {i j k : Fin n} {xs : List Symbol}
    {ss : List (Fin n)} (hex : lts.Execution i xs j ss)
    (hbdd : ∀ idx, ∀ _ : 0 < idx ∧ idx + 1 < ss.length, ss[idx] < k.val + 1)
    (hbdd' : ¬(∀ idx, ∀ _ : 0 < idx ∧ idx + 1 < ss.length, ss[idx] < k)) :
    splitLastCompl hex k ∈ language (BddPathLTS.mk lts k j k) := by sorry

/-- Part of the recursion step of Kleene's algorithm.
An execution from `i` to `j` whose interior states are all at below `k + 1` either
has no interior state equal to `k`, or it splits at its last visit to `k` into
an execution from `i` to `k` with interior states below `k + 1`,
followed by an execution from `k` to `j` with interior states below `k`. -/
theorem language_bddpath_splitLast (lts : LTS (Fin n) Symbol) (i j k : Fin n) :
    language (BddPathLTS.mk lts i j (k + 1)) = language (BddPathLTS.mk lts i j k) +
    (language (BddPathLTS.mk lts i k (k + 1)) * language (BddPathLTS.mk lts k j k)) := by sorry

end splitLast

section splitFirst

/-- Starting at state `i`, the function `splitFirst` sends a string to its shortest prefix
ending at state `k`. -/
def splitFirst {lts : LTS (Fin n) Symbol} {i j : Fin n} {xs : List Symbol} {ss : List (Fin n)}
    (_ : LTS.Execution lts i xs j ss) (k : Fin n) : List Symbol :=
    xs.take (ss.tail.findIdx (· = k) + 1)

/-- Starting at state `i`, the function `splitFirstCompl` sends a string to its longest suffix
starting at state `k`. -/
def splitFirstCompl {lts : LTS (Fin n) Symbol} {i j : Fin n} {xs : List Symbol} {ss : List (Fin n)}
    (_ : LTS.Execution lts i xs j ss) (k : Fin n) : List Symbol :=
    xs.drop (ss.tail.findIdx (· = k) + 1)

theorem splitFirst_mem {lts : LTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    {ss : List (Fin n)} (hex : lts.Execution i xs k ss)
    (hbdd : ∀ idx, ∀ _ : 0 < idx ∧ idx + 1 < ss.length, ss[idx] < k.val + 1) :
    splitFirst hex k ∈ language (BddPathLTS.mk lts i k k) := by
  use ss.take (ss.tail.findIdx (· = k) + 1 + 1)
  by_cases hss : ss.tail = []
  · simp only [splitFirst, hss, findIdx_nil, zero_add, Nat.reduceAdd, length_take, lt_min_iff,
    Order.lt_two_iff, add_le_iff_nonpos_left, nonpos_iff_eq_zero, getElem_take, Fin.val_fin_lt,
    forall_and_index]
    have : ss.length ≤ ss.tail.length + 1 := by rw [List.length_tail]; omega
    grind
  have t : (ss.tail.findIdx (· = k)) < ss.tail.length :=
    findIdx_lt_length.mpr ⟨ss.tail.getLast hss, by grind⟩
  simp only [splitFirst]
  obtain ⟨hspec, hmin⟩ := (List.findIdx_eq t).mp rfl
  constructor
  · convert (LTS.Execution.split hex (ss.tail.findIdx (· = k) + 1) (by grind)).1
    grind
  · simp only [length_take, lt_min_iff, getElem_take, Fin.val_fin_lt]
    intro idx ⟨hidx1, ⟨hidx2, hlength⟩⟩
    have hidx2' : idx - 1 < (ss.tail.findIdx (· = k)) := by grind
    simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hbdd
    apply lt_of_le_of_ne (hbdd idx ⟨hidx1, hlength⟩)
    simpa [Nat.sub_add_cancel hidx1] using hmin (idx - 1) hidx2'

theorem splitFirstCompl_mem {lts : LTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    {ss : List (Fin n)} (hex : lts.Execution i xs k ss)
    (hbdd : ∀ idx, ∀ _ : 0 < idx ∧ idx + 1 < ss.length, ss[idx] < k.val + 1) :
    splitFirstCompl hex k ∈ language (BddPathLTS.mk lts k k (k + 1)) := by
  by_cases hss : ss.tail = []
  · use ss
    have : ss.length ≤ ss.tail.length + 1 := by rw [List.length_tail]; omega
    have : xs = [] := by grind
    simp only [this, splitFirstCompl, drop_nil, Order.lt_add_one_iff, Fin.val_fin_le,
      forall_and_index] at hex ⊢
    grind
  use ss.drop (ss.tail.findIdx (· = k) + 1)
  have t : (ss.tail.findIdx (· = k)) < ss.tail.length :=
    findIdx_lt_length.mpr ⟨ss.tail.getLast hss, by grind⟩
  simp only [splitFirstCompl]
  obtain ⟨hspec, hmin⟩ := (List.findIdx_eq t).mp rfl
  constructor
  · convert (LTS.Execution.split hex (ss.tail.findIdx (· = k) + 1) (by grind)).2
    grind
  · simp only [length_drop, getElem_drop]
    intro idx hidx
    exact hbdd (ss.tail.findIdx (· = k) + 1 + idx) (by grind)

/-- Part of the recursion step of Kleene's algorithm.
An execution from `i` to `j` whose interior states are all below `k + 1` splits upon
first reaching `k`.
The part before is an executionfrom `i` to `k` with interior states below `k`.
The part after is an exection from `k` to `k` with interior states below `k + 1`. -/
theorem language_bddpath_splitFirst (lts : LTS (Fin n) Symbol) (i k : Fin n) :
    language (BddPathLTS.mk lts i k (k + 1)) =
    language (BddPathLTS.mk lts i k k) * language (BddPathLTS.mk lts k k (k + 1)) := by
  ext xs
  rw [Language.mem_mul]
  constructor
  · intro ⟨ss, ⟨hex, hbdd⟩⟩
    use splitFirst hex k, splitFirst_mem hex hbdd,
      splitFirstCompl hex k, splitFirstCompl_mem hex hbdd,
      take_append_drop _ _
  · intro ⟨ys, ⟨⟨ssy, ⟨hyex, hybdd⟩⟩, ⟨zs, ⟨⟨ssz, ⟨hzex, hzbdd⟩⟩, happend⟩⟩⟩⟩
    use ssy ++ ssz.tail
    constructor
    · simpa [happend] using LTS.Execution.comp hyex hzex
    · simp only [Fin.val_fin_lt, forall_and_index, Order.lt_add_one_iff, Fin.val_fin_le,
      length_append, length_tail] at hybdd hzbdd ⊢
      intro idx hidx1 hidx2
      rw [List.getElem_append]
      rcases lt_trichotomy (idx + 1) ssy.length with h | h | h
      · simp only [(by omega : idx < ssy.length), ↓reduceDIte]
        apply le_of_lt
        exact hybdd idx hidx1 h
      · simp only [(by omega : idx < ssy.length), ↓reduceDIte]
        have eq : idx = ssy.length - 1 := by omega
        subst idx
        exact le_of_eq hyex.last
      · have hlength : ¬idx < ssy.length := by omega
        simp only [hlength, ↓reduceDIte, getElem_tail]
        have hidx1' : 0 < idx - ssy.length + 1 := by omega
        have hidx2' : idx - ssy.length + 1 + 1 < ssz.length := by omega
        exact hzbdd (idx - ssy.length + 1) hidx1' hidx2'

end splitFirst

open Computability

section kstar

theorem kstar_eq {α : Type*} (l : Language α) : l∗ = (l - 1)∗ := by
  ext x
  rw [Language.kstar_def_nonempty, Language.mem_kstar]
  exact ⟨fun ⟨S, hx, h⟩ => ⟨S, ⟨hx, fun y ys => h y ys⟩⟩,
    fun ⟨S, ⟨hx, h⟩⟩ => ⟨S, hx, fun y ys => h y ys⟩⟩

/-- Part of the recursion step of Kleene's algorithm.
An execution from `k` to `k` whose interior states are all below `k + 1` is a concatenation of
executions from `k` to `k` whose interior states are all below `k`. -/
theorem language_bddpath_kstar (lts : LTS (Fin n) Symbol) (k : Fin n) :
    language (BddPathLTS.mk lts k k (k + 1)) = (language (BddPathLTS.mk lts k k k))∗ := by sorry

end kstar

open RegularExpression

section Regex

theorem mem_sum_matches'_iff {α : Type*} (L : List (RegularExpression α)) (x : List α) :
    x ∈ (L.sum).matches' ↔ ∃ P ∈ L, x ∈ P.matches' := by
  induction L with
  | nil => simp
  | cons head tail ih =>
  simp only [sum_cons, matches', Language.mem_add, ih, mem_cons, exists_eq_or_imp]

variable [Fintype Symbol]

/-- Regex i j k is the regex for the path from state i to state j passing through states < k.
When k = 0, i = j, the regex is ε union all characters from state i to state i.
When k = 0, i ≠ j, the regex is all characters from state i to state j.
For k + 1, the regex is the union of Regex i j k and
(Regex i k k) (Regex k k k)∗ (Regex k j k). -/
noncomputable def Regex (lts : LTS (Fin n) Symbol) [∀ i j, DecidablePred fun x => lts.Tr i x j]
    (i j : Fin n) : ℕ → RegularExpression Symbol
  | 0 =>
    let chars := (Finset.univ.filter
      (fun x : Symbol ↦ lts.Tr i x j)).toList.map RegularExpression.char
    if i = j then 1 + chars.sum else chars.sum
  | k + 1 =>
    if h : n ≤ k then Regex lts i j k
    else
      let kFin : Fin n := ⟨k, by omega⟩
      Regex lts i j k + Regex lts i kFin k * (Regex lts kFin kFin k).star * Regex lts kFin j k

/-- The correctness of Kleene's algorithm.
`Regex lts i j k` exactly matches the sTrings that have a run starting
at `i`, ending at `j`, and having all interior states below `k`. -/
theorem language_bddpath_eq_regex {k : ℕ} {lts : LTS (Fin n) Symbol}
    [∀ i j, DecidablePred fun x => lts.Tr i x j] {i j : Fin n} :
    language (BddPathLTS.mk lts i j k) = (Regex lts i j k).matches' := by
  induction k generalizing i j with
  | zero =>
    ext xs
    simp only [mem_language, Accepts, Regex] -- not_lt_zero,
    refine ⟨fun ⟨ss, ⟨hex, hbdd⟩⟩ ↦ ?_, fun h ↦  ?_⟩
    · split_ifs with heq
      · simp only [matches', Language.mem_add, mem_sum_matches'_iff]
        sorry
      · rw [mem_sum_matches'_iff]
        sorry
    · split_ifs at h with heq
      · simp only [matches', Language.mem_add, mem_sum_matches'_iff] at h
        sorry
      · rw [mem_sum_matches'_iff] at h
        sorry
  | succ k ih =>
    simp only [Regex]
    split_ifs with hk
    · rw [← ih, language_bddpath_eq_nfa lts i j hk, language_bddpath_eq_nfa lts i j (by omega)]
    rw [language_bddpath_splitLast (k := ⟨k, by omega⟩), language_bddpath_splitFirst,
      language_bddpath_kstar]
    grind [matches'_add, matches'_mul, matches'_star]

theorem language_nfa_eq_regex_of_singleton_start_accept {nfa : NA.FinAcc (Fin n) Symbol}
    [∀ i j, DecidablePred fun x => nfa.toLTS.Tr i x j] {s t : Fin n}
    (hstart : nfa.start = {s}) (haccept : nfa.accept = {t}) :
    language nfa = (Regex nfa.toLTS s t n).matches' := by
  simp [← language_bddpath_eq_regex, language, Accepts, hstart, haccept, LTS.mTr_iff_execution]
  rfl

end Regex

/-- An NFA with exactly one accepting state has a matching regular expression. -/
theorem regex_of_nfa_singleton_start_accept [Finite Symbol] {State : Type*} [Finite State]
    (nfa : NA.FinAcc State Symbol)
    (hstart : ∃ s, nfa.start = {s}) (haccept : ∃ t, nfa.accept = {t}) :
    ∃ r : RegularExpression Symbol, language nfa = r.matches' := by
  have : Fintype State := Fintype.ofFinite State
  let e := Fintype.equivFin State
  obtain ⟨s, hs⟩ := hstart
  obtain ⟨t, ht⟩ := haccept
  set nfa' := NA.FinAcc.mk
    {Tr := fun s1 a s2 => nfa.Tr (e.symm s1) a (e.symm s2), start := {e s}} {e t} with hnfa'
  have language_eq : language nfa = language nfa' := by
    ext xs
    have nfa_eq : nfa'.MTr (e s) xs (e t) ↔ nfa.MTr s xs t := by sorry
    simp only [mem_language, Accepts, hs, Set.mem_singleton_iff, ht, exists_eq_left, hnfa']
    rw [nfa_eq]
  have : Fintype Symbol := Fintype.ofFinite Symbol
  classical
  simpa [language_eq] using
    ⟨_, language_nfa_eq_regex_of_singleton_start_accept (by dsimp) (by dsimp)⟩

end Cslib.Language
