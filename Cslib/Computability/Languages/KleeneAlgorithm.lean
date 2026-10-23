/-
Copyright (c) 2026 Brooke Gill and Chi-Yun Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brooke Gill, Chi-Yun Hsu
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Languages.RegularExpressions
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Kleene's Algorithm

Kleene's algorithm constructs a regular expression by induction on a bound that restricts
which interior states an execution may pass through.
It is used to prove a direction of `Cslib.Language.IsRegular.iff_regex`, that
every language accepted by a DFA comprised of finite states is the language of a regular expression.
We implement Kleene's algorithm for the more general case of an NFA instead of DFA,
since `Execution` is developed for `LTS` but not `FLTS`.
The main theorem is `NA.FinAcc.nfa_eq_regex`.

## Main definitions
- `LTS.bddLang start last bound`: The language of finite words that are accepted by an execution
of an LTS with state type `Fin n`, where the start state is `start`, the last state is `last`,
and all states of the execution except for the first and last are less than `bound`.
- `LTS.regex s t r`: The regular expression for the executions of an LTS with state type `Fin n`
from state `s` to state `t`, whose interior states are all under the bound `r`.

## Main results
- `NA.FinAcc.nfa_eq_regex`: Any NFA has a matching regular expression.
- `LTS.bddLang_eq_nfa`: `LTS.bddLang` is equal to the language of an NFA
when `bound` is greater than or equal to the total number of states.
- `LTS.bddLang_eq_regex`: `LTS.regex s t r` matches the language `LTS.bddLang s t r`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

@[expose] public section

namespace List

variable {α : Type*}

/-- All but the first and last elements of the list `as` satisfy the predicate `p`. -/
def AllButFirstLast (p : α → Bool) (as : List α) : Prop :=
  ∀ x, x ∈ as.tail.dropLast → p x

theorem allButFirstLast_iff_getElem (p : α → Bool) (as : List α) :
    as.AllButFirstLast p ↔ ∀ i (_ : 0 < i ∧ i < as.length - 1), p as[i] := by
  simp only [AllButFirstLast, forall_mem_iff_getElem, length_dropLast, length_tail,
    getElem_dropLast, getElem_tail, forall_and_index]
  constructor
  · intro h i hi_pos hi_len
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi_pos)
    simpa [ha] using h a (by lia)
  · intro h a ha_len
    exact h (a + 1) (by lia) (by lia)

theorem allButFirstLast_imp {p q : α → Bool} {as : List α} (h : ∀ x, p x → q x)
    (hp : as.AllButFirstLast p) : as.AllButFirstLast q :=
  fun x hx ↦ h x <| hp x hx

theorem allButFirstLast_append {p : α → Bool} {as bs : List α} (hlen : 0 < as.length)
    (ha_last : p as[as.length - 1]) (ha : as.AllButFirstLast p) (hb : bs.AllButFirstLast p) :
    (as ++ bs.tail).AllButFirstLast p := by
  rw [allButFirstLast_iff_getElem] at ha hb ⊢
  simp only [length_append, length_tail] at ha hb ⊢
  intro i hi
  rw [List.getElem_append]
  rcases lt_trichotomy i (as.length - 1) with _ | heq | _
  · simpa only [show i < as.length by lia, ↓reduceDIte] using ha i (by lia)
  · simp only [show i < as.length by lia, ↓reduceDIte]
    simpa [heq] using ha_last
  · have hlen : ¬i < as.length := by lia
    simpa [hlen, ↓reduceDIte, getElem_tail] using (hb (i - as.length + 1) (by lia))

/-- The index of the first element in a list `as` that satisfies a predicate `p`,
excluding the first and last element. -/
def findIdxButFirstLast? (p : α → Bool) (as : List α) : Option ℕ :=
    (as.tail.dropLast.findIdx? p).map (· + 1)

theorem findIdxButFirstLast?_isSome (p : α → Bool) (as : List α) :
    (as.findIdxButFirstLast? p).isSome ↔ (∃ x ∈ as.tail.dropLast, p x) := by
  simp [findIdxButFirstLast?]

theorem findIdxButFirstLast?_eq {p : α → Bool} {as : List α} {i : ℕ} :
    as.findIdxButFirstLast? p = some i ↔
    ∃ _ : 0 < i ∧ i < as.length - 1, p as[i] ∧
      ∀ j (_ : 0 < j ∧ j < i), p as[j] = false := by
  simp only [findIdxButFirstLast?, Option.map_eq_some_iff, findIdx?_eq_some_iff_getElem,
    getElem_dropLast, getElem_tail, Bool.not_eq_true, length_dropLast, length_tail,
    forall_and_index]
  constructor
  · intro ⟨a, ⟨ha_len, ha_spec, ha_min⟩, hai⟩
    refine ⟨by lia, by simpa [hai] using ha_spec, ?_⟩
    intro j hj_pos hj_len
    obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj_pos)
    simpa [hb] using ha_min b (by lia)
  · intro ⟨⟨hi_pos, hi_len⟩, hi_spec, hi_min⟩
    obtain ⟨a, hia⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi_pos)
    refine ⟨a, ⟨by lia, by simpa [hia] using hi_spec, ?_⟩, hia.symm⟩
    intro b hb_len
    simpa using hi_min (b + 1) (by lia) (by lia)

/-- The index of the last element in a list `as` that satisfies a predicate `p`,
excluding the first and last element. -/
def findIdxButFirstLastRev? (p : α → Bool) (as : List α) : Option ℕ :=
    (as.reverse.findIdxButFirstLast? p).map (as.length - 1 - ·)

theorem findIdxButFirstLastRev?_eq {p : α → Bool} {as : List α} {i : ℕ} :
    as.findIdxButFirstLastRev? p = some i ↔
    ∃ _ : 0 < i ∧ i < as.length - 1, p as[i] ∧
      ∀ j (_ : i < j ∧ j < as.length - 1), p as[j] = false := by
  simp only [findIdxButFirstLastRev?, Option.map_eq_some_iff]
  constructor
  · intro ⟨i', hi', hi'i⟩
    obtain ⟨hi'_len, hi'_spec, hi'_min⟩ := findIdxButFirstLast?_eq.mp hi'
    rw [length_reverse] at hi'_len
    refine ⟨by lia, by simpa [hi'i] using hi'_spec, ?_⟩
    intro j ⟨hj_pos, hj_len⟩
    let j' := as.length - 1 - j
    simpa [show as.length - 1 - j' = j by lia] using hi'_min j' (by lia)
  · intro ⟨hi, hi_spec, hi_min⟩
    let i' := as.length - 1 - i
    refine ⟨i', findIdxButFirstLast?_eq.mpr ?_, by lia⟩
    simp only [getElem_reverse, forall_and_index, length_reverse]
    refine ⟨by lia, by simpa [show as.length - 1 - i' = i by lia] using hi_spec, ?_⟩
    intro j hj_pos hj_len
    let j' := as.length - 1 - j
    simpa [show as.length - 1 - j' = j by lia] using hi_min j' (by lia)

end List

variable {Symbol State State' : Type*} {n : ℕ}

open List Cslib.Automata Acceptor

namespace Cslib.LTS

/-- An execution of an LTS with state type `Fin n`,
where all states of the execution except for the first and last are less than `bound`. -/
def BddExec (lts : LTS (Fin n) Symbol) (start : Fin n) (xs : List Symbol) (last : Fin n)
    (ss : List (Fin n)) (bound : ℕ) : Prop :=
  lts.Execution start xs last ss ∧ ss.AllButFirstLast (fun s ↦ s.val < bound)

/-- The language of finite words that are accepted by a `BddExec`. -/
def bddLang (lts : LTS (Fin n) Symbol) (start last : Fin n) (bound : ℕ) : Language Symbol :=
  { xs | ∃ ss, lts.BddExec start xs last ss bound }

theorem bddLang_bound_zero (lts : LTS (Fin n) Symbol) (s t : Fin n) {xs : List Symbol}
   (hxs : ¬xs = []) : xs ∈ lts.bddLang s t 0 ↔ ∃ a, lts.Tr s a t ∧ xs = [a] := by
  refine ⟨fun ⟨ss, hex, hbdd⟩ ↦ ?_,
    fun ⟨a, htr, hxs⟩ ↦ hxs ▸ ⟨[s, t], Execution.of_tr htr, by simp [AllButFirstLast]⟩⟩
  simp only [AllButFirstLast, not_lt_zero, decide_false, Bool.false_eq_true, imp_false] at hbdd
  have hxs_singleton : xs.length = 1 := by
    have len : ss.tail.dropLast.length = 0 := by simp [List.eq_nil_iff_forall_not_mem.mpr hbdd]
    have le : ss.length ≤ 2 := by rw [length_dropLast, length_tail] at len; lia
    rw [hex.length] at le
    have ge : 1 ≤ xs.length := by simpa [Nat.one_le_iff_ne_zero] using hxs
    lia
  obtain ⟨a, ha⟩ : ∃ a, [a] = xs := by simpa [List.length_eq_succ_iff] using hxs_singleton
  exact ⟨a, by simpa [← ha] using hex.to_mTr, ha.symm⟩

theorem bddLang_eq_nfa (lts : LTS (Fin n) Symbol) (s t : Fin n) {r : ℕ} (_ : n ≤ r) :
    lts.bddLang s t r = language (NA.FinAcc.mk ⟨lts, {s}⟩ {t}) := by
  ext xs
  simp only [bddLang, mem_language, Accepts, Set.mem_singleton_iff]
  refine ⟨fun ⟨ss, hex, hbdd⟩ ↦ by simpa using hex.to_mTr, fun ⟨s', hs', t', ht', hmtr⟩ ↦ ?_⟩
  rw [hs', ht'] at hmtr
  obtain ⟨ss, hex⟩ := mTr_iff_execution.mp hmtr
  exact ⟨ss, hex, by grind [AllButFirstLast]⟩

section splitFirst

/-- With an execution of the string `xs` through states `ss`,
`splitFirstTake xs ss r` returns a prefix of `xs`
which ends at the FIRST occurrence (excluding the first and last state) of state `r` in `ss`.
When no such occurrence of `r` exists, `splitFirstTake` returns the empty string; however,
the current file does not use the `splitFirstTake` in such situation.
The actual definition does not require an execution, just the string `xs` and the states `ss`. -/
def splitFirstTake (xs : List Symbol) (ss : List (Fin n)) (r : Fin n) : List Symbol :=
  match ss.findIdxButFirstLast? (· = r) with
  | none => []
  | some i => xs.take i

/-- With an execution of the string `xs` through states `ss`,
`splitFirstDrop xs ss r` returns a suffix of `xs`
which starts at the FIRST occurrence (excluding the first and last state) of state `r` in `ss`.
When no such occurrence of `r` exists, `splitFirstDrop` returns the full string; however,
the current file does not use the `splitFirstDrop` in such situation.
The actual definition does not require an execution, just the string `xs` and the states `ss`. -/
def splitFirstDrop (xs : List Symbol) (ss : List (Fin n)) (r : Fin n) : List Symbol :=
  match ss.findIdxButFirstLast? (· = r) with
  | none => xs
  | some i => xs.drop i

theorem splitFirst_mem {lts : LTS (Fin n) Symbol} {s t r : Fin n} {xs : List Symbol}
    {ss : List (Fin n)} (hex : lts.Execution s xs t ss) (hbdd : ss.AllButFirstLast (· ≤ r))
    (hbdd' : ¬ss.AllButFirstLast (· < r)) :
    splitFirstTake xs ss r ∈ lts.bddLang s r r ∧
    splitFirstDrop xs ss r ∈ lts.bddLang r t (r + 1) := by
  have hisSome : (ss.findIdxButFirstLast? (· = r)).isSome := by
    rw [ss.findIdxButFirstLast?_isSome (· = r)]
    by_contra! hne
    simp only [ne_eq, decide_eq_true_eq] at hne
    simp only [AllButFirstLast, decide_eq_true_eq, not_forall] at hbdd hbdd'
    obtain ⟨u, hu, hnlt⟩ := hbdd'
    have hlt := lt_of_le_of_ne (hbdd u hu) (hne u hu)
    contradiction
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hisSome
  obtain ⟨hi_len, hi_spec, hi_min⟩ := findIdxButFirstLast?_eq.mp hi
  rw [decide_eq_true_eq] at hi_spec
  constructor
  · use ss.take (i + 1)
    refine ⟨by simpa [splitFirstTake, hi, hi_spec] using hex.take i (by lia), ?_⟩
    rw [allButFirstLast_iff_getElem] at hbdd ⊢
    intro j hj
    rw [length_take] at hj
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hbdd hi_min
    simpa using lt_of_le_of_ne (hbdd j (by lia)) (hi_min j (by lia))
  · use ss.drop i
    refine ⟨by simpa [splitFirstDrop, hi, hi_spec] using hex.drop i (by lia), ?_⟩
    rw [allButFirstLast_iff_getElem] at hbdd ⊢
    intro j hj
    rw [length_drop] at hj
    simpa [← add_assoc] using hbdd (i + j) (by lia)

/-- Part of the recursion step of Kleene's algorithm.
A run from `s` to `t` whose interior states are `≤ r` either has all interior states `< r`,
or it splits at its first visit to `r` into
an execution from `s` to `r` with all interior states `< r`, followed by
an execution from `r` to `t` with all interior states `≤ r`. -/
theorem bddLang_splitFirst (lts : LTS (Fin n) Symbol) (s t r : Fin n) :
    lts.bddLang s t (r + 1) = lts.bddLang s t r + lts.bddLang s r r * lts.bddLang r t (r + 1) := by
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
    cases h : ss.findIdxButFirstLast? (· = r) <;> simp_all [splitFirstTake, splitFirstDrop]
  · rintro (⟨ss, hex, hbdd⟩ | ⟨ys, ⟨ssy, hyex, hybdd⟩, ⟨zs, ⟨ssz, hzex, hzbdd⟩, happend⟩⟩)
    · exact ⟨ss, hex, allButFirstLast_imp (by grind) hbdd⟩
    · refine ⟨ssy ++ ssz.tail, by simpa [happend] using hyex.comp hzex, ?_⟩
      simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hybdd hzbdd ⊢
      have hybdd := allButFirstLast_imp (q := fun s ↦ s ≤ r) (by grind) hybdd
      exact allButFirstLast_append (by simp [hyex.length]) (by simpa using le_of_eq hyex.last)
        hybdd hzbdd

end splitFirst

section splitLast

/-- With an execution of the string `xs` through states `ss`,
`splitLastTake xs ss r` returns a prefix of `xs`
which ends at the LAST occurrence (excluding the first and last state) of state `r` in `ss`.
When no such occurrence of `r` exists, `splitLastTake` returns the empty string.
The actual definition does not require an execution, just the string `xs` and the states `ss`. -/
def splitLastTake (xs : List Symbol) (ss : List (Fin n)) (r : Fin n) : List Symbol :=
  match ss.findIdxButFirstLastRev? (· = r) with
  | none => []
  | some i => xs.take i

/-- With an execution of the string `xs` through states `ss`,
`splitLastDrop xs ss r` returns a prefix of `xs`
which ends at the LAST occurrence (excluding the first and last state) of state `r` in `ss`.
When no such occurrence of `r` exists, `splitLastDrop` returns the full string.
The actual definition does not require an execution, just the string `xs` and the states `ss`. -/
def splitLastDrop (xs : List Symbol) (ss : List (Fin n)) (r : Fin n) : List Symbol :=
  match ss.findIdxButFirstLastRev? (· = r) with
  | none => xs
  | some i => xs.drop i

theorem splitLast_mem {lts : LTS (Fin n) Symbol} {t r : Fin n} {xs : List Symbol}
    {ss : List (Fin n)} (hex : lts.Execution r xs t ss) (hbdd : ss.AllButFirstLast (· ≤ r)) :
    splitLastTake xs ss r ∈ lts.bddLang r r (r + 1) ∧
    splitLastDrop xs ss r ∈ lts.bddLang r t r := by
  cases hi : ss.findIdxButFirstLastRev? (· = r) with
  | none =>
  simp only [splitLastTake, splitLastDrop, hi, bddLang, BddExec]
  constructor
  · exact ⟨[r], Execution.refl r, by simp [AllButFirstLast]⟩
  · use ss
    refine ⟨hex, ?_⟩
    simp only [AllButFirstLast, decide_eq_true_eq, Fin.val_fin_lt] at hbdd ⊢
    simp only [findIdxButFirstLastRev?, findIdxButFirstLast?, tail_reverse, dropLast_reverse,
      Option.map_map, Option.map_eq_none_iff, findIdx?_eq_none_iff, mem_reverse,
      decide_eq_false_iff_not, tail_dropLast] at hi
    exact fun s hs ↦ lt_of_le_of_ne (hbdd s hs) (hi s hs)
  | some i =>
  obtain ⟨hi_len, hi_spec, hi_min⟩ := findIdxButFirstLastRev?_eq.mp hi
  rw [decide_eq_true_eq] at hi_spec
  constructor
  · use ss.take (i + 1)
    refine ⟨by simpa [splitLastTake, hi, hi_spec] using hex.take i (by lia), ?_⟩
    rw [allButFirstLast_iff_getElem] at hbdd ⊢
    intro j hj
    rw [length_take] at hj
    simpa using hbdd j (by lia)
  · use ss.drop i
    refine ⟨by simpa [splitLastDrop, hi, hi_spec] using hex.drop i (by lia), ?_⟩
    rw [allButFirstLast_iff_getElem] at hbdd ⊢
    intro j hj
    rw [length_drop] at hj
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hbdd hi_min
    simpa using lt_of_le_of_ne (hbdd (i + j) (by lia)) (hi_min (i + j) (by lia))

theorem splitLastDrop_mem_nonempty {lts : LTS (Fin n) Symbol} {t r : Fin n} {xs : List Symbol}
    {ss : List (Fin n)} (hxs : xs ≠ []) (hex : lts.Execution r xs t ss)
    (hbdd : ss.AllButFirstLast (· ≤ r)) : splitLastDrop xs ss r ∈ lts.bddLang r t r - 1 := by
  rw [Language.mem_sub]
  refine ⟨(splitLast_mem hex hbdd).2, ?_⟩
  simp only [Language.mem_one]
  cases hi : ss.findIdxButFirstLastRev? (· = r) with
  | none => simp [splitLastDrop, hi, hxs]
  | some i =>
  obtain ⟨hi_len, hi_spec, hi_min⟩ := findIdxButFirstLastRev?_eq.mp hi
  simp only [splitLastDrop, hi, drop_eq_nil_iff, not_le]
  simpa [hex.length'] using hi_len.2

/-- Part of the recursion step of Kleene's algorithm.
An execution from `r` to `t` whose interior states are `≤ r` splits at its last visit to `r` into
an execution from `r` to `r` with all interior states `≤ r`, followed by
an execution from `r` to `t` with all interior states `< r`. -/
theorem bddLang_splitLast (lts : LTS (Fin n) Symbol) (t r : Fin n) :
    lts.bddLang r t (r + 1) = lts.bddLang r r (r + 1) * lts.bddLang r t r := by
  ext xs
  rw [Language.mem_mul]
  constructor
  · intro ⟨ss, hex, hbdd⟩
    simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hbdd
    use splitLastTake xs ss r, (splitLast_mem hex hbdd).1,
      splitLastDrop xs ss r, (splitLast_mem hex hbdd).2
    cases h : ss.findIdxButFirstLastRev? (· = r) <;> simp_all [splitLastTake, splitLastDrop]
  · rintro ⟨ys, ⟨ssy, hyex, hybdd⟩, ⟨zs, ⟨ssz, hzex, hzbdd⟩, happend⟩⟩
    refine ⟨ssy ++ ssz.tail, by simpa [happend] using hyex.comp hzex, ?_⟩
    simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hybdd hzbdd ⊢
    have hzbdd := allButFirstLast_imp (q := fun s ↦ s ≤ r) (by grind) hzbdd
    exact allButFirstLast_append (by simp [hyex.length]) (by simpa using le_of_eq hyex.last)
      hybdd hzbdd

end splitLast

open Computability

section kstar

/-- Part of the recursion step of Kleene's algorithm.
An execution from `r` to `r` whose interior states are `≤ r` is
a concatenation of executions from `r` to `r` whose interior states are all `≤ r`. -/
theorem bddLang_kstar (lts : LTS (Fin n) Symbol) (r : Fin n) :
    lts.bddLang r r (r + 1) = (lts.bddLang r r r)∗ := by
  rw [← one_mul (lts.bddLang r r r)∗, ← Language.sub_one_kstar]
  refine (Language.self_eq_add_mul_iff (by simp [Language.mem_sub])).mp ?_
  ext xs
  simp only [Language.mem_add, Language.mem_mul, Language.mem_sub]
  constructor
  · intro ⟨ss, hex, hbdd⟩
    simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hbdd
    by_cases hxs : xs ∈ (1 : Language Symbol)
    · exact Or.inr hxs
    left
    use splitLastTake xs ss r, (splitLast_mem hex hbdd).1,
      splitLastDrop xs ss r, splitLastDrop_mem_nonempty hxs hex hbdd
    cases h : ss.findIdxButFirstLastRev? (· = r) <;> simp_all [splitLastTake, splitLastDrop]
  · rintro (⟨ys, ⟨ssy, hyex, hybdd⟩, ⟨zs, ⟨⟨ssz, hzex, hzbdd⟩, hzsnotempty⟩, happend⟩⟩ | hxs)
    · refine ⟨ssy ++ ssz.tail, by simpa [happend] using hyex.comp hzex, ?_⟩
      simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hybdd hzbdd ⊢
      have hzbdd := allButFirstLast_imp (q := fun s ↦ s ≤ r) (by grind) hzbdd
      exact allButFirstLast_append (by simp [hyex.length]) (by simpa using le_of_eq hyex.last)
        hybdd hzbdd
    · simp only [Language.mem_one] at hxs
      simpa [hxs] using ⟨[r], Execution.refl r, by simp [AllButFirstLast]⟩

end kstar

section regex

open RegularExpression

variable [Finite Symbol]

open Classical in
/-- `regex s t r` is the regular expression for the path from state `s` to `t`
passing through states `< r`.
When `r = 0`, `s = t`, the regex is empty string `ε` union all characters from state `s` to `s`.
When `r = 0`, `s ≠ t`, the regex is all characters from state `s` to `t`.
For `r + 1`, the regex is the union of `regex s t r` and
`(regex s r r) (regex r r r)∗ (regex r t r)`. -/
noncomputable def regex (lts : LTS (Fin n) Symbol) (s t : Fin n) : ℕ → RegularExpression Symbol
  | 0 =>
    let chars := (Set.toFinite {x : Symbol | lts.Tr s x t}).toFinset.toList.map char
    if s = t then 1 + chars.sum else chars.sum
  | r + 1 =>
    if h : n ≤ r then regex lts s t r
    else
      let rFin : Fin n := ⟨r, by lia⟩
      regex lts s t r + regex lts s rFin r * (regex lts rFin rFin r).star * regex lts rFin t r

/-- `LTS.regex s t r` matches the language `LTS.bddLang s t r`. -/
theorem bddLang_eq_regex {r : ℕ} {lts : LTS (Fin n) Symbol} {s t : Fin n} :
    lts.bddLang s t r = (regex lts s t r).matches' := by
  induction r generalizing s t with
  | zero =>
    ext xs
    simp only [regex]
    split_ifs with heq
    · simp only [matches', Language.mem_add, Language.mem_one, mem_sum_matches',
      mem_map, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
      exists_exists_and_eq_and, Language.mem_singleton]
      by_cases hxs : xs = []
      · simp only [← heq, hxs, ne_cons_self, and_false, exists_false, or_false, iff_true]
        exact ⟨[s], Execution.refl s, by simp [AllButFirstLast]⟩
      simpa [hxs] using lts.bddLang_bound_zero s t hxs
    · simp only [mem_sum_matches', mem_map, Finset.mem_toList, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, exists_exists_and_eq_and, matches', Language.mem_singleton]
      by_cases hxs : xs = []
      · simp only [hxs, ne_cons_self, and_false, exists_false, iff_false]
        contrapose heq
        obtain ⟨_, hex, _⟩ := heq
        simpa using hex.to_mTr
      exact lts.bddLang_bound_zero s t hxs
  | succ r ih =>
    simp only [regex]
    split_ifs with hr
    · have hr' : n ≤ r + 1 := by lia
      rw [← ih, lts.bddLang_eq_nfa s t hr, lts.bddLang_eq_nfa s t hr']
    · rw [lts.bddLang_splitFirst (r := ⟨r, by lia⟩), lts.bddLang_splitLast, lts.bddLang_kstar]
      grind [matches'_add, matches'_mul, matches'_star]

/-- An NFA with state type `Fin n` and with exactly one start state `s` and
exactly one accept state `t` has a matching regular expression given by `LTS.regex s t n`. -/
theorem fin_nfa_single_start_accept_eq_regex (lts : LTS (Fin n) Symbol) (s t : Fin n) :
    language (NA.FinAcc.mk ⟨lts, {s}⟩ {t}) = (lts.regex s t n).matches' := by
  rw [← LTS.bddLang_eq_regex, LTS.bddLang_eq_nfa lts s t le_rfl]

end regex

end Cslib.LTS

namespace Cslib.Automata.NA.FinAcc

theorem nfa_single_start_accept_reindex (nfa : NA.FinAcc State Symbol) (e : State ≃ State')
    {s t : State} (hstart : nfa.start = {s}) (haccept : nfa.accept = {t}) :
    language nfa = language (NA.FinAcc.mk ⟨(nfa.toLTS.reindex e), {e s}⟩ {e t}) := by
  set nfa' := NA.FinAcc.mk ⟨(nfa.toLTS.reindex e), {e s}⟩ {e t} with hnfa'
  ext xs
  have nfa_eq : nfa'.MTr (e s) xs (e t) ↔ nfa.MTr s xs t :=
    ⟨by simpa [nfa', LTS.reindex] using (LTS.reindex.bisim_trace nfa'.toLTS e.symm (e s) (e t) xs),
      LTS.reindex.bisim_trace nfa.toLTS e s t xs⟩
  simp only [mem_language, Accepts, hstart, Set.mem_singleton_iff, haccept, exists_eq_left, hnfa']
  rw [nfa_eq]

/-- An NFA with exactly one start state and exactly one accept state
has a matching regular expression. -/
theorem nfa_single_start_accept_eq_regex [Finite Symbol] [Finite State]
    (nfa : NA.FinAcc State Symbol) (s t : State)
    (hstart : nfa.start = {s}) (haccept : nfa.accept = {t}) :
    ∃ r : RegularExpression Symbol, language nfa = r.matches' := by
  let e := Finite.equivFin State
  exact ⟨_, (nfa_single_start_accept_reindex nfa e hstart haccept).trans
    (LTS.fin_nfa_single_start_accept_eq_regex _ (e s) (e t))⟩

/-- Any NFA has a matching regular expression. -/
theorem nfa_eq_regex [Finite Symbol] [Finite State] (nfa : NA.FinAcc State Symbol) :
    ∃ r : RegularExpression Symbol, language nfa = r.matches' := by
  obtain ⟨r, hr⟩ := RegularExpression.iSup_matches' (s := nfa.start ×ˢ nfa.accept)
    (l := fun p ↦ language (NA.FinAcc.mk ⟨nfa.toLTS, {p.1}⟩ {p.2}))
    (fun p _ ↦ nfa_single_start_accept_eq_regex _ p.1 p.2 rfl rfl)
  use r
  ext xs
  rw [← hr, Language.mem_biSup]
  simp [mem_language, Accepts]
  grind

end Cslib.Automata.NA.FinAcc
