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

def AllButFirstLast (p : α → Bool) (as : List α) : Prop := ∀ x, x ∈ as.tail.dropLast → p x

theorem allButFirstLast_iff_getElem (p : α → Bool) (as : List α) :
    as.AllButFirstLast p ↔ ∀ i (_ : i < as.length - 1 - 1), p as[i + 1] = true := by
  simp [AllButFirstLast, forall_mem_iff_getElem]

theorem allButFirstLast_reverse (p : α → Bool) (as : List α) :
    as.AllButFirstLast p ↔ as.reverse.AllButFirstLast p := by
  simp [AllButFirstLast, tail_dropLast]

theorem allButFirstLast_iff_getElem_reverse (p : α → Bool) (as : List α) :
    as.AllButFirstLast p ↔
    ∀ i (_ : i < as.length - 1 - 1), p as[as.length - 1 - (i + 1)] = true := by
  rw [allButFirstLast_reverse, allButFirstLast_iff_getElem]
  simp

theorem allButFirstLast_imp {p q : α → Bool} {as : List α} (h : ∀ x, p x → q x)
    (hp : as.AllButFirstLast p) : as.AllButFirstLast q := (fun x hx ↦ h x <| hp x hx)

theorem allButFirstLast_append {p : α → Bool} {as bs : List α} (hlen : ∃ i, as.length = i + 1)
    (halast : p as[as.length - 1]) (ha : as.AllButFirstLast p) (hb : bs.AllButFirstLast p) :
    (as ++ bs.tail).AllButFirstLast p := by
  rw [allButFirstLast_iff_getElem] at ha hb ⊢
  simp only [length_append, length_tail] at ha hb ⊢
  intro i hi
  rw [List.getElem_append]
  rcases lt_trichotomy (i + 1) (as.length - 1) with h | h | h
  · simp only [(by omega : i + 1 < as.length), ↓reduceDIte]
    exact ha i (by omega)
  · simp only [(by omega : i + 1 < as.length), ↓reduceDIte]
    simpa [h] using halast
  · have hlen : ¬i + 1 < as.length := by omega
    simp only [hlen, ↓reduceDIte, getElem_tail]
    exact hb (i + 1 - as.length) (by omega)

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

theorem bddLang_bound_zero (lts : LTS (Fin n) Symbol) (s t : Fin n) {xs : List Symbol}
   (hxs : ¬xs = []) : xs ∈ lts.BddLang s t 0 ↔ ∃ a, lts.Tr s a t ∧ xs = [a] := by
  refine ⟨fun ⟨ss, hex, hbdd⟩ ↦ ?_,
    fun ⟨a, htr, hxs⟩ ↦ hxs ▸ ⟨[s, t], Execution.of_tr htr, by simp [AllButFirstLast]⟩⟩
  simp only [AllButFirstLast, not_lt_zero, decide_false, Bool.false_eq_true, imp_false] at hbdd
  have : xs.length = 1 := by
    have len : ss.tail.dropLast.length = 0 := by simp [List.eq_nil_iff_forall_not_mem.mpr hbdd]
    have le : ss.length ≤ 2 := by rw [length_dropLast, length_tail] at len; omega
    rw [hex.length] at le
    have ge : 1 ≤ xs.length := by simpa [Nat.one_le_iff_ne_zero] using hxs
    omega
  obtain ⟨a, ha⟩ : ∃ a, [a] = xs := by simpa [List.length_eq_succ_iff] using this
  exact ⟨a, by simpa [← ha] using hex.to_mTr, ha.symm⟩

open Automata Acceptor

theorem bddLang_eq_language_nfa (lts : LTS (Fin n) Symbol) (s t : Fin n) {r : ℕ} (_ : n ≤ r) :
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
    simp only [AllButFirstLast, decide_eq_true_eq, not_forall] at hbdd hbdd'
    obtain ⟨u, hu, hnlt⟩ := hbdd'
    have hlt := lt_of_le_of_ne (hbdd u hu) (hne u hu)
    contradiction
  obtain ⟨i, hi⟩ := findIdxButFirstLast?_index hisSome
  obtain ⟨hi_len, hi_spec, hi_min⟩ := findIdxButFirstLast?_eq.mp hi
  rw [decide_eq_true_eq] at hi_spec
  constructor
  · use ss.take (i + 1 + 1)
    refine ⟨by simpa [splitFirstTake, hi, hi_spec] using hex.take (i + 1) (by omega), ?_⟩
    rw [allButFirstLast_iff_getElem] at hbdd ⊢
    intro j hj
    rw [length_take] at hj
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hbdd hi_min
    simpa using lt_of_le_of_ne (hbdd j (by omega)) (hi_min j (by omega))
  · use ss.drop (i + 1)
    refine ⟨by simpa [splitFirstDrop, hi, hi_spec] using hex.drop (i + 1) (by omega), ?_⟩
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
    cases h : ss.findIdxButFirstLast? (· = r) <;> simp_all [splitFirstTake, splitFirstDrop]
  · rintro (h_left | ⟨ys, ⟨ssy, hyex, hybdd⟩, ⟨zs, ⟨ssz, hzex, hzbdd⟩, happend⟩⟩)
    · obtain ⟨ss, hex, hbdd⟩ := h_left
      exact ⟨ss, hex, allButFirstLast_imp (by grind) hbdd⟩
    · refine ⟨ssy ++ ssz.tail, by simpa [happend] using hyex.comp hzex, ?_⟩
      simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hybdd hzbdd ⊢
      have hybdd := allButFirstLast_imp (q := fun s ↦ s ≤ r) (by grind) hybdd
      exact allButFirstLast_append (by simp [hyex.length]) (by simpa using le_of_eq hyex.last)
        hybdd hzbdd

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
    {ss : List (Fin n)} (hex : lts.Execution r xs t ss) (hbdd : ss.AllButFirstLast (· ≤ r)) :
    splitLastTake xs ss r ∈ lts.BddLang r r (r + 1) ∧
      splitLastDrop xs ss r ∈ lts.BddLang r t r := by
  cases h : ss.findIdxButFirstLastRev? (· = r) with
  | none =>
  simp only [splitLastTake, splitLastDrop, h, BddLang, BddExec]
  constructor
  · exact ⟨[r], Execution.refl r, by simp [AllButFirstLast]⟩
  · use ss
    refine ⟨hex, ?_⟩
    simp only [AllButFirstLast, decide_eq_true_eq, Fin.val_fin_lt] at hbdd ⊢
    simp only [findIdxButFirstLastRev?, findIdxButFirstLast?, tail_reverse, dropLast_reverse,
      Option.map_map, Option.map_eq_none_iff, findIdx?_eq_none_iff, mem_reverse,
      decide_eq_false_iff_not, tail_dropLast] at h
    exact fun s hs ↦ lt_of_le_of_ne (hbdd s hs) (h s hs)
  | some a =>
  obtain ⟨i, hi⟩ := findIdxButFirstLastRev?_index (Option.isSome_iff_exists.mpr ⟨a, h⟩)
  obtain ⟨hi_len, hi_spec, hi_min⟩ := findIdxButFirstLastRev?_eq.mp hi
  rw [decide_eq_true_eq] at hi_spec
  constructor
  · use ss.take (ss.length - 1 - (i + 1) + 1)
    refine ⟨by simpa [splitLastTake, hi, hi_spec]
      using hex.take (ss.length - 1 - (i + 1)) (by omega), ?_⟩
    rw [allButFirstLast_iff_getElem] at hbdd ⊢
    intro j hj
    rw [length_take] at hj
    simpa using hbdd j (by omega)
  · use ss.drop (ss.length - 1 - (i + 1))
    refine ⟨by simpa [splitLastDrop, hi, hi_spec]
      using hex.drop (ss.length - 1 - (i + 1)) (by omega), ?_⟩
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

theorem splitLastDrop_mem_nonempty {lts : LTS (Fin n) Symbol} {t r : Fin n} {xs : List Symbol}
    {ss : List (Fin n)} (hxs : xs ≠ [])
    (hex : lts.Execution r xs t ss) (hbdd : ss.AllButFirstLast (· ≤ r)) :
    splitLastDrop xs ss r ∈ lts.BddLang r t r - 1 := by
  rw [Language.mem_sub]
  refine ⟨(splitLast_mem hex hbdd).2, ?_⟩
  simp only [Language.mem_one]
  cases h : ss.findIdxButFirstLastRev? (· = r) with
  | none => simp [splitLastDrop, h, hxs]
  | some a =>
  obtain ⟨i, hi⟩ := findIdxButFirstLastRev?_index (Option.isSome_iff_exists.mpr ⟨a, h⟩)
  obtain ⟨hi_len, hi_spec, hi_min⟩ := findIdxButFirstLastRev?_eq.mp hi
  simp only [splitLastDrop, h, drop_eq_nil_iff, not_le]
  simp only [hi, Option.some.injEq, hex.length] at h
  have : xs.length ≠ 0 := by simpa using hxs
  grind

theorem bddLang_splitLast (lts : LTS (Fin n) Symbol) (t r : Fin n) :
    lts.BddLang r t (r + 1) = lts.BddLang r r (r + 1) * lts.BddLang r t r := by
  ext xs
  rw [Language.mem_mul]
  constructor
  · intro ⟨ss, hex, hbdd⟩
    simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hbdd
    use splitLastTake xs ss r, (splitLast_mem hex hbdd).1,
      splitLastDrop xs ss r, (splitLast_mem hex hbdd).2
    cases h : ss.findIdxButFirstLastRev? (· = r) <;>
    simp_all [splitLastTake, splitLastDrop]
  · rintro ⟨ys, ⟨ssy, hyex, hybdd⟩, ⟨zs, ⟨ssz, hzex, hzbdd⟩, happend⟩⟩
    refine ⟨ssy ++ ssz.tail, by simpa [happend] using hyex.comp hzex, ?_⟩
    simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hybdd hzbdd ⊢
    have hzbdd := allButFirstLast_imp (q := fun s ↦ s ≤ r) (by grind) hzbdd
    exact allButFirstLast_append (by simp [hyex.length]) (by simpa using le_of_eq hyex.last)
      hybdd hzbdd

end splitLast

open Computability

section kstar

theorem kstar_eq {α : Type*} (l : Language α) : l∗ = (l - 1)∗ := by
  ext x
  rw [Language.kstar_def_nonempty, Language.mem_kstar]
  exact ⟨fun ⟨S, hx, h⟩ => ⟨S, ⟨hx, fun y ys => h y ys⟩⟩,
    fun ⟨S, ⟨hx, h⟩⟩ => ⟨S, hx, fun y ys => h y ys⟩⟩

theorem Language.self_eq_add_mul_iff {α : Type*} {l m n : Language α} (hm : [] ∉ m) :
    l = l * m + n ↔ l = n * m∗ := by
  rw [← Language.reverse_injective.eq_iff, ← Language.reverse_injective.eq_iff (a := l)]
  simp only [Language.reverse_add, Language.reverse_mul, Language.reverse_kstar]
  exact (Language.self_eq_mul_add_iff (by simp [hm]))

/-- Part of the recursion step of Kleene's algorithm.
A run from `r` to `r` whose interior states are all at most `r` is a concatenation of runs from
`r` to `r` whose interior states are all below `r`.
In Kleene's algorithm, this is the "star" in the recursion. -/
theorem bddLang_kstar (lts : LTS (Fin n) Symbol) (r : Fin n) :
    lts.BddLang r r (r + 1) = (lts.BddLang r r r)∗ := by
  rw [← one_mul (lts.BddLang r r r)∗, kstar_eq]
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
    cases h : ss.findIdxButFirstLastRev? (· = r) <;>
    simp_all [splitLastTake, splitLastDrop]
  · rintro (⟨ys, ⟨ssy, hyex, hybdd⟩, ⟨zs, ⟨⟨ssz, hzex, hzbdd⟩, hzsnotempty⟩, happend⟩⟩ | hxs)
    · refine ⟨ssy ++ ssz.tail, by simpa [happend] using hyex.comp hzex, ?_⟩
      simp only [Order.lt_add_one_iff, Fin.val_fin_le] at hybdd hzbdd ⊢
      have hzbdd := allButFirstLast_imp (q := fun s ↦ s ≤ r) (by grind) hzbdd
      exact allButFirstLast_append (by simp [hyex.length]) (by simpa using le_of_eq hyex.last)
        hybdd hzbdd
    · simp only [Language.mem_one] at hxs
      simpa [hxs] using ⟨[r], Execution.refl r, by simp [AllButFirstLast]⟩

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

/-- `Regex s t r` is the regex for the path from state `s` to `t` passing through states `< r`.
When `r = 0`, `s = t`, the regex is `ε` union all characters from state `s` to `s`.
When `r = 0`, `s ≠ t`, the regex is all characters from state `s` to `t`.
For `r + 1`, the regex is the union of `Regex s t r` and
`(Regex s r r) (Regex r r r)∗ (Regex r t r)`. -/
noncomputable def Regex (lts : LTS (Fin n) Symbol) [∀ s t, DecidablePred fun x => lts.Tr s x t]
    (s t : Fin n) : ℕ → RegularExpression Symbol
  | 0 =>
    let chars := (Finset.univ.filter
      (fun x : Symbol ↦ lts.Tr s x t)).toList.map RegularExpression.char
    if s = t then 1 + chars.sum else chars.sum
  | r + 1 =>
    if h : n ≤ r then Regex lts s t r
    else
      let rFin : Fin n := ⟨r, by omega⟩
      Regex lts s t r + Regex lts s rFin r * (Regex lts rFin rFin r).star * Regex lts rFin t r

theorem bddLang_eq_language_regex {r : ℕ} {lts : LTS (Fin n) Symbol}
    [∀ s t, DecidablePred fun x => lts.Tr s x t] {s t : Fin n} :
    lts.BddLang s t r = (Regex lts s t r).matches' := by
  induction r generalizing s t with
  | zero =>
    ext xs
    simp only [Regex]
    split_ifs with heq
    · simp only [matches', Language.mem_add, Language.mem_one, mem_sum_matches'_iff,
      mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_exists_and_eq_and, Language.mem_singleton]
      by_cases hxs : xs = []
      · simp only [← heq, hxs, ne_cons_self, and_false, exists_false, or_false, iff_true]
        exact ⟨[s], Execution.refl s, by simp [AllButFirstLast]⟩
      simpa [hxs] using lts.bddLang_bound_zero s t hxs
    · simp only [mem_sum_matches'_iff, mem_map, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_exists_and_eq_and, matches', Language.mem_singleton]
      by_cases hxs : xs = []
      · simp only [hxs, ne_cons_self, and_false, exists_false, iff_false]
        contrapose! heq
        obtain ⟨_, hex, _⟩ := heq
        simpa using hex.to_mTr
      exact lts.bddLang_bound_zero s t hxs
  | succ r ih =>
    simp only [Regex]
    split_ifs with hr
    · rw [← ih, lts.bddLang_eq_language_nfa s t hr, lts.bddLang_eq_language_nfa s t (by omega)]
    rw [lts.bddLang_splitFirst (r := ⟨r, by omega⟩), lts.bddLang_splitLast, lts.bddLang_kstar]
    grind [matches'_add, matches'_mul, matches'_star]

theorem language_nfa_eq_regex_of_singleton_start_accept {nfa : NA.FinAcc (Fin n) Symbol}
    [∀ s t, DecidablePred fun x => nfa.toLTS.Tr s x t] {s t : Fin n}
    (hstart : nfa.start = {s}) (haccept : nfa.accept = {t}) :
    language nfa = (Regex nfa.toLTS s t n).matches' := by
  simp [← bddLang_eq_language_regex, bddLang_eq_language_nfa, ← hstart, ← haccept]

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
    have nfa_imp_nfa' (s₁ t₁ : State) (μs : List Symbol) :
        nfa.MTr s₁ μs t₁ → nfa'.MTr (e s₁) μs (e t₁) := by
      intro h
      induction h with
      | refl => simp only [MTr.nil_iff, nfa']
      | stepL hTr hMTr ih =>
      simp only [nfa']
      refine MTr.stepL ?_ ih
      simp [hTr]
    have nfa'_imp_nfa (s₁' t₁' : Fin (Fintype.card State)) (μs : List Symbol) :
        nfa'.MTr s₁' μs t₁' → nfa.MTr (e.symm s₁') μs (e.symm t₁') := by
      intro h'
      induction h' with
      | refl => simp only [MTr.nil_iff]
      | stepL hTr hMTr ih =>
      refine MTr.stepL ?_ (ih)
      simpa using hTr
    have nfa_eq : nfa'.MTr (e s) xs (e t) ↔ nfa.MTr s xs t :=
      ⟨by simpa using nfa'_imp_nfa (e s) (e t) xs, nfa_imp_nfa' s t xs⟩
    simp only [mem_language, Accepts, hs, Set.mem_singleton_iff, ht, exists_eq_left, hnfa']
    rw [nfa_eq]
  have : Fintype Symbol := Fintype.ofFinite Symbol
  classical
  simpa [language_eq] using
    ⟨_, language_nfa_eq_regex_of_singleton_start_accept (by dsimp) (by dsimp)⟩

end Cslib.LTS
