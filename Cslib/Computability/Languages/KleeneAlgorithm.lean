/-
Copyright (c) 2026 Brooke Gill and Chi-Yun Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brooke Gill, Chi-Yun Hsu
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Automata.DA.Basic
public import Mathlib.Computability.Language
public import Mathlib.Computability.RegularExpressions

/-!
# Kleene's Algorithm

Kleene's algorithm constructs a regular expresssion by induction on a bound `k` that restricts
which interior states a run may pass through.
It is used to prove `Cslib.Language.IsRegular.iff_regex`, that every language accepted by
a DFA comprised of finite states is the language of a regular expression.
The special case where the DFA has only one accepting state is proved in
`regex_of_dfa_singleton_accept` in this file.

## Main definitions
- `PathSupp`: The interior states of a run
- `BddPath`: A transition system containing a start state, finish state, and a specific bound on
all interior states
- `Regex flts i j k`: The regular expression for the paths from state `i` to state `j`,
whose interior states are all under a specific bound `k`

## Main results
- `regex_of_dfa_singleton_accept`: DFAs with one accepting state have a matching regular
  expression
- `language_bddpath_eq_dfa`: A bound that has reached the total number of states no longer
  constrains anything
- `language_bddpath_eq_regex`: `Regex flts i j k` matches exactly the same paths from `i` to `j`
  with interior states below `k`

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

@[expose] public section

namespace Cslib.Language

open scoped FLTS

variable {Symbol : Type*}

section PathSupp

variable {State : Type*}

/-- `PathSupp s xs` is the set of states that can be reached from state `s` by reading
the string `xs`, not including the starting state and the ending state. -/
def PathSupp (flts : FLTS State Symbol) : State → List Symbol → Set State
  | _, [] | _, [_] => ∅
  | s, a :: x => {flts.tr s a} ∪ PathSupp flts (flts.tr s a) x

theorem pathSupp_empty_iff_empty_or_char {flts : FLTS State Symbol} {s : State} {xs : List Symbol} :
    PathSupp flts s xs = ∅ ↔ xs = [] ∨ (∃ a : Symbol, xs = [a]) := by
  match xs with
  | [] | [_] => grind [PathSupp]
  | x :: y :: ys =>
    have : flts.tr s x ∈ PathSupp flts s (x :: y :: ys) := by grind [PathSupp]
    grind

/-- If `xs` is nonempty, then the interior states of the run that starts at `s` and reads `a :: xs`
consist of the state reached after reading `a` as well as the interior states of the run that starts
at `flts.tr s a` and reads `xs`. -/
theorem pathSupp_head {flts : FLTS State Symbol} {s : State} {a : Symbol} {xs : List Symbol}
    (hxs : xs ≠ []) : PathSupp flts s (a :: xs) =
    {flts.tr s a} ∪ PathSupp flts (flts.tr s a) xs := by
  grind [PathSupp]

theorem pathSupp_append {flts : FLTS State Symbol} {s : State} {xs ys : List Symbol}
    (hxs : xs ≠ [] ∧ ys ≠ []) : PathSupp flts s (xs ++ ys) =
    {flts.mtr s xs} ∪ PathSupp flts s xs ∪ PathSupp flts (flts.mtr s xs) ys := by
  induction xs generalizing s with
  | nil => grind [PathSupp]
  | cons a xs ih =>
  rw [List.cons_append, pathSupp_head (by simp [hxs.2])]
  by_cases hx : xs = []
  · grind [PathSupp]
  · grind [pathSupp_head hx]

end PathSupp

open Automata Acceptor

variable {n : ℕ}

/-- A Bounded Path (`BddPath`) has states `Fin n` and accepts strings (lists of symbols)
starting with state `start` and ending with state `finish`
with the interior states less than `bound`. -/
structure BddPath (n : ℕ) (Symbol : Type*) extends FLTS (Fin n) Symbol where
  start : Fin n
  finish : Fin n
  bound : ℕ

instance : Acceptor (BddPath n Symbol) Symbol where
  Accepts (p : BddPath n Symbol) (xs : List Symbol) :=
    p.mtr p.start xs = p.finish ∧ (∀ i ∈ PathSupp p.toFLTS p.start xs, i < p.bound)

theorem language_bddpath_head_iff {flts : FLTS (Fin n) Symbol} {i j : Fin n} {k : ℕ}
    {a : Symbol} {xs : List Symbol} :
    a :: xs ∈ language (BddPath.mk flts i j k) ↔
    xs ∈ language (BddPath.mk flts (flts.tr i a) j k) ∧ (flts.tr i a < k ∨ xs = []) := by
  simp only [mem_language, Accepts]
  by_cases hxs : xs = []
  · grind [PathSupp]
  grind [pathSupp_head hxs]

theorem language_bddpath_eq_dfa (flts : FLTS (Fin n) Symbol) (i j : Fin n) {k : ℕ} (hk : n ≤ k) :
    language (BddPath.mk flts i j k) = language (DA.FinAcc.mk {tr := flts.tr, start := i} {j}) := by
  simp [language, Accepts]
  grind

open List

section splitLast

/-- Starting at state `i`, the function `splitLast` sends a string to its longest prefix
ending at state `k`.
If the string ends at state `k`, then `splitLast` returns the original string.
If the string never passes through state `k` (starting state can be `k`),
then `splitLast` returns the empty string. -/
def splitLast (flts : FLTS (Fin n) Symbol) (i k : Fin n) : List Symbol → List Symbol
  | [] => []
  | a :: x => if (splitLast flts (flts.tr i a) k x = []) ∧ flts.tr i a ≠ k then []
  else a :: splitLast flts (flts.tr i a) k x

theorem isPrefix_splitLast (flts : FLTS (Fin n) Symbol) (i k : Fin n) (xs : List Symbol) :
    IsPrefix (splitLast flts i k xs) xs := by
  induction xs generalizing i with
  | nil => simp [splitLast]
  | cons a xs ih => grind [splitLast]

/-- Starting at state `i`, the function `splitLastCompl` sends a string to its shortest suffix
starting at state `k`.
If the string ends at state `k`, then `splitLastCompl` returns the empty string.
If the string never passes through state `k` (starting state can be `k`),
then `splitLastCompl` returns the original string. -/
noncomputable def splitLastCompl (flts : FLTS (Fin n) Symbol) (i k : Fin n) (xs : List Symbol) :
    List Symbol := (isPrefix_splitLast flts i k xs).choose

theorem splitLastCompl_append (flts : FLTS (Fin n) Symbol) (i k : Fin n) (xs : List Symbol) :
    splitLast flts i k xs ++ splitLastCompl flts i k xs = xs := by
  grind [splitLastCompl]

theorem splitLastCompl_head (flts : FLTS (Fin n) Symbol) (i k : Fin n) (xs : List Symbol)
    (a : Symbol) : splitLastCompl flts i k (a :: xs) =
    (if splitLast flts (flts.tr i a) k xs = [] ∧ flts.tr i a ≠ k then a :: xs
    else splitLastCompl flts (flts.tr i a) k xs) := by grind [splitLastCompl, splitLast]

theorem splitLast_eq {flts : FLTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    (h : k ∉ PathSupp flts i xs) (h' : k = flts.mtr i xs) : splitLast flts i k xs = xs := by
  induction xs generalizing i with
  | nil => grind [splitLast, PathSupp]
  | cons a xs ih =>
  by_cases hxs : xs = []
  · grind [splitLast, PathSupp]
  grind [pathSupp_head hxs, splitLast,
    (isPrefix_splitLast flts (flts.tr i a) k xs).length_le]

theorem splitLastCompl_eq {flts : FLTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    (h : k ∉ PathSupp flts i xs) (h' : k = flts.mtr i xs) : splitLastCompl flts i k xs = [] := by
  simpa [splitLast_eq h h'] using splitLastCompl_append flts i k xs

/-- `splitLast flts i k xs` is non-empty exclusively when the run from `i` over `xs`
visits `k` at some step AFTER the start. -/
theorem splitLast_nonempty_iff_mem_PathSupp {flts : FLTS (Fin n) Symbol} {i k : Fin n}
    {xs : List Symbol} (hxs : xs ≠ []) :
    ¬(splitLast flts i k xs = []) ↔ k ∈ PathSupp flts i xs ∨ k = flts.mtr i xs := by
  induction xs generalizing i with
  | nil => contradiction
  | cons a xs ih =>
  by_cases hxs' : xs = []
  · grind [splitLast, PathSupp]
  grind [pathSupp_head hxs', splitLast,
    (isPrefix_splitLast flts (flts.tr i a) k xs).length_le]

/-- `splitLastCompl flts i k xs` is not all of `xs` exclusively when the run from `i` over `xs`
visits `k` at some step AFTER the start. -/
theorem splitLastCompl_neq_iff_mem_PathSupp {flts : FLTS (Fin n) Symbol} {i k : Fin n}
    {xs : List Symbol} (hxs : xs ≠ []) :
    ¬(splitLastCompl flts i k xs = xs) ↔ k ∈ PathSupp flts i xs ∨ k = flts.mtr i xs := by
  rw [← splitLast_nonempty_iff_mem_PathSupp hxs, not_iff_not]
  nth_rw 2 [← splitLastCompl_append flts i k xs]
  simp

/-- The run of `a :: xs` from `i` to `j` having `k` as the largest interior state and
no prefix of `a :: xs` (of length 1 or more) ending at state `k` cannot both be true. -/
theorem splitLast_aux {flts : FLTS (Fin n) Symbol} {i j k : Fin n} {xs : List Symbol}
    {a : Symbol} (h : a :: xs ∈ language (BddPath.mk flts i j (k + 1)))
    (h' : a :: xs ∉ language (BddPath.mk flts i j k))
    (hc : splitLast flts (flts.tr i a) k xs = [] ∧ flts.tr i a ≠ k) : False := by
  simp only [mem_language, Accepts, Order.lt_add_one_iff, Fin.val_fin_le, not_and,
      not_forall, not_lt] at *
  simp only [h, forall_const] at h'
  obtain ⟨x, ⟨hx, hxk⟩⟩ := h'
  have eq := le_antisymm (h.2 x hx) hxk
  rw [eq] at hx
  by_cases hxs : xs = []
  · grind [PathSupp]
  rw [pathSupp_head hxs] at hx h
  rcases hx with hx1 | hx2
  · have := hc.2
    simp only [Set.mem_singleton_iff] at hx1
    symm at hx1
    contradiction
  · grind [(splitLast_nonempty_iff_mem_PathSupp hxs).mpr (Or.inl hx2)]

/-- If the run of `xs` from `i` to `j` has `k` as the largest interior state, then
`splitLast flts i k xs` (the longest prefix of `xs` ending at `k`)
is a path from `i` to `k` whose interior states are all below `k + 1`. -/
theorem splitLast_mem {flts : FLTS (Fin n) Symbol} {i j k : Fin n} {xs : List Symbol}
    (h : xs ∈ language (BddPath.mk flts i j (k + 1)))
    (h' : xs ∉ language (BddPath.mk flts i j k)) :
    splitLast flts i k xs ∈ language (BddPath.mk flts i k (k + 1)) := by
  induction xs generalizing i with
  | nil =>
  simp [Accepts, PathSupp] at h h'
  contradiction
  | cons a xs ih =>
  simp only [splitLast]
  split_ifs with hc
  · exfalso; exact splitLast_aux h h' hc
  · rw [not_and_or, not_not] at hc
    -- The last `k` is later than `flts.tr i a` or equal to it.
    by_cases hc1 : ¬splitLast flts (flts.tr i a) k xs = []
    · by_cases hxs : xs = []
      · grind [splitLast]
      have haux := language_bddpath_head_iff.mp h
      simp only [hxs, or_false] at haux
      refine language_bddpath_head_iff.mpr ⟨?_, Or.inl haux.2⟩
      by_cases hk : k ∈ PathSupp flts (flts.tr i a) xs
      · apply ih haux.1
        simp [Accepts]
        grind
      · have eq : k = flts.mtr (flts.tr i a) xs := by
          simpa [hk] using (splitLast_nonempty_iff_mem_PathSupp hxs).mp hc1
        grind [splitLast_eq, h.1]
    · rw [not_not] at hc1
      simpa [hc1, Accepts, PathSupp, FLTS.mtr] using hc

/-- If the run of `xs` from `i` to `j` has `k` as the largest interior state, then
`splitLastCompl flts i k xs` (the shortest suffix of `xs` starting at `k`)
is a path from `k` to `j` whose interior states are all below `k`. -/
theorem splitLastCompl_mem {flts : FLTS (Fin n) Symbol} {i j k : Fin n} {xs : List Symbol}
    (h : xs ∈ language (BddPath.mk flts i j (k + 1)))
    (h' : xs ∉ language (BddPath.mk flts i j k)) :
    splitLastCompl flts i k xs ∈ language (BddPath.mk flts k j k) := by
  induction xs generalizing i with
  | nil =>
  simp [Accepts, PathSupp] at h h'
  contradiction
  | cons a xs ih =>
  have h'' := splitLast_mem h h'
  rw [splitLastCompl_head]
  split_ifs with hc
  · exfalso; exact splitLast_aux h h' hc
  · rw [not_and_or, not_not] at hc
    -- The last `k` is later than `flts.tr i a` or equal to it.
    by_cases hc1 : ¬splitLast flts (flts.tr i a) k xs = []
    · by_cases hxs : xs = []
      · grind [splitLastCompl]
      -- First hypothesis of `ih` is implied by `h`
      have haux := language_bddpath_head_iff.mp h
      -- Assumptions `h` and `h'` combined says that `k ∈ PathSupp flts i (a :: xs)`
      by_cases hk : k ∈ PathSupp flts (flts.tr i a) xs
      · -- `k` appears in PathSupp
        apply ih haux.1
        simp [Accepts]
        grind
      · -- `k` only appears at the end state
        -- `hk` should contradict with `h` and `h'`
        apply (splitLast_nonempty_iff_mem_PathSupp hxs).mp at hc1
        simp_all [Accepts, PathSupp, splitLastCompl_eq]
    · -- The last `k` is equal to `flts.tr i a`
      -- Cannot apply ih
      -- Directly prove the goal from definition
      simp only [mem_language, Accepts] at h ⊢
      by_cases hxs : xs = []
      · grind [splitLastCompl_eq, PathSupp]
      grind [splitLastCompl_append, splitLast_nonempty_iff_mem_PathSupp, pathSupp_head]

/-- Part of the recursion step of Kleene's algorithm.
A run from `i` to `j` whose interior states are all at most `k` either has no interior state equal
to `k`, or it splits at its last visit to `k` into a run from `i` to `k` with interior states
below `k + 1`, followed by a run from `k` to `j` with interior states below `k`. -/
theorem language_bddpath_splitLast (flts : FLTS (Fin n) Symbol) (i j k : Fin n) :
    language (BddPath.mk flts i j (k + 1)) = language (BddPath.mk flts i j k) +
    (language (BddPath.mk flts i k (k + 1)) * language (BddPath.mk flts k j k)) := by
  ext xs
  rw [Language.mem_add, Language.mem_mul]
  constructor
  · intro h
    by_cases h' : xs ∈ language (BddPath.mk flts i j k)
    · left; exact h'
    right
    use splitLast flts i k xs, splitLast_mem h h',
    splitLastCompl flts i k xs, splitLastCompl_mem h h',
    splitLastCompl_append flts _ _ _
  · rintro (h_left | ⟨ys, ⟨⟨hys, hsuppys⟩, ⟨zs, ⟨⟨hzs, hsuppzs⟩, happend⟩⟩⟩⟩)
    · simp only [mem_language, Accepts] at h_left ⊢
      grind
    · refine ⟨by grind, ?_⟩
      by_cases ys = [] ∨ zs = []
      · grind
      grind [pathSupp_append]

end splitLast

section splitFirst

/-- Starting from a state `i`, the function `splitFirst` sends a string to its shortest prefix
ending at state `k`.
The string is empty if and only if its `splitFirst` is empty.
If the string never passes through state `k` (starting state can be `k`),
then `splitFirst` returns the original string. -/
def splitFirst (flts : FLTS (Fin n) Symbol) (i k : Fin n) : List Symbol → List Symbol
  | [] => []
  | a :: x => if flts.tr i a = k then [a] else a :: splitFirst flts (flts.tr i a) k x

theorem isPrefix_splitFirst (flts : FLTS (Fin n) Symbol) (i k : Fin n) (xs : List Symbol) :
    IsPrefix (splitFirst flts i k xs) xs := by
  induction xs generalizing i with
  | nil => simp [splitFirst]
  | cons a xs ih => grind [splitFirst]

noncomputable def splitFirstCompl (flts : FLTS (Fin n) Symbol) (i k : Fin n)
    (xs : List Symbol) : List Symbol := (isPrefix_splitFirst flts i k xs).choose

theorem splitFirst_append (flts : FLTS (Fin n) Symbol) (i k : Fin n) (xs : List Symbol) :
    splitFirst flts i k xs ++ splitFirstCompl flts i k xs = xs := by
  grind [splitFirstCompl]

/-- If the run of `xs` from `i` to `k` has all interior states below `k + 1`, then
  `splitFirst flts i k xs` (the shortest prefix of `xs`)
  is a path whose interior states are all below `k`. -/
theorem splitFirst_mem {flts : FLTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    (h : xs ∈ (language (BddPath.mk flts i k (k + 1)))) :
    splitFirst flts i k xs ∈ language (BddPath.mk flts i k k) := by
  induction xs generalizing i with
  | nil => simpa [Accepts, splitFirst, PathSupp] using h
  | cons a xs ih =>
  simp only [mem_language, Accepts, splitFirst] at ih h ⊢
  obtain ⟨h1, h2⟩ := h
  split_ifs with ha
  · refine ⟨by grind, ?_⟩
    have : PathSupp flts i [a] = ∅ := by grind [PathSupp]
    simp [this]
  · by_cases hxs : xs = []
    · grind
    rw [pathSupp_head hxs] at h2
    by_cases hPath : splitFirst flts (flts.tr i a) k xs = []
    · grind
    grind [pathSupp_head]

theorem splitFirst_mem_nonempty {flts : FLTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    (hxs : xs ≠ []) (h : xs ∈ (language (BddPath.mk flts i k (k + 1)))) :
    splitFirst flts i k xs ∈ language (BddPath.mk flts i k k) - 1 := by
  rw [Language.mem_sub]
  refine ⟨splitFirst_mem h, ?_⟩
  simp only [Language.mem_one]
  induction xs with
  | nil => contradiction
  | cons a xs ih => grind [splitFirst]

/-- If the run of `xs` from `i` to `k` has all interior states below `k + 1`, then
  `splitFirstCompl flts i k xs` (the longest suffix of `xs` starting at `k`)
  is a path from `k` to `k` whose interior states are all below `k + 1`. -/
theorem splitFirstCompl_mem {flts : FLTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    (h : xs ∈ (language (BddPath.mk flts i k (k + 1)))) :
    splitFirstCompl flts i k xs ∈ language (BddPath.mk flts k k (k + 1)) := by
  have h' := splitFirst_mem h
  simp only [mem_language, Accepts] at h h' ⊢
  rw [← splitFirst_append flts i k xs] at h
  refine ⟨by grind, ?_⟩
  by_cases splitFirst flts i k xs = [] ∨ splitFirstCompl flts i k xs = []
  · grind [PathSupp]
  grind [pathSupp_append]

/-- Part of the recursion step of Kleene's algorithm.
A run from `i` to `j` whose interior states are all at most `k` splits upon first reaching `k`.
The part before the visit is a run from `i` to `k` with interior states below `k`.
The part after it is a run from `k` to `k` with interior states below `k + 1`. -/
theorem language_bddpath_splitFirst (flts : FLTS (Fin n) Symbol) (i k : Fin n) :
    language (BddPath.mk flts i k (k + 1)) =
    language (BddPath.mk flts i k k) * language (BddPath.mk flts k k (k + 1)) := by
  ext xs
  rw [Language.mem_mul]
  constructor
  · intro h
    use splitFirst flts i k xs, splitFirst_mem h,
      splitFirstCompl flts i k xs, splitFirstCompl_mem h,
      splitFirst_append flts _ _ _
  · intro ⟨ys, ⟨⟨hys, hsuppys⟩, ⟨zs, ⟨⟨hzs, hsuppzs⟩, happend⟩⟩⟩⟩
    refine ⟨by grind, ?_⟩
    by_cases ys = [] ∨ zs = []
    · grind
    grind [pathSupp_append]

end splitFirst

open Computability

section kstar

theorem kstar_eq {α : Type*} (l : Language α) : l∗ = (l - 1)∗ := by
  ext x
  rw [Language.kstar_def_nonempty, Language.mem_kstar]
  exact ⟨fun ⟨S, hx, h⟩ => ⟨S, ⟨hx, fun y ys => h y ys⟩⟩,
    fun ⟨S, ⟨hx, h⟩⟩ => ⟨S, hx, fun y ys => h y ys⟩⟩

/-- Part of the recursion step of Kleene's algorithm.
A run from `k` to `k` whose interior states are all at most `k` is a concatenation of runs from
`k` to `k` whose interior states are all below `k`.
In Kleene's algorithm, this is the "star" in the recursion. -/
theorem language_bddpath_kstar (flts : FLTS (Fin n) Symbol) (k : Fin n) :
    language (BddPath.mk flts k k (k + 1)) = (language (BddPath.mk flts k k k))∗ := by
  rw [← mul_one (language (BddPath.mk flts k k ↑k))∗, kstar_eq]
  refine (Language.self_eq_mul_add_iff (by simp [Language.mem_sub])).mp ?_
  ext xs
  simp only [Language.mem_add, Language.mem_mul, Language.mem_sub]
  constructor
  · intro h
    by_cases h' : xs ∈ (1 : Language Symbol)
    · grind
    left
    use splitFirst flts k k xs, splitFirst_mem_nonempty h' h,
      splitFirstCompl flts k k xs, splitFirstCompl_mem h,
      splitFirst_append flts _ _ _
  · rintro (⟨ys, ⟨⟨⟨hys, hsuppys⟩, hysnotempty⟩, ⟨zs, ⟨⟨hzs, hsuppzs⟩, happend⟩⟩⟩⟩ | hempty)
    · refine ⟨by grind, ?_⟩
      by_cases zs = []
      · grind
      grind [pathSupp_append, Language.mem_one]
    · rw [Language.mem_one] at hempty
      simp only [mem_language, Accepts]
      grind [PathSupp]

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

/--
Regex i j k is the regex for the path from state i to state j passing through states < k.
When k = 0, i = j, the regex is ε union all characters from state i to state i.
When k = 0, i ≠ j, the regex is all characters from state i to state j.
For k + 1, the regex is the union of Regex i j k and
(Regex i k k) (Regex k k k)∗ (Regex k j k).
-/
noncomputable def Regex (flts : FLTS (Fin n) Symbol) (i j : Fin n) : ℕ → RegularExpression Symbol
  | 0 =>
    let chars := (Finset.univ.filter
      (fun x : Symbol ↦ flts.tr i x = j)).toList.map RegularExpression.char
    if i = j then 1 + chars.sum else chars.sum
  | k + 1 =>
    if h : n ≤ k then Regex flts i j k
    else
      let kFin : Fin n := ⟨k, by omega⟩
      Regex flts i j k + Regex flts i kFin k * (Regex flts kFin kFin k).star * Regex flts kFin j k

/-- The correctness of Kleene's algorithm.
`Regex flts i j k` exactly matches the strings that have a run starting
at `i`, ending at `j`, and having all interior states below `k`. -/
theorem language_bddpath_eq_regex {k : ℕ} {flts : FLTS (Fin n) Symbol} {i j : Fin n} :
    language (BddPath.mk flts i j k) = (Regex flts i j k).matches' := by
  induction k generalizing i j with
  | zero =>
    ext xs
    simp only [mem_language, Accepts, not_lt_zero, Regex]
    rw [(by grind : (∀ i_1 ∈ PathSupp flts i xs, False) ↔ PathSupp flts i xs = ∅)]
    split_ifs with heq
    · -- The case of i = j, k = 0
      simp only [matches', Language.mem_add, mem_sum_matches'_iff, pathSupp_empty_iff_empty_or_char]
      aesop
    · -- The case of i ≠ j, k = 0
      rw [mem_sum_matches'_iff, pathSupp_empty_iff_empty_or_char]
      aesop
  | succ k ih =>
    simp only [Regex]
    split_ifs with hk
    · rw [← ih, language_bddpath_eq_dfa flts i j hk, language_bddpath_eq_dfa flts i j (by omega)]
    rw [language_bddpath_splitLast (k := ⟨k, by omega⟩), language_bddpath_splitFirst,
      language_bddpath_kstar]
    grind [matches'_add, matches'_mul, matches'_star]

theorem language_dfa_eq_regex_of_singleton_accept {dfa : DA.FinAcc (Fin n) Symbol} {s : Fin n}
    (h : dfa.accept = {s}) : language dfa = (Regex dfa.toFLTS dfa.start s n).matches' := by
  simp [← language_bddpath_eq_regex, language, Accepts, h]
  rfl

end Regex

/-- DFAs with one accepting state have a matching regular expression -/
theorem regex_of_dfa_singleton_accept [Finite Symbol] {State : Type*} [Finite State]
    (dfa : DA.FinAcc State Symbol) (h : ∃ s, dfa.accept = {s}) :
    ∃ r : RegularExpression Symbol, language dfa = r.matches' := by
  have : Fintype State := Fintype.ofFinite State
  let e := Fintype.equivFin State
  obtain ⟨s, h⟩ := h
  set dfa' := DA.FinAcc.mk {tr := fun s a => e (dfa.tr (e.symm s) a), start := (e dfa.start)} {e s}
    with hdfa'
  have language_eq : language dfa = language dfa' := by
    ext xs
    have dfa_eq : dfa'.mtr dfa'.start xs = e (dfa.mtr dfa.start xs) := by
      induction xs using List.reverseRec with
      | nil => grind
      | append_singleton xs x ih => grind
    simp only [mem_language, Accepts, h, hdfa']
    rw [dfa_eq]
    simp
  have : Fintype Symbol := Fintype.ofFinite Symbol
  simpa [language_eq] using  ⟨_, language_dfa_eq_regex_of_singleton_accept (by dsimp)⟩

end Cslib.Language
