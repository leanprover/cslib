/-
Copyright (c) 2026 geopi1. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: geopi1
-/
module

public import Cslib.Algorithms.Lean.Query.Maximum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Int

/-! # Finding the minimum and the maximum together

Finding both the minimum and the maximum of `n` elements with comparisons needs exactly
`⌈3n/2⌉ - 2` comparisons, written `(3 * n + 1) / 2 - 2` below.

* `minMax` compares the elements in pairs, and each pair's smaller element with the current
  minimum and its larger element with the current maximum. `minMax_isMinMaxFinder` proves it
  correct and `countQueries_minMax` proves it makes exactly `(3 * n + 1) / 2 - 2` queries.
* `IsMinMaxFinder.exists_oracle_le_countQueries` proves that *every* correct comparison-based
  min-max finder makes at least `(3 * n + 1) / 2 - 2` queries on some oracle, for every list of `n`
  distinct elements. `IsMinMaxFinder.lowerBound` restates this as a `Query.LowerBound`.

The lower bound is Pohl's adversary argument. Every element other than the reported minimum must
win some comparison, and every element other than the reported maximum must lose one: otherwise
moving it to the bottom (respectively top) of the order does not change any answer. The adversary
keeps integer values for the elements and answers each comparison so that it gives at most one
new "win or loss" unless both elements are new, adjusting the values of elements that have only
won (raising them) or only lost (lowering them) so that earlier answers stay valid. A potential
argument then shows that `2n - 2` units cost at least `⌈3n/2⌉ - 2` comparisons.

## References

* [I. Pohl, *A sorting problem and its complexity*][Pohl1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein, *Introduction to Algorithms*][Cormen2009],
  Section 9.1.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

variable {α : Type}

/-! ## Specification -/

/-- `find` is a correct comparison-based min-max finder: on a nonempty list it returns a pair of
elements of the list, and when the oracle implements a total preorder `r` they are an `r`-minimum
and an `r`-maximum of the list. -/
structure IsMinMaxFinder (find : List α → FreeM (LEQuery α) (Option (α × α))) : Prop where
  /-- On a nonempty input, the program returns some pair. -/
  isSome : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι),
    xs ≠ [] → ((find xs).eval oracle).isSome
  /-- The returned elements belong to the input, for any oracle. -/
  mem : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι) (mn mx : α),
    (find xs).eval oracle = some (mn, mx) → mn ∈ xs ∧ mx ∈ xs
  /-- The returned elements are a minimum and a maximum, when the oracle implements a total
  preorder. -/
  le_of_mem : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (_ : ∀ a b, oracle (.le a b) = decide (r a b)) (mn mx : α),
    (find xs).eval oracle = some (mn, mx) → ∀ y ∈ xs, r mn y ∧ r y mx

/-! ## The pairwise scan -/

/-- Scan `rest` two elements at a time, keeping the current minimum `mn` and maximum `mx`: the
smaller element of each pair is compared with `mn` and the larger with `mx`. A last single element
is compared with both. -/
def minMaxAux (mn mx : α) : List α → FreeM (LEQuery α) (α × α)
  | [] => pure (mn, mx)
  | [x] => do
    let b₁ ← LEQuery.ask x mn
    let b₂ ← LEQuery.ask mx x
    pure (bif b₁ then x else mn, bif b₂ then x else mx)
  | x :: y :: rest => do
    let b ← LEQuery.ask x y
    let b₁ ← LEQuery.ask (bif b then x else y) mn
    let b₂ ← LEQuery.ask mx (bif b then y else x)
    minMaxAux (bif b₁ then (bif b then x else y) else mn)
      (bif b₂ then (bif b then y else x) else mx) rest

/-- The minimum and the maximum of a list, or `none` for the empty list. -/
def minMax : List α → FreeM (LEQuery α) (Option (α × α))
  | [] => pure none
  | [x] => pure (some (x, x))
  | x :: y :: rest => do
    let b ← LEQuery.ask x y
    some <$> minMaxAux (bif b then x else y) (bif b then y else x) rest

@[simp] theorem countQueries_minMaxAux (oracle : {ι : Type} → LEQuery α ι → ι) :
    ∀ (mn mx : α) (rest : List α),
      (minMaxAux mn mx rest).countQueries oracle = 3 * (rest.length / 2) + 2 * (rest.length % 2)
  | _, _, [] => by simp [minMaxAux]
  | _, _, [_] => by simp [minMaxAux]
  | _, _, x :: y :: rest => by
    have ih := fun a b => countQueries_minMaxAux oracle a b rest
    simp only [minMaxAux, FreeM.countQueries_bind, FreeM.countQueries_lift, ih, List.length_cons]
    omega

/-- The pairwise scan makes exactly `⌈3n/2⌉ - 2` queries, whatever the oracle. -/
@[simp] theorem countQueries_minMax (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (minMax xs).countQueries oracle = (3 * xs.length + 1) / 2 - 2 := by
  match xs with
  | [] => simp [minMax]
  | [x] => simp [minMax]
  | x :: y :: rest =>
    simp only [minMax, FreeM.countQueries_bind, FreeM.countQueries_lift, FreeM.countQueries_map,
      countQueries_minMaxAux, List.length_cons]
    omega

private theorem minMaxAux_mem (oracle : {ι : Type} → LEQuery α ι → ι) :
    ∀ (mn mx : α) (rest : List α),
      ((minMaxAux mn mx rest).eval oracle).1 ∈ mn :: rest ∧
        ((minMaxAux mn mx rest).eval oracle).2 ∈ mx :: rest
  | _, _, [] => by simp [minMaxAux]
  | mn, mx, [x] => by
    simp only [minMaxAux, FreeM.eval_bind, FreeM.eval_lift, FreeM.eval_pure]
    constructor <;> cases oracle _ <;> simp
  | mn, mx, x :: y :: rest => by
    simp only [minMaxAux, FreeM.eval_bind, FreeM.eval_lift]
    obtain ⟨h₁, h₂⟩ := minMaxAux_mem oracle
      (bif oracle (.le (bif oracle (.le x y) then x else y) mn)
      then (bif oracle (.le x y) then x else y) else mn)
      (bif oracle (.le mx (bif oracle (.le x y) then y else x))
      then (bif oracle (.le x y) then y else x) else mx) rest
    constructor
    · rcases List.mem_cons.mp h₁ with h | h
      · rw [h]; cases oracle (.le x y) <;> cases oracle _ <;> simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    · rcases List.mem_cons.mp h₂ with h | h
      · rw [h]; cases oracle (.le x y) <;> cases oracle _ <;> simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))

/-- The invariant of the scan, under an oracle implementing a total preorder: the result is below
the initial minimum and every scanned element, and above the initial maximum and every scanned
element. -/
private theorem minMaxAux_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) :
    ∀ (mn mx : α) (rest : List α),
      r ((minMaxAux mn mx rest).eval oracle).1 mn ∧ r mx ((minMaxAux mn mx rest).eval oracle).2 ∧
        ∀ z ∈ rest, r ((minMaxAux mn mx rest).eval oracle).1 z ∧
          r z ((minMaxAux mn mx rest).eval oracle).2
  | mn, mx, [] => by simp [minMaxAux, refl_of r]
  | mn, mx, [x] => by
    simp only [minMaxAux, FreeM.eval_bind, FreeM.eval_lift, FreeM.eval_pure, horacle,
      List.mem_singleton, forall_eq]
    by_cases h₁ : r x mn <;> by_cases h₂ : r mx x <;> simp only [h₁, h₂, decide_true,
      decide_false, Bool.cond_true, Bool.cond_false] <;>
      grind [total_of r x mn, total_of r mx x, refl_of r mn, refl_of r mx, refl_of r x]
  | mn, mx, x :: y :: rest => by
    simp only [minMaxAux, FreeM.eval_bind, FreeM.eval_lift, horacle]
    -- `lo ≤ hi` is the pair in order.
    obtain ⟨lo, hi, hlohi, hxy, hlo, hhi⟩ : ∃ lo hi, r lo hi ∧
        ((lo = x ∧ hi = y) ∨ (lo = y ∧ hi = x)) ∧
        (bif decide (r x y) then x else y) = lo ∧ (bif decide (r x y) then y else x) = hi := by
      by_cases hb : r x y
      · exact ⟨x, y, hb, Or.inl ⟨rfl, rfl⟩, by simp [hb], by simp [hb]⟩
      · exact ⟨y, x, (total_of r x y).resolve_left hb, Or.inr ⟨rfl, rfl⟩, by simp [hb],
          by simp [hb]⟩
    rw [hlo, hhi]
    -- The updated candidates.
    obtain ⟨mn₁, hmn₁, hmn₁mn, hmn₁lo⟩ : ∃ mn₁, (bif decide (r lo mn) then lo else mn) = mn₁ ∧
        r mn₁ mn ∧ r mn₁ lo := by
      by_cases h : r lo mn
      · exact ⟨lo, by simp [h], h, refl_of r lo⟩
      · exact ⟨mn, by simp [h], refl_of r mn, (total_of r lo mn).resolve_left h⟩
    obtain ⟨mx₁, hmx₁, hmx₁mx, hmx₁hi⟩ : ∃ mx₁, (bif decide (r mx hi) then hi else mx) = mx₁ ∧
        r mx mx₁ ∧ r hi mx₁ := by
      by_cases h : r mx hi
      · exact ⟨hi, by simp [h], h, refl_of r hi⟩
      · exact ⟨mx, by simp [h], refl_of r mx, (total_of r mx hi).resolve_left h⟩
    rw [hmn₁, hmx₁]
    obtain ⟨i₁, i₂, i₃⟩ := minMaxAux_le oracle r horacle mn₁ mx₁ rest
    refine ⟨_root_.trans i₁ hmn₁mn, _root_.trans hmx₁mx i₂, fun z hz => ?_⟩
    have hlo' : r ((minMaxAux mn₁ mx₁ rest).eval oracle).1 lo := _root_.trans i₁ hmn₁lo
    have hhi' : r hi ((minMaxAux mn₁ mx₁ rest).eval oracle).2 := _root_.trans hmx₁hi i₂
    have hz' : z = lo ∨ z = hi ∨ z ∈ rest := by
      rcases List.mem_cons.mp hz with rfl | hz
      · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      rcases List.mem_cons.mp hz with rfl | hz
      · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      · exact Or.inr (Or.inr hz)
    rcases hz' with rfl | rfl | hz
    · exact ⟨hlo', _root_.trans hlohi hhi'⟩
    · exact ⟨_root_.trans hlo' hlohi, hhi'⟩
    · exact i₃ z hz

theorem minMax_isMinMaxFinder : IsMinMaxFinder (minMax (α := α)) where
  isSome xs oracle h := by
    match xs with
    | [] => exact absurd rfl h
    | [x] => simp [minMax]
    | x :: y :: rest => simp [minMax]
  mem xs oracle mn mx h := by
    match xs with
    | [] => simp [minMax] at h
    | [x] =>
      simp only [minMax, FreeM.eval_pure, Option.some.injEq, Prod.mk.injEq] at h
      simp [← h.1, ← h.2]
    | x :: y :: rest =>
      simp only [minMax, FreeM.eval_bind, FreeM.eval_lift, FreeM.eval_map,
        Option.some.injEq] at h
      obtain ⟨h₁, h₂⟩ := minMaxAux_mem oracle (bif oracle (.le x y) then x else y)
        (bif oracle (.le x y) then y else x) rest
      rw [h] at h₁ h₂
      constructor
      · rcases List.mem_cons.mp h₁ with h | h
        · simp only at h; rw [h]; cases oracle (.le x y) <;> simp
        · simp [h]
      · rcases List.mem_cons.mp h₂ with h | h
        · simp only at h; rw [h]; cases oracle (.le x y) <;> simp
        · simp [h]
  le_of_mem xs oracle r _ _ _ horacle mn mx h := by
    match xs with
    | [] => simp [minMax] at h
    | [x] =>
      simp only [minMax, FreeM.eval_pure, Option.some.injEq, Prod.mk.injEq] at h
      simp [← h.1, ← h.2, refl_of r x]
    | x :: y :: rest =>
      simp only [minMax, FreeM.eval_bind, FreeM.eval_lift, FreeM.eval_map,
        Option.some.injEq, horacle] at h
      obtain ⟨i₁, i₂, i₃⟩ := minMaxAux_le oracle r horacle (bif decide (r x y) then x else y)
        (bif decide (r x y) then y else x) rest
      rw [h] at i₁ i₂ i₃
      intro z hz
      by_cases hb : r x y
      · simp only [hb, decide_true, Bool.cond_true] at i₁ i₂ i₃
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨i₁, _root_.trans hb i₂⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨_root_.trans i₁ hb, i₂⟩
        · exact i₃ z hz
      · have hyx : r y x := (total_of r x y).resolve_left hb
        simp only [hb, decide_false, Bool.cond_false] at i₁ i₂ i₃
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨_root_.trans i₁ hyx, i₂⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨i₁, _root_.trans hyx i₂⟩
        · exact i₃ z hz

/-- The pairwise scan uses at most `⌈3n/2⌉ - 2` queries on inputs of length `n`. -/
theorem minMax_upperBound :
    UpperBound (minMax (α := α)) List.length (fun n => (3 * n + 1) / 2 - 2) :=
  UpperBound.of_pointwise (fun _ _ h => by omega) fun oracle xs =>
    (countQueries_minMax oracle xs).le

/-! ## Winners and losers -/

/-- The winner of the comparison `(a, b)`: `b` if the oracle answers `a ≤ b`, and `a` otherwise. -/
def winner (oracle : {ι : Type} → LEQuery α ι → ι) (q : α × α) : α :=
  if oracle (.le q.1 q.2) then q.2 else q.1

theorem winner_def (oracle : {ι : Type} → LEQuery α ι → ι) (q : α × α) :
    winner oracle q = if oracle (.le q.1 q.2) then q.2 else q.1 := by
  simp [winner]

/-- `r` modified so that `y` is above every element. -/
private def toTop (r : α → α → Prop) (y : α) (a b : α) : Prop :=
  b = y ∨ (a ≠ y ∧ r a b)

/-- `r` modified so that `y` is below every element. -/
private def toBottom (r : α → α → Prop) (y : α) (a b : α) : Prop :=
  a = y ∨ (b ≠ y ∧ r a b)

private instance (r : α → α → Prop) [Std.Total r] (y : α) : Std.Total (toTop r y) where
  total a b := by
    by_cases ha : a = y
    · exact Or.inr (Or.inl ha)
    by_cases hb : b = y
    · exact Or.inl (Or.inl hb)
    rcases total_of r a b with h | h
    · exact Or.inl (Or.inr ⟨ha, h⟩)
    · exact Or.inr (Or.inr ⟨hb, h⟩)

private instance (r : α → α → Prop) [IsTrans α r] (y : α) : IsTrans α (toTop r y) where
  trans a b c hab hbc := by
    rcases hbc with hc | ⟨hb, hbc⟩
    · exact Or.inl hc
    rcases hab with rfl | ⟨ha, hab⟩
    · exact absurd rfl hb
    · exact Or.inr ⟨ha, _root_.trans hab hbc⟩

private instance (r : α → α → Prop) [Std.Total r] (y : α) : Std.Total (toBottom r y) where
  total a b := by
    by_cases ha : a = y
    · exact Or.inl (Or.inl ha)
    by_cases hb : b = y
    · exact Or.inr (Or.inl hb)
    rcases total_of r a b with h | h
    · exact Or.inl (Or.inr ⟨hb, h⟩)
    · exact Or.inr (Or.inr ⟨ha, h⟩)

private instance (r : α → α → Prop) [IsTrans α r] (y : α) : IsTrans α (toBottom r y) where
  trans a b c hab hbc := by
    rcases hab with ha | ⟨hb, hab⟩
    · exact Or.inl ha
    rcases hbc with rfl | ⟨hc, hbc⟩
    · exact absurd rfl hb
    · exact Or.inr ⟨hc, _root_.trans hab hbc⟩

/-- In a run of a correct min-max finder under a total preorder, every input element other than
the reported maximum loses a comparison with a different element. -/
theorem IsMinMaxFinder.exists_loser {find : List α → FreeM (LEQuery α) (Option (α × α))}
    (hfind : IsMinMaxFinder find) (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) {mn mx : α}
    (hm : (find xs).eval oracle = some (mn, mx)) {y : α} (hy : y ∈ xs) (hyx : y ≠ mx) :
    ∃ q ∈ comparisons oracle (find xs), q.1 ≠ q.2 ∧ loser oracle q = y := by
  classical
  by_contra! hlose
  let oracle' : {ι : Type} → LEQuery α ι → ι := LEQuery.oracleOf fun a b => decide (toTop r y a b)
  have hagree : ∀ q ∈ comparisons oracle (find xs),
      oracle (.le q.1 q.2) = oracle' (.le q.1 q.2) := by
    rintro ⟨a, b⟩ hq
    simp only [horacle, oracle', LEQuery.oracleOf_le, toTop]
    by_cases hab : a = b
    · subst hab
      simp [refl_of r a]
    have hl := hlose (a, b) hq hab
    simp only [loser_def, horacle] at hl
    by_cases hb : b = y
    · subst hb
      by_cases h : r a b
      · simp [h]
      · simp [h] at hl
    · by_cases ha : a = y
      · subst ha
        by_cases h : r a b
        · simp [h] at hl
        · simp [h, hb]
      · simp [ha, hb]
  have hm' : (find xs).eval oracle' = some (mn, mx) := by
    rw [← eval_eq_of_comparisons _ _ _ hagree, hm]
  rcases (hfind.le_of_mem xs oracle' (toTop r y) (fun _ _ => rfl) mn mx hm' y hy).2 with h | ⟨h, _⟩
  · exact hyx h.symm
  · exact h rfl

/-- In a run of a correct min-max finder under a total preorder, every input element other than
the reported minimum wins a comparison with a different element. -/
theorem IsMinMaxFinder.exists_winner {find : List α → FreeM (LEQuery α) (Option (α × α))}
    (hfind : IsMinMaxFinder find) (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) {mn mx : α}
    (hm : (find xs).eval oracle = some (mn, mx)) {y : α} (hy : y ∈ xs) (hyn : y ≠ mn) :
    ∃ q ∈ comparisons oracle (find xs), q.1 ≠ q.2 ∧ winner oracle q = y := by
  classical
  by_contra! hwin
  let oracle' : {ι : Type} → LEQuery α ι → ι :=
    LEQuery.oracleOf fun a b => decide (toBottom r y a b)
  have hagree : ∀ q ∈ comparisons oracle (find xs),
      oracle (.le q.1 q.2) = oracle' (.le q.1 q.2) := by
    rintro ⟨a, b⟩ hq
    simp only [horacle, oracle', LEQuery.oracleOf_le, toBottom]
    by_cases hab : a = b
    · subst hab
      simp [refl_of r a]
    have hw := hwin (a, b) hq hab
    simp only [winner_def, horacle] at hw
    by_cases ha : a = y
    · subst ha
      by_cases h : r a b
      · simp [h]
      · simp [h] at hw
    · by_cases hb : b = y
      · subst hb
        by_cases h : r a b
        · simp [h] at hw
        · simp [h, ha]
      · simp [ha, hb]
  have hm' : (find xs).eval oracle' = some (mn, mx) := by
    rw [← eval_eq_of_comparisons _ _ _ hagree, hm]
  rcases (hfind.le_of_mem xs oracle' (toBottom r y) (fun _ _ => rfl) mn mx hm' y hy).1 with
    h | ⟨h, _⟩
  · exact hyn h.symm
  · exact h rfl

/-! ## The adversary -/

/-- The oracle comparing the values of `v : α → ℤ`. -/
def valOracle (v : α → ℤ) : {ι : Type} → LEQuery α ι → ι :=
  LEQuery.oracleOf fun a b => decide (v a ≤ v b)

@[simp] theorem valOracle_le (v : α → ℤ) (a b : α) :
    valOracle v (.le a b) = decide (v a ≤ v b) := by
  simp [valOracle]

section Adversary

variable [DecidableEq α]

/-- The winners of the comparisons between different elements in `cs`. -/
private def winsOf (oracle : {ι : Type} → LEQuery α ι → ι) (cs : List (α × α)) : Finset α :=
  ((cs.filter fun q => q.1 ≠ q.2).map (winner oracle)).toFinset

/-- The losers of the comparisons between different elements in `cs`. -/
private def lossesOf (oracle : {ι : Type} → LEQuery α ι → ι) (cs : List (α × α)) : Finset α :=
  ((cs.filter fun q => q.1 ≠ q.2).map (loser oracle)).toFinset

private theorem winsOf_cons (oracle : {ι : Type} → LEQuery α ι → ι) (a b : α)
    (cs : List (α × α)) :
    winsOf oracle ((a, b) :: cs) =
      if a = b then winsOf oracle cs else insert (winner oracle (a, b)) (winsOf oracle cs) := by
  by_cases h : a = b <;> simp [winsOf, h]

private theorem lossesOf_cons (oracle : {ι : Type} → LEQuery α ι → ι) (a b : α)
    (cs : List (α × α)) :
    lossesOf oracle ((a, b) :: cs) =
      if a = b then lossesOf oracle cs else insert (loser oracle (a, b)) (lossesOf oracle cs) := by
  by_cases h : a = b <;> simp [lossesOf, h]

/-- The potential of an element with won comparisons `W` and lost comparisons `L`: `1` if it has
taken part in no comparison yet, `2` if it has only won or only lost, and `4` if both. -/
private def pot (W L : Finset α) (x : α) : ℕ :=
  (if x ∈ W then 2 else 0) + (if x ∈ L then 2 else 0) + (if x ∉ W ∧ x ∉ L then 1 else 0)

/-- The total potential of the elements of `S`. -/
private def Pot (S W L : Finset α) : ℕ := ∑ x ∈ S, pot W L x

/-- The increase of the potential of `w` when it wins. -/
private def incW (W L : Finset α) (w : α) : ℕ := if w ∈ W then 0 else if w ∈ L then 2 else 1

/-- The increase of the potential of `l` when it loses. -/
private def incL (W L : Finset α) (l : α) : ℕ := if l ∈ L then 0 else if l ∈ W then 2 else 1

private theorem pot_insert_le (W L : Finset α) {w l : α} (h : w ≠ l) (x : α) :
    pot (insert w W) (insert l L) x ≤
      pot W L x + (if x = w then incW W L w else 0) + (if x = l then incL W L l else 0) := by
  by_cases hw : x = w
  · subst hw
    have hl : x ≠ l := h
    by_cases hW : x ∈ W <;> by_cases hL : x ∈ L <;> simp [pot, incW, hW, hL, hl]
  · by_cases hl : x = l
    · subst hl
      by_cases hW : x ∈ W <;> by_cases hL : x ∈ L <;> simp [pot, incL, hW, hL, hw]
    · simp [pot, hw, hl]

private theorem Pot_insert_le (S W L : Finset α) {w l : α} (h : w ≠ l) :
    Pot S (insert w W) (insert l L) ≤ Pot S W L + incW W L w + incL W L l := by
  calc Pot S (insert w W) (insert l L)
      ≤ ∑ x ∈ S, (pot W L x + (if x = w then incW W L w else 0) +
          (if x = l then incL W L l else 0)) :=
        Finset.sum_le_sum fun x _ => pot_insert_le W L h x
    _ ≤ Pot S W L + incW W L w + incL W L l := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.sum_ite_eq']
        unfold Pot
        split_ifs <;> omega

/-- `v'` is obtained from `v` by raising elements that have only won and lowering elements that
have only lost. Such changes keep the answers to all past comparisons. -/
private def Adj (W L : Finset α) (v v' : α → ℤ) : Prop :=
  ∀ x, (x ∈ W → v x ≤ v' x) ∧ (x ∈ L → v' x ≤ v x)

omit [DecidableEq α] in
private theorem Adj.rfl' {W L : Finset α} {v : α → ℤ} : Adj W L v v :=
  fun _ => ⟨fun _ => le_rfl, fun _ => le_rfl⟩

omit [DecidableEq α] in
private theorem Adj.trans' {W L W₁ L₁ : Finset α} {v v₁ v₂ : α → ℤ} (h₁ : Adj W L v v₁)
    (h₂ : Adj W₁ L₁ v₁ v₂) (hW : W ⊆ W₁) (hL : L ⊆ L₁) : Adj W L v v₂ := fun x =>
  ⟨fun hx => ((h₁ x).1 hx).trans ((h₂ x).1 (hW hx)),
    fun hx => ((h₂ x).2 (hL hx)).trans ((h₁ x).2 hx)⟩

omit [DecidableEq α] in
/-- `b` can be made to win against `a`, unless `b` has lost and `a` has won before. -/
private theorem exists_le_of {W L : Finset α} {a b : α} (v : α → ℤ) (hab : a ≠ b)
    (h : b ∉ L ∨ a ∉ W) : ∃ v₁, Adj W L v v₁ ∧ v₁ a ≤ v₁ b := by
  classical
  rcases h with hb | ha
  · refine ⟨Function.update v b (max (v b) (v a)), fun x => ⟨fun _ => ?_, fun hx => ?_⟩, ?_⟩
    · by_cases hx : x = b
      · subst hx; simp
      · simp [hx]
    · have : x ≠ b := by rintro rfl; exact hb hx
      simp [this]
    · simp [hab]
  · refine ⟨Function.update v a (min (v a) (v b)), fun x => ⟨fun hx => ?_, fun _ => ?_⟩, ?_⟩
    · have : x ≠ a := by rintro rfl; exact ha hx
      simp [this]
    · by_cases hx : x = a
      · subst hx; simp
      · simp [hx]
    · simp [hab.symm]

omit [DecidableEq α] in
/-- `a` can be made to win against `b`, unless `a` has lost and `b` has won before. -/
private theorem exists_lt_of {W L : Finset α} {a b : α} (v : α → ℤ) (hab : a ≠ b)
    (h : a ∉ L ∨ b ∉ W) : ∃ v₁, Adj W L v v₁ ∧ v₁ b < v₁ a := by
  classical
  rcases h with ha | hb
  · refine ⟨Function.update v a (max (v a) (v b + 1)), fun x => ⟨fun _ => ?_, fun hx => ?_⟩, ?_⟩
    · by_cases hx : x = a
      · subst hx; simp
      · simp [hx]
    · have : x ≠ a := by rintro rfl; exact ha hx
      simp [this]
    · simp [hab.symm]
  · refine ⟨Function.update v b (min (v b) (v a - 1)), fun x => ⟨fun hx => ?_, fun _ => ?_⟩, ?_⟩
    · have : x ≠ b := by rintro rfl; exact hb hx
      simp [this]
    · by_cases hx : x = b
      · subst hx; simp
      · simp [hx]
    · simp [hab]

/-- One step of the adversary: it answers the comparison `(a, b)` of two different elements,
possibly after adjusting the values, so that the potential grows by at most `2`. -/
private theorem step (S W L : Finset α) (v : α → ℤ) {a b : α} (hab : a ≠ b) :
    ∃ (ans : Bool) (v₁ : α → ℤ), Adj W L v v₁ ∧ ans = decide (v₁ a ≤ v₁ b) ∧
      Pot S (insert (if ans then b else a) W) (insert (if ans then a else b) L) ≤
        Pot S W L + 2 := by
  by_cases hA : (a ∉ L ∨ b ∉ W) ∧ incW W L a + incL W L b ≤ 2
  · obtain ⟨v₁, hadj, hlt⟩ := exists_lt_of v hab hA.1
    refine ⟨false, v₁, hadj, (decide_eq_false (not_le.mpr hlt)).symm, ?_⟩
    simpa using (Pot_insert_le S W L hab).trans (by omega)
  by_cases hB : b ∉ L ∨ a ∉ W
  · obtain ⟨v₁, hadj, hle⟩ := exists_le_of v hab hB
    refine ⟨true, v₁, hadj, (decide_eq_true hle).symm, ?_⟩
    have hinc : incW W L b + incL W L a ≤ 2 := by
      by_cases ha₁ : a ∈ W <;> by_cases ha₂ : a ∈ L <;> by_cases hb₁ : b ∈ W <;>
        by_cases hb₂ : b ∈ L <;> simp_all [incW, incL]
    simpa using (Pot_insert_le S W L (Ne.symm hab)).trans (by omega)
  · -- Both elements have won and lost before: the answer is forced and gives no new unit.
    have haW : a ∈ W := by by_contra h; exact hB (Or.inr h)
    have hbL : b ∈ L := by by_contra h; exact hB (Or.inl h)
    have haL : a ∈ L := by
      by_contra h; exact hA ⟨Or.inl h, by simp [incW, incL, haW, hbL]⟩
    have hbW : b ∈ W := by
      by_contra h; exact hA ⟨Or.inr h, by simp [incW, incL, haW, hbL]⟩
    refine ⟨decide (v a ≤ v b), v, Adj.rfl', rfl, ?_⟩
    cases decide (v a ≤ v b) <;> simp [Finset.insert_eq_of_mem, haW, haL, hbW, hbL]

/-- The adversary: for every program, there are values whose oracle makes the potential of the
winners and losers along the run grow by at most `2` per comparison, from any starting state. -/
private theorem adversary {β : Type} (S : Finset α) :
    ∀ (p : FreeM (LEQuery α) β) (v : α → ℤ) (W L : Finset α), ∃ v' : α → ℤ, Adj W L v v' ∧
      Pot S (W ∪ winsOf (valOracle v') (comparisons (valOracle v') p))
        (L ∪ lossesOf (valOracle v') (comparisons (valOracle v') p)) ≤
        Pot S W L + 2 * (comparisons (valOracle v') p).length
  | .pure _, v, W, L => ⟨v, Adj.rfl', by rw [comparisons_pure]; simp [winsOf, lossesOf]⟩
  | .liftBind (.le a b) cont, v, W, L => by
    by_cases hab : a = b
    · subst hab
      obtain ⟨v', hadj, hpot⟩ := adversary S (cont true) v W L
      refine ⟨v', hadj, ?_⟩
      have hans : valOracle v' (.le a a) = true := by simp
      rw [comparisons_liftBind, hans, winsOf_cons, lossesOf_cons]
      simp only [↓reduceIte, List.length_cons]
      omega
    · obtain ⟨ans, v₁, hadj₁, hans₁, hpot₁⟩ := step S W L v hab
      obtain ⟨v', hadj', hpot'⟩ := adversary S (cont ans) v₁
        (insert (if ans then b else a) W) (insert (if ans then a else b) L)
      have hw := (hadj' (if ans then b else a)).1 (Finset.mem_insert_self _ _)
      have hl := (hadj' (if ans then a else b)).2 (Finset.mem_insert_self _ _)
      have hans : valOracle v' (.le a b) = ans := by
        cases ans
        · simp only [Bool.false_eq_true, ↓reduceIte] at hw hl
          have := (decide_eq_false_iff_not.mp hans₁.symm)
          simp only [valOracle_le, decide_eq_false_iff_not, not_le]
          omega
        · simp only [↓reduceIte] at hw hl
          have := (decide_eq_true_iff.mp hans₁.symm)
          simp only [valOracle_le, decide_eq_true_eq]
          omega
      refine ⟨v', hadj₁.trans' hadj' (Finset.subset_insert _ _) (Finset.subset_insert _ _), ?_⟩
      rw [comparisons_liftBind, hans, winsOf_cons, lossesOf_cons]
      simp only [hab, ↓reduceIte, winner_def, loser_def, hans, List.length_cons]
      rw [Finset.union_insert, Finset.union_insert, ← Finset.insert_union, ← Finset.insert_union]
      omega

end Adversary

/-! ## The lower bound -/

/-- **Lower bound for finding the minimum and the maximum.** For every correct comparison-based
min-max finder and every list of `n` distinct elements, there is an oracle (given by integer
values, so implementing a total preorder) on which it makes at least `⌈3n/2⌉ - 2` queries. -/
theorem IsMinMaxFinder.exists_oracle_le_countQueries
    {find : List α → FreeM (LEQuery α) (Option (α × α))} (hfind : IsMinMaxFinder find)
    (xs : List α) (hxs : xs.Nodup) :
    ∃ v : α → ℤ, (3 * xs.length + 1) / 2 - 2 ≤ (find xs).countQueries (valOracle v) := by
  classical
  set S := xs.toFinset
  obtain ⟨v, -, hpot⟩ := adversary S (find xs) 0 ∅ ∅
  refine ⟨v, ?_⟩
  rw [← length_comparisons]
  by_cases hne : xs = []
  · simp [hne]
  obtain ⟨⟨mn, mx⟩, hm⟩ := Option.isSome_iff_exists.mp (hfind.isSome xs (valOracle v) hne)
  let r : α → α → Prop := fun a b => v a ≤ v b
  have : Std.Total r := ⟨fun a b => le_total (v a) (v b)⟩
  have : IsTrans α r := ⟨fun _ _ _ => le_trans⟩
  have horacle : ∀ a b, valOracle v (.le a b) = decide (r a b) := fun _ _ => rfl
  set cs := comparisons (valOracle v) (find xs)
  -- Every element other than `mn` has won and every element other than `mx` has lost.
  have hW : ∀ y ∈ S, y ≠ mn → y ∈ winsOf (valOracle v) cs := by
    intro y hy hyn
    obtain ⟨q, hq, hne, hwin⟩ :=
      hfind.exists_winner xs _ r horacle hm (List.mem_toFinset.mp hy) hyn
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, by simpa⟩, hwin⟩)
  have hL : ∀ y ∈ S, y ≠ mx → y ∈ lossesOf (valOracle v) cs := by
    intro y hy hyx
    obtain ⟨q, hq, hne, hlose⟩ :=
      hfind.exists_loser xs _ r horacle hm (List.mem_toFinset.mp hy) hyx
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, by simpa⟩, hlose⟩)
  -- So the final potential is at least `4n - 4`.
  have hlow :
      4 * S.card ≤ Pot S (∅ ∪ winsOf (valOracle v) cs) (∅ ∪ lossesOf (valOracle v) cs) + 4 := by
    calc 4 * S.card = ∑ y ∈ S, 4 := by simp [mul_comm]
      _ ≤ ∑ y ∈ S, (pot (∅ ∪ winsOf (valOracle v) cs) (∅ ∪ lossesOf (valOracle v) cs) y +
            ((if y = mn then 2 else 0) + (if y = mx then 2 else 0))) := by
          refine Finset.sum_le_sum fun y hy => ?_
          have hw := hW y hy
          have hl := hL y hy
          by_cases hyn : y = mn <;> by_cases hyx : y = mx <;>
            simp only [pot, Finset.empty_union, hyn, hyx, ↓reduceIte] at hw hl ⊢ <;>
            split_ifs <;> simp_all
      _ ≤ _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
            Finset.sum_ite_eq']
          unfold Pot
          split_ifs <;> omega
  have hP0 : Pot S ∅ ∅ = S.card := by simp [Pot, pot]
  have hS : S.card = xs.length := List.toFinset_card_of_nodup hxs
  omega

/-- Any correct min-max finder on an infinite type has query complexity at least `⌈3n/2⌉ - 2` on
inputs of size `n`. -/
theorem IsMinMaxFinder.lowerBound [Infinite α]
    {find : List α → FreeM (LEQuery α) (Option (α × α))} (hfind : IsMinMaxFinder find) :
    LowerBound find List.length (fun n => (3 * n + 1) / 2 - 2) := by
  intro n
  let xs := (List.range n).map (Infinite.natEmbedding α)
  have hxs : xs.Nodup := (List.nodup_range).map (Infinite.natEmbedding α).injective
  obtain ⟨v, hv⟩ := hfind.exists_oracle_le_countQueries xs hxs
  exact ⟨xs, by simp [xs], valOracle v, by simpa [xs] using hv⟩

/-- The pairwise scan is optimal: on every list of distinct elements, every correct min-max finder
makes at least as many queries as `minMax` on some oracle. -/
theorem minMax_optimal {find : List α → FreeM (LEQuery α) (Option (α × α))}
    (hfind : IsMinMaxFinder find) (xs : List α) (hxs : xs.Nodup) :
    ∃ v : α → ℤ, ∀ oracle : {ι : Type} → LEQuery α ι → ι,
      (minMax xs).countQueries oracle ≤ (find xs).countQueries (valOracle v) := by
  obtain ⟨v, hv⟩ := hfind.exists_oracle_le_countQueries xs hxs
  exact ⟨v, fun oracle => (countQueries_minMax oracle xs).trans_le hv⟩

end Cslib.Query
