/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Donald Poindexter, Jr.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

/-!
# BubbleSort on a list

In this file we define `bubble`, `bubbleSortAux`, and `bubbleSort` as algorithms in
`TimeM ℕ (List α)`, where the time counts comparisons.

## Main results

- `bubbleSort_correct`: `bubbleSort` returns a sorted permutation of the input.
- `bubbleSort_time`: the number of comparisons is at most `n.choose 2`.

## References

Bubble sort is classical; this file formalizes the standard invariant that one sweep
moves a maximum element to the end.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

/-- A list is sorted if it satisfies the `Pairwise (· ≤ ·)` predicate. -/
abbrev IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l

/-- One left-to-right sweep of bubble sort, counting comparisons as time cost. -/
def bubble : List α → TimeM ℕ (List α)
  | [] => return []
  | [x] => return [x]
  | x :: y :: xs => do
      ✓
        if x ≤ y then
          let rest ← bubble (y :: xs)
          return x :: rest
        else
          let rest ← bubble (x :: xs)
          return y :: rest

/-- Auxiliary bubble sort with fuel parameter `n`.
Intended for calls where `n = xs.length`. -/
def bubbleSortAux : ℕ → List α → TimeM ℕ (List α)
  | 0, xs => return xs
  | 1, xs => return xs
  | n + 2, xs => do
      let ys ← bubble xs
      match ys with
      | [] => return []
      | [a] => return [a]
      | a :: b :: rest =>
          let init := (a :: b :: rest).dropLast
          let last := (a :: b :: rest).getLast (by simp)
          let sortedInit ← bubbleSortAux (n + 1) init
          return sortedInit ++ [last]

/-- Runs bubble sort on `xs`, counting comparisons as time cost. -/
def bubbleSort (xs : List α) : TimeM ℕ (List α) :=
  bubbleSortAux xs.length xs

section Correctness

open List

/-- `bubble` preserves length. -/
@[simp]
theorem bubble_same_length (xs : List α) : ⟪bubble xs⟫.length = xs.length := by
  fun_induction bubble xs with
  | case1 => simp
  | case2 x => simp
  | case3 x y xs ihT ihF =>
      simp
      split <;> simp [ihT, ihF]

/-- `bubble` is a permutation of the input. -/
theorem bubble_perm (xs : List α) : ⟪bubble xs⟫ ~ xs := by
  fun_induction bubble xs with
  | case1 => simp
  | case2 x => simp
  | case3 x y xs ihT ihF =>
      simp only [bind_pure_comp, ret_bind]
      split
      · exact Perm.cons x ihT
      · exact (Perm.cons y ihF).trans (Perm.swap x y xs)

/-- If `xs ≠ []`, then `⟪bubble xs⟫ ≠ []`. -/
theorem bubble_ne_nil {xs : List α} (hx : xs ≠ []) : ⟪bubble xs⟫ ≠ [] := by
  intro hret
  have hlen0 : 0 = xs.length := by
    simpa [hret] using (bubble_same_length (xs := xs))
  cases xs with
  | nil =>
      cases hx rfl
  | cons a tl =>
      have : Nat.succ tl.length = 0 := by simpa using hlen0.symm
      exact (Nat.succ_ne_zero tl.length this).elim

omit [LinearOrder α] in
/-- If a list has length `n + 2`, then it has the form `a :: b :: rest`. -/
lemma exists_cons_cons_of_length_eq (l : List α) (n : Nat) (h : l.length = n + 2) :
    ∃ a b rest, l = a :: b :: rest := by
  cases l with
  | nil =>
      have h' : (0 : Nat) = Nat.succ (Nat.succ n) := by
        simp at h
      exact False.elim (Nat.noConfusion h')
  | cons a tl =>
      cases tl with
      | nil =>
          have h' : Nat.succ 0 = Nat.succ (Nat.succ n) := by
            simp at h
          have : 0 = Nat.succ n := Nat.succ.inj h'
          exact False.elim (Nat.noConfusion this)
      | cons b rest =>
          exact ⟨a, b, rest, rfl⟩

omit [LinearOrder α] in
/-- `dropLast` shortens a nonempty list by exactly one element. -/
lemma dropLast_length_add_one {l : List α} (hl : l ≠ []) :
    l.dropLast.length + 1 = l.length := by
  have := congrArg List.length (List.dropLast_append_getLast (l := l) hl)
  simpa [List.length_append] using this

/-- Key property: after one sweep, the last element is ≥ every element of the input. -/
theorem bubble_getLast_ge_of_mem (xs : List α) (hx : xs ≠ []) :
    ∀ w, w ∈ xs → w ≤ (⟪bubble xs⟫).getLast (bubble_ne_nil hx) := by
  fun_induction bubble xs with
  | case1 =>
      cases hx rfl
  | case2 x =>
      intro w hw
      simp only [mem_cons, not_mem_nil, or_false] at hw
      subst hw
      simp [bubble]
  | case3 x y xs ihT ihF =>
      intro w hw
      by_cases hxy : x ≤ y
      · have hret : ⟪bubble (x :: y :: xs)⟫ = x :: ⟪bubble (y :: xs)⟫ := by
          simp [bubble, hxy]
        have hne2 : ⟪bubble (y :: xs)⟫ ≠ [] := bubble_ne_nil (by simp)
        have hne1 : ⟪bubble (x :: y :: xs)⟫ ≠ [] := bubble_ne_nil (by simp)
        have hlast :
            (⟪bubble (x :: y :: xs)⟫).getLast hne1
              = (⟪bubble (y :: xs)⟫).getLast hne2 := by
          have hcongr := List.getLast_congr hne1 (by simp) hret
          simpa using
            (hcongr.trans (List.getLast_cons (a := x) (l := ⟪bubble (y :: xs)⟫) hne2))
        have hw' : w = x ∨ w ∈ (y :: xs) := by
          simpa [List.mem_cons] using hw
        cases hw' with
        | inl hwx =>
            cases hwx
            have hy : y ≤ (⟪bubble (y :: xs)⟫).getLast hne2 := by
              exact ihT (by simp) y (by simp)
            have : x ≤ (⟪bubble (y :: xs)⟫).getLast hne2 := by
              exact le_trans hxy hy
            simpa [hlast] using this
        | inr hwyxs =>
            have : w ≤ (⟪bubble (y :: xs)⟫).getLast hne2 := by
              exact ihT (by simp) w hwyxs
            simpa [hlast] using this
      · have hret : ⟪bubble (x :: y :: xs)⟫ = y :: ⟪bubble (x :: xs)⟫ := by
          simp [bubble, hxy]
        have hne2 : ⟪bubble (x :: xs)⟫ ≠ [] := bubble_ne_nil (by simp)
        have hne1 : ⟪bubble (x :: y :: xs)⟫ ≠ [] := bubble_ne_nil (by simp)
        have hlast :
            (⟪bubble (x :: y :: xs)⟫).getLast hne1
              = (⟪bubble (x :: xs)⟫).getLast hne2 := by
          have hcongr := List.getLast_congr hne1 (by simp) hret
          simpa using
            (hcongr.trans (List.getLast_cons (a := y) (l := ⟪bubble (x :: xs)⟫) hne2))
        have hlt : y < x := lt_of_not_ge hxy
        have hw' : w = x ∨ w ∈ (y :: xs) := by
          simpa [List.mem_cons] using hw
        cases hw' with
        | inl hwx =>
            cases hwx
            have : x ≤ (⟪bubble (x :: xs)⟫).getLast hne2 := by
              exact ihF (by simp) x (by simp)
            simpa [hlast] using this
        | inr hwyxs =>
            have hw'' : w = y ∨ w ∈ xs := by
              simpa [List.mem_cons] using hwyxs
            cases hw'' with
            | inl hwy =>
                cases hwy
                have hxlast : x ≤ (⟪bubble (x :: xs)⟫).getLast hne2 := by
                  exact ihF (by simp) x (by simp)
                have : y ≤ (⟪bubble (x :: xs)⟫).getLast hne2 := by
                  exact le_trans (le_of_lt hlt) hxlast
                simpa [hlast] using this
            | inr hwxs =>
                have : w ≤ (⟪bubble (x :: xs)⟫).getLast hne2 := by
                  exact ihF (by simp) w (by simp [hwxs])
                simpa [hlast] using this

/-- If `l` is sorted and all elements are ≤ `x`, then `l ++ [x]` is sorted. -/
theorem IsSorted.append_singleton {l : List α} {x : α}
    (hl : IsSorted l) (hx : ∀ a ∈ l, a ≤ x) : IsSorted (l ++ [x]) := by
  induction l with
  | nil =>
      simp [IsSorted]
  | cons a tl ih =>
      cases hl with
      | cons ha htl =>
          have hx_tl : ∀ b ∈ tl, b ≤ x := by
            intro b hb
            exact hx b (by simp [hb])
          refine List.Pairwise.cons ?_ (by simpa using (ih htl hx_tl))
          intro b hb
          have : b ∈ tl ∨ b = x := by
            simpa using (List.mem_append.mp hb)
          cases this with
          | inl hbtl =>
              exact ha b hbtl
          | inr hbx =>
              subst hbx
              exact hx a (by simp)

/-- `bubbleSortAux` returns a permutation of the input when `xs.length = n`. -/
theorem bubbleSortAux_perm (n : ℕ) (xs : List α) (hn : xs.length = n) :
    ⟪bubbleSortAux n xs⟫ ~ xs := by
  induction n generalizing xs with
  | zero =>
      simp [bubbleSortAux]
  | succ n ih =>
      cases n with
      | zero =>
          simp [bubbleSortAux]
      | succ m =>
          have hblen : ⟪bubble xs⟫.length = m + 2 := by
            simp [hn]
          rcases exists_cons_cons_of_length_eq (⟪bubble xs⟫) m hblen with
            ⟨a, b, rest, hys⟩
          let init := (a :: b :: rest).dropLast
          have hlen_ab : (a :: b :: rest).length = m + 2 := by
            simpa [hys] using hblen
          have hrest_len : rest.length = m := by
            have : rest.length + 2 = m + 2 := by
              simpa using hlen_ab
            exact Nat.add_right_cancel this
          have hinit_len : init.length = m + 1 := by
            simp [init, hrest_len]
          have ih_init : ⟪bubbleSortAux (m + 1) init⟫ ~ init := by
            exact ih init hinit_len
          have hbub : (a :: b :: rest) ~ xs := by
            have : ⟪bubble xs⟫ ~ xs := bubble_perm xs
            simpa [hys] using this
          simp only [bubbleSortAux, dropLast_cons₂, ne_eq, reduceCtorEq, not_false_eq_true,
            getLast_cons, bind_pure_comp, ret_bind, hys, ret_map]
          calc
            ⟪bubbleSortAux (m + 1) init⟫ ++ [(a :: b :: rest).getLast (by simp)]
                ~ init ++ [(a :: b :: rest).getLast (by simp)] := by
                    exact Perm.append ih_init (Perm.refl _)
            _ ~ (a :: b :: rest) := by
                    exact Perm.of_eq
                      (List.dropLast_append_getLast (l := (a :: b :: rest)) (by simp))
            _ ~ xs := hbub

/-- `bubbleSortAux` output is sorted when `xs.length = n`. -/
theorem bubbleSortAux_sorted (n : ℕ) (xs : List α) (hn : xs.length = n) :
    IsSorted ⟪bubbleSortAux n xs⟫ := by
  induction n generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          simp [bubbleSortAux, IsSorted]
      | cons a tl =>
          simp at hn
  | succ n ih =>
      cases n with
      | zero =>
          cases xs with
          | nil =>
              simp at hn
          | cons a tl =>
              cases tl with
              | nil =>
                  simp [bubbleSortAux, IsSorted]
              | cons b rest =>
                  simp at hn
      | succ m =>
          have hx_ne : xs ≠ [] := by
            intro h
            subst h
            simp at hn
          have hblen : ⟪bubble xs⟫.length = m + 2 := by
            simp [hn]
          rcases exists_cons_cons_of_length_eq (⟪bubble xs⟫) m hblen with
            ⟨a, b, rest, hys⟩
          let init := (a :: b :: rest).dropLast
          let last := (a :: b :: rest).getLast (by simp)
          have hlen_ab : (a :: b :: rest).length = m + 2 := by
            simpa [hys] using hblen
          have hrest_len : rest.length = m := by
            have : rest.length + 2 = m + 2 := by
              simpa using hlen_ab
            exact Nat.add_right_cancel this
          have hinit_len : init.length = m + 1 := by
            simp [init, hrest_len]
          have hsorted_init : IsSorted ⟪bubbleSortAux (m + 1) init⟫ := by
            exact ih init hinit_len
          have hperm_init : ⟪bubbleSortAux (m + 1) init⟫ ~ init := by
            exact bubbleSortAux_perm (m + 1) init hinit_len
          have hbound : ∀ z ∈ ⟪bubbleSortAux (m + 1) init⟫, z ≤ last := by
            intro z hz
            have hz_init : z ∈ init := hperm_init.subset hz
            have hz_drop : z ∈ (a :: b :: rest).dropLast := by
              simpa [init] using hz_init
            have hz_ys : z ∈ (a :: b :: rest) := by
              exact List.mem_of_mem_dropLast hz_drop
            have hz_ret : z ∈ ⟪bubble xs⟫ := by
              simpa [hys] using hz_ys
            have hz_xs : z ∈ xs := by
              exact (bubble_perm xs).subset hz_ret
            have hz_last0 :
                z ≤ (⟪bubble xs⟫).getLast (bubble_ne_nil hx_ne) := by
              exact bubble_getLast_ge_of_mem xs hx_ne z hz_xs
            have hgl :
                (⟪bubble xs⟫).getLast (bubble_ne_nil hx_ne) = last := by
              have := List.getLast_congr (bubble_ne_nil hx_ne) (by simp) hys
              simpa [last] using this
            simpa [hgl] using hz_last0
          simp only [bubbleSortAux, dropLast_cons₂, ne_eq, reduceCtorEq, not_false_eq_true,
            getLast_cons, bind_pure_comp, ret_bind, hys, ret_map]
          exact IsSorted.append_singleton hsorted_init hbound

/-- BubbleSort is functionally correct. -/
theorem bubbleSort_correct (xs : List α) :
    IsSorted ⟪bubbleSort xs⟫ ∧ ⟪bubbleSort xs⟫ ~ xs :=
  ⟨bubbleSortAux_sorted xs.length xs rfl,
   bubbleSortAux_perm xs.length xs rfl⟩

end Correctness

section TimeComplexity

/-- One bubble sweep on a list of length `n` costs at most `n - 1` comparisons. -/
@[simp]
theorem bubble_time (xs : List α) : (bubble xs).time ≤ xs.length - 1 := by
  fun_induction bubble xs with
  | case1 =>
      simp
  | case2 x =>
      simp
  | case3 x y xs ihT ihF =>
      by_cases hxy : x ≤ y
      · have htail : (bubble (y :: xs)).time ≤ xs.length := by
          simpa using ihT
        simp [hxy, time_bind, time_tick]
        simpa [Nat.add_comm] using (Nat.add_le_add_left htail 1)
      · have htail : (bubble (x :: xs)).time ≤ xs.length := by
          simpa using ihF
        simp [hxy, time_bind, time_tick]
        simpa [Nat.add_comm] using (Nat.add_le_add_left htail 1)

/-- Recurrence for bubble sort's comparison count. -/
def timeBubbleSortRec : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => (n + 1) + timeBubbleSortRec (n + 1)

/-- The recurrence is bounded by `n.choose 2`. -/
theorem timeBubbleSortRec_le (n : ℕ) : timeBubbleSortRec n ≤ n.choose 2 := by
  fun_induction timeBubbleSortRec n with
  | case1 =>
      simp
  | case2 =>
      simp
  | case3 n ih =>
      simp only [Nat.succ_eq_add_one]
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have h' :
          timeBubbleSortRec (n + 1) + (n + 1) ≤ (n + 1).choose 2 + (n + 1) := by
        exact Nat.add_le_add_right ih (n + 1)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'

/-- Time bound for `bubbleSortAux`: at most `timeBubbleSortRec n` when `xs.length = n`. -/
theorem bubbleSortAux_time_le (n : ℕ) (xs : List α) (hn : xs.length = n) :
    (bubbleSortAux n xs).time ≤ timeBubbleSortRec n := by
  induction n generalizing xs with
  | zero =>
      simp [bubbleSortAux, timeBubbleSortRec]
  | succ n ih =>
      cases n with
      | zero =>
          simp [bubbleSortAux, timeBubbleSortRec]
      | succ m =>
          have hblen : ⟪bubble xs⟫.length = m + 2 := by
            simp [hn]
          rcases exists_cons_cons_of_length_eq (⟪bubble xs⟫) m hblen with
            ⟨a, b, rest, hys⟩
          let init := (a :: b :: rest).dropLast
          have hlen_ab : (a :: b :: rest).length = m + 2 := by
            simpa [hys] using hblen
          have hrest_len : rest.length = m := by
            have : rest.length + 2 = m + 2 := by
              simpa using hlen_ab
            exact Nat.add_right_cancel this
          have hinit_len : init.length = m + 1 := by
            simp [init, hrest_len]
          have ih_init :
              (bubbleSortAux (m + 1) init).time ≤ timeBubbleSortRec (m + 1) := by
            exact ih init hinit_len
          have hb : (bubble xs).time ≤ xs.length - 1 := by
            exact bubble_time (xs := xs)
          have hlen : xs.length - 1 = m + 1 := by
            have hn' : xs.length = m + 2 := by
              simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hn
            simp [hn']
          have hbub : (bubble xs).time ≤ m + 1 := by
            simpa [hlen] using hb
          have htime :
              (bubbleSortAux (m + 2) xs).time
                = (bubble xs).time + (bubbleSortAux (m + 1) init).time := by
            simp [bubbleSortAux, time_bind, hys, init]
          have hrec :
              timeBubbleSortRec (m + 2) = (m + 1) + timeBubbleSortRec (m + 1) := by
            simp [timeBubbleSortRec, Nat.add_assoc]
          calc
            (bubbleSortAux (m + 2) xs).time
                = (bubble xs).time + (bubbleSortAux (m + 1) init).time := htime
            _ ≤ (m + 1) + timeBubbleSortRec (m + 1) := by
                exact Nat.add_le_add hbub ih_init
            _ = timeBubbleSortRec (m + 2) := by
                simp [hrec]

/-- Time complexity of bubbleSort: comparisons ≤ `n.choose 2`. -/
theorem bubbleSort_time (xs : List α) :
    let n := xs.length
    (bubbleSort xs).time ≤ n.choose 2 := by
  simpa [bubbleSort] using
    le_trans (bubbleSortAux_time_le xs.length xs rfl)
      (timeBubbleSortRec_le xs.length)

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
