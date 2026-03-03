/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai, Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.UpperBound
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Defs
import Std.Tactic.Do
import Mathlib.Tactic.Linarith
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Log

open Std.Do Cslib.Query TimeT

set_option mvcgen.warning false

namespace Cslib.Query

/-- The monadic `merge` at `m := Id` agrees with `List.merge`. -/
public theorem id_run_merge (le : α → α → Bool) (xs ys : List α) :
    Id.run (merge (fun p => pure (le p.1 p.2)) xs ys) = List.merge xs ys le := by
  fun_induction merge (m := Id) (fun p => pure (le p.1 p.2)) xs ys with
  | case1 => simp [Id.run_pure]
  | case2 xs => simp [Id.run_pure, List.merge_right]
  | case3 x xs y ys ih_t ih_f =>
    simp only [Id.run_bind, Id.run_pure] at ih_t ih_f ⊢
    rw [List.cons_merge_cons]
    split <;> simp_all

-- Unlike `id_run_merge` above, we don't prove a conformance lemma
-- `id_run_mergeSort : Id.run (mergeSort ...) = List.mergeSort ...`
-- because Lean's `module` system does not expose equational lemmas
-- (e.g. `List.mergeSort.eq_3`) to downstream modules.
-- Instead, we validate our definition via specifications:
-- `merge_perm`, `mergeSort_perm`, and `mergeSort_runsIn`.

/-- `merge` produces a permutation of `xs ++ ys`, for any non-failing monadic comparator. -/
public theorem merge_perm {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (xs ys : List α) :
    ⦃⌜True⌝⦄ merge cmp xs ys ⦃⇓result => ⌜List.Perm result (xs ++ ys)⌝⦄ := by
  fun_induction merge (m := m) cmp xs ys with
  | case1 => mvcgen
  | case2 xs =>
    mvcgen
    · mpure_intro; simp [List.append_nil]
  | case3 x xs y ys ih_t ih_f =>
    mvcgen [ih_t, ih_f, hcmp]
    · mpure_intro; exact List.Perm.cons _ ‹_›
    · mpure_intro
      exact (List.Perm.cons _ ‹_›).trans
        ((List.Perm.swap x y _).trans (List.Perm.cons x (List.perm_middle.symm)))

/-- `mergeSort` produces a permutation of its input, for any non-failing monadic comparator. -/
public theorem mergeSort_perm {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (xs : List α) :
    ⦃⌜True⌝⦄ mergeSort cmp xs ⦃⇓result => ⌜List.Perm result xs⌝⦄ := by
  fun_induction mergeSort (m := m) cmp xs with
  | case1 => mvcgen
  | case2 => mvcgen
  | case3 a b xs lr _ _ ih_left ih_right =>
    have hmerge := merge_perm cmp hcmp
    mvcgen [ih_left, ih_right, hmerge]
    · apply SPred.pure_mono
      intro h_merge
      rename_i _ _ _ h_left _ h_right _
      have hsplit := List.MergeSort.Internal.splitInTwo_fst_append_splitInTwo_snd
        ⟨a :: b :: xs, rfl⟩
      exact h_merge.trans ((h_left.append h_right).trans (.of_eq hsplit))

/-- `merge` uses at most `xs.length + ys.length` queries. -/
public theorem merge_costs (query : (α × α) → TimeM Bool) (hquery : ∀ a, Costs (query a) 1)
    (xs ys : List α) : Costs (merge query xs ys) (xs.length + ys.length) := by
  fun_induction merge (m := TimeM) query xs ys with
  | case1 => exact Costs.pure_le _ _
  | case2 xs => exact Costs.pure_le _ _
  | case3 x xs y ys ih_t ih_f =>
    apply Costs.le
    · exact Costs.bind (hquery (x, y)) fun le =>
        Costs.ite_max le (Costs.map ih_t) (Costs.map ih_f)
    · simp only [List.length_cons]; omega

/-- The key arithmetic inequality for the merge sort recurrence:
`⌈n/2⌉ * clog(⌈n/2⌉) + ⌊n/2⌋ * clog(⌊n/2⌋) + n ≤ n * clog(n)`. -/
private theorem mergeSort_bound (n : ℕ) (hn : 2 ≤ n) :
    ((n + 1) / 2) * Nat.clog 2 ((n + 1) / 2) +
      (n / 2 * Nat.clog 2 (n / 2) + ((n + 1) / 2 + n / 2)) ≤
      n * Nat.clog 2 n := by
  -- clog n = clog ⌈n/2⌉ + 1
  have hclog := Nat.clog_of_one_lt (by omega : (1 : Nat) < 2) hn
  have hceil : Nat.clog 2 ((n + 1) / 2) + 1 ≤ Nat.clog 2 n := le_of_eq hclog.symm
  have hfloor : Nat.clog 2 (n / 2) + 1 ≤ Nat.clog 2 n :=
    (Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1).trans hceil
  have hsum : (n + 1) / 2 + n / 2 = n := by omega
  have h1 := Nat.mul_le_mul_left ((n + 1) / 2) hceil
  have h2 := Nat.mul_le_mul_left (n / 2) hfloor
  nlinarith [
    Nat.mul_succ ((n + 1) / 2) (Nat.clog 2 ((n + 1) / 2)),
    Nat.mul_succ (n / 2) (Nat.clog 2 (n / 2))]

/-- `mergeSort` uses at most `xs.length * Nat.clog 2 xs.length` queries. -/
public theorem mergeSort_runsIn :
    UpperBound (mergeSort (α := α)) (fun xs => xs.length * Nat.clog 2 xs.length) := by
  change ∀ (query : (α × α) → TimeM Bool), (∀ a, Costs (query a) 1) →
    ∀ xs, Costs (mergeSort query xs) (xs.length * Nat.clog 2 xs.length)
  intro query hquery xs
  fun_induction mergeSort (m := TimeM) query xs with
  | case1 => exact Costs.pure _
  | case2 => exact Costs.pure _
  | case3 a b xs lr _ _ ih_left ih_right =>
    have hperm := mergeSort_perm query (fun p => SPred.pure_intro trivial)
    apply Costs.le
    · exact Costs.bind_spec ih_left (hperm _) fun left h_perm_left =>
        Costs.bind_spec ih_right (hperm _) fun right h_perm_right => by
          have := merge_costs query hquery left right
          rwa [h_perm_left.length_eq, h_perm_right.length_eq] at this
    · simp only [lr.1.2, lr.2.2]
      exact mergeSort_bound _ (by simp only [List.length_cons]; omega)

-- Sorted results

section Sorted

variable (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]

/-- `merge` preserves sortedness and produces a permutation, for any monadic comparator
    with a pure return reflecting `r`. This combined version is needed because the sortedness
    proof requires knowing the result is a permutation of the input. -/
private theorem merge_spec {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : PureReturn cmp (fun p => decide (r p.1 p.2)))
    (xs ys : List α) (hxs : List.Pairwise r xs) (hys : List.Pairwise r ys) :
    ⦃⌜True⌝⦄ merge cmp xs ys
    ⦃⇓result => ⌜List.Pairwise r result ∧ List.Perm result (xs ++ ys)⌝⦄ := by
  fun_induction merge (m := m) cmp xs ys with
  | case1 =>
    mvcgen
  | case2 xs =>
    mvcgen
    · mpure_intro; exact ⟨hxs, by simp⟩
  | case3 x xs y ys ih_t ih_f =>
    have ih_t' := ih_t hxs.of_cons hys
    have ih_f' := ih_f hxs hys.of_cons
    have hcmp' : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓b => ⌜b = decide (r p.1 p.2)⌝⦄ := hcmp
    mvcgen [ih_t', ih_f', hcmp']
    · mpure_intro
      rename_i _ _ hrest
      obtain ⟨hrest_pw, hrest_perm⟩ := hrest
      have hlt : r x y := by simp_all [decide_eq_true_eq]
      exact ⟨List.pairwise_cons.mpr ⟨fun z hz =>
        match List.mem_append.mp (hrest_perm.mem_iff.mp hz) with
        | Or.inl hmem_xs => List.rel_of_pairwise_cons hxs hmem_xs
        | Or.inr hmem_yys =>
          match List.mem_cons.mp hmem_yys with
          | Or.inl h => h ▸ hlt
          | Or.inr hmem_ys => _root_.trans hlt (List.rel_of_pairwise_cons hys hmem_ys),
        hrest_pw⟩, List.Perm.cons _ hrest_perm⟩
    · mpure_intro
      rename_i _ _ hrest
      obtain ⟨hrest_pw, hrest_perm⟩ := hrest
      have hlt : ¬ r x y := by simp_all [decide_eq_true_eq]
      have hyx : r y x := (Std.Total.total y x).resolve_right hlt
      exact ⟨List.pairwise_cons.mpr ⟨fun z hz =>
        match List.mem_cons.mp (hrest_perm.mem_iff.mp hz) with
        | Or.inl h => h ▸ hyx
        | Or.inr hmem =>
          match List.mem_append.mp hmem with
          | Or.inl hmem_xs => _root_.trans hyx (List.rel_of_pairwise_cons hxs hmem_xs)
          | Or.inr hmem_ys => List.rel_of_pairwise_cons hys hmem_ys,
        hrest_pw⟩,
        (List.Perm.cons _ hrest_perm).trans
          ((List.Perm.swap x y _).trans (List.Perm.cons x (List.perm_middle.symm)))⟩

/-- `merge` preserves sortedness, for any monadic comparator with a pure return
    reflecting `r`. -/
public theorem merge_sorted {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : PureReturn cmp (fun p => decide (r p.1 p.2)))
    (xs ys : List α) :
    ⦃⌜List.Pairwise r xs ∧ List.Pairwise r ys⌝⦄ merge cmp xs ys
    ⦃⇓result => ⌜List.Pairwise r result⌝⦄ := by
  simp only [Triple]
  apply SPred.pure_elim'
  intro ⟨hxs, hys⟩
  exact Triple.entails_wp_of_post (merge_spec r cmp hcmp xs ys hxs hys) (by
    simp only [PostCond.entails_noThrow]; intro _; exact SPred.pure_mono And.left)

/-- `mergeSort` produces a sorted list, for any monadic comparator with a pure return
    reflecting `r`. -/
public theorem mergeSort_sorted {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : PureReturn cmp (fun p => decide (r p.1 p.2)))
    (xs : List α) :
    ⦃⌜True⌝⦄ mergeSort cmp xs
    ⦃⇓result => ⌜List.Pairwise r result⌝⦄ := by
  fun_induction mergeSort (m := m) cmp xs with
  | case1 =>
    mvcgen
    · mpure_intro; exact List.Pairwise.nil
  | case2 =>
    mvcgen
    · mpure_intro; exact List.pairwise_singleton r _
  | case3 a b xs lr _ _ ih_left ih_right =>
    apply Triple.bind _ _ ih_left
    intro left
    simp only [Triple]; apply SPred.pure_elim'; intro hleft
    have hmerge : ∀ right, ⦃⌜List.Pairwise r right⌝⦄ merge cmp left right
        ⦃⇓result => ⌜List.Pairwise r result⌝⦄ := by
      intro right; simp only [Triple]; apply SPred.pure_elim'; intro hright
      exact Triple.entails_wp_of_post (merge_spec r cmp hcmp left right hleft hright)
        (by simp only [PostCond.entails_noThrow]; intro _; exact SPred.pure_mono And.left)
    mvcgen [ih_right, hmerge]

/-- At `m := TimeT n`, `merge` preserves sortedness (with a pure comparator). -/
public theorem merge_sorted_timeT {ps : PostShape} [Monad n] [WPMonad n ps]
    (xs ys : List α) :
    ⦃⌜List.Pairwise r xs ∧ List.Pairwise r ys⌝⦄
    merge (m := TimeT n) (fun p => pure (decide (r p.1 p.2))) xs ys
    ⦃⇓result => ⌜List.Pairwise r result⌝⦄ :=
  merge_sorted r _ (PureReturn.pure _) xs ys

/-- At `m := TimeT n`, `mergeSort` produces a sorted list (with a pure comparator). -/
public theorem mergeSort_sorted_timeT {ps : PostShape} [Monad n] [WPMonad n ps]
    (xs : List α) :
    ⦃⌜True⌝⦄
    mergeSort (m := TimeT n) (fun p => pure (decide (r p.1 p.2))) xs
    ⦃⇓result => ⌜List.Pairwise r result⌝⦄ :=
  mergeSort_sorted r _ (PureReturn.pure _) xs

/-- At `m := Id`, `merge` preserves sortedness. -/
public theorem merge_sorted_id
    (xs ys : List α) (hxs : List.Pairwise r xs) (hys : List.Pairwise r ys) :
    List.Pairwise r (Id.run (merge (fun p => pure (decide (r p.1 p.2))) xs ys)) := by
  have := merge_sorted r (m := Id) _ (PureReturn.pure _) xs ys
  simp only [Triple] at this
  exact this ⟨hxs, hys⟩

/-- At `m := Id`, `mergeSort` produces a sorted list. -/
public theorem mergeSort_sorted_id (xs : List α) :
    List.Pairwise r (Id.run (mergeSort (fun p => pure (decide (r p.1 p.2))) xs)) := by
  have := mergeSort_sorted r (m := Id) _ (PureReturn.pure _) xs
  simp only [Triple] at this
  exact this trivial

end Sorted

end Cslib.Query
