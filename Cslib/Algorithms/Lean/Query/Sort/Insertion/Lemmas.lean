/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.UpperBound
public import Cslib.Algorithms.Lean.Query.Sort.Insertion.Defs
import Std.Tactic.Do
public import Mathlib.Data.List.Sort

open Std.Do Cslib.Query TimeT

set_option mvcgen.warning false

public section

namespace Cslib.Query

/-- `orderedInsert` produces a permutation of `x :: xs`, for any non-failing monadic comparator. -/
public theorem orderedInsert_perm {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (x : α) (xs : List α) :
    ⦃⌜True⌝⦄ orderedInsert cmp x xs ⦃⇓result => ⌜List.Perm result (x :: xs)⌝⦄ := by
  induction xs with
  | nil =>
    simp only [orderedInsert]
    mvcgen
  | cons y ys ih =>
    simp only [orderedInsert]
    mvcgen [ih, hcmp]
    · mpure_intro; exact (List.Perm.cons _ ‹_›).trans (List.Perm.swap _ _ _)

/-- Variant of `orderedInsert_perm` with a permutation precondition:
    if `sorted` is a permutation of `xs`,
    then `orderedInsert` produces a permutation of `x :: xs`. -/
private theorem orderedInsert_perm' {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (x : α) (xs : List α) (sorted : List α) :
    ⦃⌜List.Perm sorted xs⌝⦄ orderedInsert cmp x sorted
      ⦃⇓ result => ⌜List.Perm result (x :: xs)⌝⦄ := by
  simp only [Triple]
  apply SPred.pure_elim'
  intro hsorted
  exact triple_mono (orderedInsert_perm cmp hcmp x sorted)
    (fun _ hperm => hperm.trans (List.Perm.cons x hsorted))

/-- `insertionSort` produces a permutation of its input, for any non-failing monadic comparator. -/
public theorem insertionSort_perm {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (xs : List α) :
    ⦃⌜True⌝⦄ insertionSort cmp xs ⦃⇓result => ⌜List.Perm result xs⌝⦄ := by
  induction xs with
  | nil =>
    simp only [insertionSort]
    mvcgen
  | cons x xs ih =>
    simp only [insertionSort]
    have := orderedInsert_perm' cmp hcmp x xs
    mvcgen [ih, this]

/-- `orderedInsert` uses at most `xs.length` queries. -/
public theorem orderedInsert_runsIn (x : α) :
    UpperBound (fun cmp xs => orderedInsert cmp x xs) List.length := by
  change ∀ (query : (α × α) → TimeM Bool), (∀ a, TimeT.Costs (query a) 1) →
    ∀ xs, TimeT.Costs (orderedInsert query x xs) xs.length
  intro query hquery xs
  induction xs with
  | nil =>
    simp only [orderedInsert]
    exact Costs.pure _
  | cons y ys ih =>
    dsimp only [orderedInsert]
    apply Costs.le
    · exact Costs.bind (hquery (x, y)) fun lt =>
        Costs.ite lt (Costs.pure_le _ _) (Costs.map ih)
    · simp only [List.length]; omega

/-- `insertionSort` uses at most `xs.length ^ 2` queries. -/
public theorem insertionSort_runsIn :
    UpperBound (insertionSort (α := α)) (fun xs => xs.length ^ 2) := by
  change ∀ (query : (α × α) → TimeM Bool), (∀ a, TimeT.Costs (query a) 1) →
    ∀ xs, TimeT.Costs (insertionSort query xs) (xs.length ^ 2)
  intro query hquery xs
  induction xs with
  | nil =>
    simp only [insertionSort]
    exact Costs.pure _
  | cons x xs ih =>
    dsimp only [insertionSort]
    apply Costs.le
    · exact Costs.bind_spec ih
        (insertionSort_perm query (fun p => SPred.pure_intro trivial) xs)
        fun sorted hperm => by
          have := orderedInsert_runsIn x query hquery sorted
          rwa [List.Perm.length_eq hperm] at this
    · simp only [List.length, Nat.pow_two]; have := Nat.mul_succ xs.length xs.length; grind

/-- The monadic `orderedInsert` at `m := Id` agrees with `List.orderedInsert`. -/
public theorem id_run_orderedInsert (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    Id.run (orderedInsert (fun p => pure (decide (r p.1 p.2))) x xs) =
      List.orderedInsert r x xs := by
  induction xs with
  | nil => simp [orderedInsert, Id.run_pure]
  | cons y ys ih =>
    simp only [orderedInsert, Id.run_bind, Id.run_pure, List.orderedInsert_cons]
    split <;> grind

/-- The monadic `insertionSort` at `m := Id` agrees with `List.insertionSort`. -/
public theorem id_run_insertionSort (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    Id.run (insertionSort (fun p => pure (decide (r p.1 p.2))) xs) =
      List.insertionSort r xs := by
  induction xs with
  | nil => simp [insertionSort, Id.run_pure]
  | cons x xs ih =>
    simp only [insertionSort, Id.run_bind, List.insertionSort_cons, ih]
    exact id_run_orderedInsert r x (List.insertionSort r xs)

-- Sorted results

section Sorted

variable (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]

/-- `orderedInsert` preserves sortedness and produces a permutation, for any monadic comparator
    with a pure return reflecting `r`. This combined version is needed because the sortedness
    proof in the recursive case requires knowing the result is a permutation of the input. -/
private theorem orderedInsert_spec {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : PureReturn cmp (fun p => decide (r p.1 p.2)))
    (x : α) (xs : List α) (hpw : List.Pairwise r xs) :
    ⦃⌜True⌝⦄ orderedInsert cmp x xs
    ⦃⇓result => ⌜List.Pairwise r result ∧ List.Perm result (x :: xs)⌝⦄ := by
  induction xs with
  | nil =>
    simp only [orderedInsert]
    mvcgen [hcmp]
    · mpure_intro; exact ⟨List.pairwise_singleton r x, .refl _⟩
  | cons y ys ih =>
    simp only [orderedInsert]
    have ih' := ih hpw.of_cons
    have hcmp' : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓b => ⌜b = decide (r p.1 p.2)⌝⦄ := hcmp
    mvcgen [ih', hcmp']
    · mpure_intro
      have hlt : r x y := by simp_all [decide_eq_true_eq]
      exact ⟨List.pairwise_cons.mpr ⟨fun z hz =>
        match List.mem_cons.mp hz with
        | Or.inl h => h ▸ hlt
        | Or.inr h => _root_.trans hlt (List.rel_of_pairwise_cons hpw h), hpw⟩, .refl _⟩
    · mpure_intro
      rename_i _ _ _ hrest
      obtain ⟨hrest_pw, hrest_perm⟩ := hrest
      have hlt : ¬ r x y := by simp_all [decide_eq_true_eq]
      exact ⟨List.pairwise_cons.mpr ⟨fun z hz =>
        match List.mem_cons.mp (hrest_perm.mem_iff.mp hz) with
        | Or.inl h => h ▸ (Std.Total.total y x).resolve_right hlt
        | Or.inr h => List.rel_of_pairwise_cons hpw h, hrest_pw⟩,
        (List.Perm.cons y hrest_perm).trans (List.Perm.swap x y ys)⟩

/-- `orderedInsert` preserves sortedness, for any monadic comparator with a pure return
    reflecting `r`. -/
public theorem orderedInsert_sorted {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : PureReturn cmp (fun p => decide (r p.1 p.2)))
    (x : α) (xs : List α) :
    ⦃⌜List.Pairwise r xs⌝⦄ orderedInsert cmp x xs
    ⦃⇓result => ⌜List.Pairwise r result⌝⦄ := by
  simp only [Triple]
  apply SPred.pure_elim'
  intro hpw
  exact triple_mono (orderedInsert_spec r cmp hcmp x xs hpw) (fun _ => And.left)

/-- `insertionSort` produces a sorted list, for any monadic comparator with a pure return
    reflecting `r`. -/
public theorem insertionSort_sorted {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (hcmp : PureReturn cmp (fun p => decide (r p.1 p.2)))
    (xs : List α) :
    ⦃⌜True⌝⦄ insertionSort cmp xs
    ⦃⇓result => ⌜List.Pairwise r result⌝⦄ := by
  induction xs with
  | nil =>
    simp only [insertionSort]
    mvcgen
    · mpure_intro; exact List.Pairwise.nil
  | cons x xs ih =>
    simp only [insertionSort]
    have hord := orderedInsert_sorted r cmp hcmp x
    mvcgen [ih, hord]

/-- At `m := Id`, `orderedInsert` preserves sortedness. -/
public theorem orderedInsert_sorted_id
    (x : α) (xs : List α) (h : List.Pairwise r xs) :
    List.Pairwise r (Id.run (orderedInsert (fun p => pure (decide (r p.1 p.2))) x xs)) := by
  have := orderedInsert_sorted r (m := Id) _ (PureReturn.pure _) x xs
  simp only [Triple] at this
  exact this h

/-- At `m := Id`, `insertionSort` produces a sorted list. -/
public theorem insertionSort_sorted_id (xs : List α) :
    List.Pairwise r (Id.run (insertionSort (fun p => pure (decide (r p.1 p.2))) xs)) := by
  have := insertionSort_sorted r (m := Id) _ (PureReturn.pure _) xs
  simp only [Triple] at this
  exact this trivial

/-- At `m := TimeT n`, `orderedInsert` preserves sortedness (with a pure comparator). -/
public theorem orderedInsert_sorted_timeT {ps : PostShape} [Monad n] [WPMonad n ps]
    (x : α) (xs : List α) :
    ⦃⌜List.Pairwise r xs⌝⦄
    orderedInsert (m := TimeT n) (fun p => pure (decide (r p.1 p.2))) x xs
    ⦃⇓result => ⌜List.Pairwise r result⌝⦄ :=
  orderedInsert_sorted r _ (PureReturn.pure _) x xs

/-- At `m := TimeT n`, `insertionSort` produces a sorted list (with a pure comparator). -/
public theorem insertionSort_sorted_timeT {ps : PostShape} [Monad n] [WPMonad n ps]
    (xs : List α) :
    ⦃⌜True⌝⦄
    insertionSort (m := TimeT n) (fun p => pure (decide (r p.1 p.2))) xs
    ⦃⇓result => ⌜List.Pairwise r result⌝⦄ :=
  insertionSort_sorted r _ (PureReturn.pure _) xs

end Sorted

end Cslib.Query

end -- public section
