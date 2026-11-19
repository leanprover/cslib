/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Eric Wieser
-/
module

public import Mathlib.Data.List.Sort
public import Cslib.Foundations.Control.Monad.IsMonadHom
import all Init.Data.List.Sort.Basic

/-!
# A Monadic version of the builtin `List.mergeSort` and Stability Lemmas

This can be instantiated with `Id` to recover the original, or with `TimeM` or `FreeM` for
algorithmic analysis.

We also establish filter-based stability lemmas (`List.filter_merge`, `List.filter_merge_eqv`,
`List.filter_mergeSort`, and `List.mergeSort_stable`) showing that `List.merge` and
`List.mergeSort` preserve the relative order of comparator-equivalent elements.
-/

public section

open Cslib (IsMonadHom)

namespace List

variable {m n} [Monad m] [Monad n]

/-- A monadic version of `List.merge` -/
def mergeM (xs ys : List α) (le : α → α → m Bool) : m (List α) := do
  match xs, ys with
  | [], ys => return ys
  | xs, [] => return xs
  | x :: xs, y :: ys =>
    if ← le x y then
      return x :: (← mergeM xs (y :: ys) le)
    else
      return y :: (← mergeM (x :: xs) ys le)

@[simp, grind =]
theorem nil_mergeM (ys : List α) (le : α → α → m Bool) : mergeM [] ys le = pure ys := by
  simp [mergeM]
@[simp, grind =]
theorem mergeM_right (xs : List α) (le : α → α → m Bool) : mergeM xs [] le = pure xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [mergeM]
@[simp] theorem cons_mergeM_cons (x y : α) (xs ys : List α) (le : α → α → m Bool) :
    mergeM (x :: xs) (y :: ys) le = do
      if ← le x y then
        return x :: (← mergeM xs (y :: ys) le)
      else
        return y :: (← mergeM (x :: xs) ys le) := by
  simp [mergeM]

@[simp↓]
theorem mergeM_pure [LawfulMonad m] (xs ys : List α) (le : α → α → Bool) :
    mergeM xs ys (fun x y => (pure (le x y) : m Bool)) = pure (merge xs ys le) := by
  fun_induction mergeM with grind [merge]

@[simp]
theorem idRun_mergeM (xs ys : List α) (le : α → α → Id Bool) :
    Id.run (mergeM xs ys le) = merge xs ys (fun x y => Id.run <| le x y) :=
  mergeM_pure _ _ _

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_listMergeM {f : {β : Type} → m β → n β}
    (hf : IsMonadHom m n f) (xs ys : List α) (le : α → α → m Bool) :
    f (mergeM xs ys le) = mergeM xs ys (fun x y => f (le x y)) := by
  fun_induction mergeM xs ys le with
  | case1 | case2 => grind
  | case3 x xs y ys ihx ihy => simp [hf.map_bind, hf.map_pure, apply_ite f, ihx, ihy]

/-- A monadic version of `List.mergeSortM` -/
def mergeSortM (xs : List α) (le : α → α → m Bool) : m (List α) :=
  match xs with
  | [] => return []
  | [a] => return [a]
  | a :: b :: xs => do
    let lr := MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩
    mergeM (← mergeSortM lr.1 le) (← mergeSortM lr.2 le) le
termination_by xs.length

@[simp] theorem mergeSortM_nil (le : α → α → m Bool) : mergeSortM [] le = pure [] := by
  simp [mergeSortM]
@[simp] theorem mergeSortM_singleton (a : α) (le : α → α → m Bool) :
    mergeSortM [a] le = pure [a] := by
  simp [mergeSortM]

@[simp↓]
theorem mergeSortM_pure [LawfulMonad m] (xs : List α) (le : α → α → Bool) :
    mergeSortM xs (fun x y => (pure (le x y) : m Bool)) = pure (mergeSort xs le) := by
  fun_induction mergeSort with
  | case1 | case2 => simp
  | case3 a b xs le lr _ _ ih1 ih2 =>
    simp only [mergeSortM]
    rw [ih1, ih2]
    simp

@[simp]
theorem idRun_mergeSortM (xs : List α) (le : α → α → Id Bool) :
    Id.run (mergeSortM xs le) = mergeSort xs (fun x y => Id.run <| le x y) :=
  mergeSortM_pure _ _

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_listMergeSortM {f : {β : Type} → m β → n β}
    (hf : IsMonadHom m n f) (xs : List α) (le : α → α → m Bool) :
    f (mergeSortM xs le) = mergeSortM xs (fun x y => f (le x y)) := by
  fun_induction mergeSortM xs le with
  | case1 | case2 => simp [hf.map_pure]
  | case3 a b xs le ih1 ih2 => simp only [mergeSortM, hf.map_bind, ih1, ih2, hf.map_listMergeM, le]

section Stability

/-- Filtering `List.merge xs ys le` by a predicate `p` whose satisfying elements are pairwise
related by `le` distributes over `++`, provided `xs` is sorted with respect to `le` and `le` is
transitive. -/
theorem filter_merge {le : α → α → Bool} [IsTrans α (fun x y => le x y = true)]
    {p : α → Bool} {xs ys : List α}
    (hxs : xs.Pairwise (fun x y => le x y = true))
    (hp : ∀ ⦃x y⦄, p x = true → p y = true → le x y = true) :
    (xs.merge ys le).filter p = xs.filter p ++ ys.filter p := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ihx =>
    obtain ⟨hx_xs, hxs'⟩ := pairwise_cons.mp hxs
    induction ys with
    | nil => simp
    | cons y ys ihy =>
      rw [cons_merge_cons]
      split <;> rename_i hxy
      · simp only [filter_cons, ihx hxs']
        split <;> simp
      · rw [filter_cons (x := y), ihy]
        by_cases hy : p y = true
        · have h_nil : (x :: xs).filter p = [] := by
            rw [filter_eq_nil_iff]
            intro z hz hpz
            apply hxy
            rcases mem_cons.mp hz with rfl | hz'
            · exact hp hpz hy
            · exact trans_of (fun a b => le a b = true) (hx_xs z hz') (hp hpz hy)
          rw [h_nil]
          simp [hy]
        · simp [hy]

/-- Stability of `List.merge` on equivalence classes: for a transitive comparator `le` and sorted
left input `xs`, filtering `xs.merge ys le` by the equivalence class of `k` preserves the relative
order of elements from `xs` followed by `ys`. -/
theorem filter_merge_eqv {le : α → α → Bool} [IsTrans α (fun x y => le x y = true)]
    {xs ys : List α} (hxs : xs.Pairwise (fun x y => le x y = true)) (k : α) :
    (xs.merge ys le).filter (fun x => le x k && le k x) =
      xs.filter (fun x => le x k && le k x) ++ ys.filter (fun x => le x k && le k x) :=
  filter_merge hxs fun _ _ hx hy => by
    simp only [Bool.and_eq_true] at hx hy
    exact trans_of (fun a b => le a b = true) hx.1 hy.2

/-- Filtering `List.mergeSort xs le` by a predicate `p` whose satisfying elements are pairwise
related by `le` preserves `xs.filter p`, provided `le` is total and transitive. -/
theorem filter_mergeSort (xs : List α) (le : α → α → Bool)
    [Std.Total (fun x y => le x y = true)] [IsTrans α (fun x y => le x y = true)]
    {p : α → Bool} (hp : ∀ ⦃x y⦄, p x = true → p y = true → le x y = true) :
    (xs.mergeSort le).filter p = xs.filter p :=
  match xs with
  | [] => by simp
  | [a] => by simp
  | a :: b :: xs => by
    let lr := MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩
    have : lr.1.1.length < (a :: b :: xs).length := by
      simp only [lr, MergeSort.Internal.splitInTwo_fst, length_take, length_cons]; omega
    have : lr.2.1.length < (a :: b :: xs).length := by
      simp only [lr, MergeSort.Internal.splitInTwo_snd, length_drop, length_cons]; omega
    have hpw : (lr.1.1.mergeSort le).Pairwise (fun x y => le x y = true) :=
      pairwise_mergeSort (le := le)
        (fun _ _ _ h₁ h₂ => trans_of (fun x y => le x y = true) h₁ h₂)
        (fun x y => by
          simpa only [Bool.or_eq_true] using total_of (fun x y => le x y = true) x y)
        lr.1.1
    rw [mergeSort, filter_merge hpw hp, filter_mergeSort lr.1.1 le hp,
      filter_mergeSort lr.2.1 le hp, ← filter_append,
      MergeSort.Internal.splitInTwo_fst_append_splitInTwo_snd]
termination_by xs.length

/-- `List.mergeSort` is stable: for any total and transitive comparator `le`, elements equivalent
to `k` appear in `xs.mergeSort le` in the exact same order as in `xs`. -/
theorem mergeSort_stable (xs : List α) (le : α → α → Bool)
    [Std.Total (fun x y => le x y = true)] [IsTrans α (fun x y => le x y = true)] (k : α) :
    (xs.mergeSort le).filter (fun x => le x k && le k x) =
      xs.filter (fun x => le x k && le k x) :=
  filter_mergeSort xs le fun _ _ hx hy => by
    simp only [Bool.and_eq_true] at hx hy
    exact trans_of (fun a b => le a b = true) hx.1 hy.2

/-- Variant of `List.filter_merge` for a decidable transitive relation `r : α → α → Prop`. -/
theorem filter_merge' {r : α → α → Prop} [DecidableRel r] [IsTrans α r]
    {p : α → Bool} {xs ys : List α}
    (hxs : xs.Pairwise r) (hp : ∀ ⦃x y⦄, p x = true → p y = true → r x y) :
    (xs.merge ys (r · ·)).filter p = xs.filter p ++ ys.filter p := by
  have : IsTrans α (fun x y => decide (r x y) = true) :=
    ⟨fun _ _ _ h₁ h₂ => by
      simp only [decide_eq_true_eq] at h₁ h₂ ⊢
      exact trans_of r h₁ h₂⟩
  exact filter_merge (hxs.imp (by simp)) (fun _ _ hx hy => decide_eq_true (hp hx hy))

/-- Variant of `List.filter_mergeSort` for a decidable total transitive relation
`r : α → α → Prop`. -/
theorem filter_mergeSort' (xs : List α) (r : α → α → Prop)
    [DecidableRel r] [Std.Total r] [IsTrans α r]
    {p : α → Bool} (hp : ∀ ⦃x y⦄, p x = true → p y = true → r x y) :
    (xs.mergeSort (r · ·)).filter p = xs.filter p := by
  have : IsTrans α (fun x y => decide (r x y) = true) :=
    ⟨fun _ _ _ h₁ h₂ => by
      simp only [decide_eq_true_eq] at h₁ h₂ ⊢
      exact trans_of r h₁ h₂⟩
  have : Std.Total (fun x y => decide (r x y) = true) :=
    ⟨fun x y => by simpa only [decide_eq_true_eq] using total_of r x y⟩
  exact filter_mergeSort xs (r · ·) (fun _ _ hx hy => decide_eq_true (hp hx hy))

end Stability

end List
