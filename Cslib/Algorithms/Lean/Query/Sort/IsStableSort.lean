/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.IsSort
import Cslib.Foundations.Data.List.Sort

/-! # IsStableSort: Specification for Stable Comparison Sorts

A comparison sort is *stable* if it keeps elements that compare as equal in their input order.
`IsStableSort sort` states this in the form of `List.sublist_mergeSort` and
`List.sublist_insertionSort`: when the oracle implements a total preorder `r`, every sublist of
the input that is already sorted for `r` is a sublist of the output.

## Main results

* `IsStableSort.filter_eval`: a stable sort lists each equivalence class of `r` in input order.
* `IsStableSort.eval_eq`: all stable comparison sorts produce the same list under any total
  preorder. `IsSort.eval_eq` needs an antisymmetric order; stability fixes how ties are broken,
  so here no antisymmetry is needed.
-/

open Cslib Cslib.Query
open scoped List

public section

namespace Cslib.Query

/-- A `FreeM`-based function is a stable comparison sort if it is a correct comparison sort and,
    when the oracle implements a total preorder, every sorted sublist of the input remains a
    sublist of the output. In particular, equivalent elements keep their input order. -/
structure IsStableSort (sort : List α → FreeM (LEQuery α) (List α)) : Prop
    extends IsSort sort where
  /-- A sublist of the input that is sorted for `r` is a sublist of the output, when the oracle
  implements the total preorder `r`. -/
  sublist : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (_ : ∀ a b, oracle (.le a b) = decide (r a b)) {c : List α},
    c.Pairwise r → c <+ xs → c <+ (sort xs).eval oracle

variable {α : Type} {sort sort₁ sort₂ : List α → FreeM (LEQuery α) (List α)}

/-- A stable sort lists each equivalence class of a total preorder in input order: the elements
    equivalent to `k` appear in the output exactly as they appear in the input. -/
theorem IsStableSort.filter_eval (h : IsStableSort sort) (xs : List α)
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) (k : α) :
    ((sort xs).eval oracle).filter (fun x => decide (r x k ∧ r k x)) =
      xs.filter (fun x => decide (r x k ∧ r k x)) := by
  set p : α → Bool := fun x => decide (r x k ∧ r k x)
  -- The elements equivalent to `k` are pairwise related, so they form a sorted sublist.
  have hpw : (xs.filter p).Pairwise r := by
    refine List.pairwise_of_forall_mem_list fun a ha b hb => ?_
    exact _root_.trans (of_decide_eq_true (List.mem_filter.mp ha).2).1
      (of_decide_eq_true (List.mem_filter.mp hb).2).2
  have hsub := (h.sublist xs oracle r horacle hpw (List.filter_sublist)).filter p
  rw [List.filter_eq_self.mpr fun a ha => (List.mem_filter.mp ha).2] at hsub
  -- The output is a permutation of the input, so the two filters have the same length.
  exact (hsub.eq_of_length ((h.perm xs oracle).filter p).length_eq.symm).symm

/-- All stable comparison sorts produce the same list under an oracle implementing a total
    preorder. Unlike `IsSort.eval_eq`, this needs no antisymmetry: equivalent elements are
    kept in input order by both sorts. -/
theorem IsStableSort.eval_eq (h₁ : IsStableSort sort₁) (h₂ : IsStableSort sort₂)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) (xs : List α) :
    (sort₁ xs).eval oracle = (sort₂ xs).eval oracle :=
  ((h₁.perm xs oracle).trans (h₂.perm xs oracle).symm).eq_of_pairwise_of_filter_eq
    (h₁.sorted xs oracle r horacle) (h₂.sorted xs oracle r horacle) fun k =>
      (h₁.filter_eval xs oracle r horacle k).trans (h₂.filter_eval xs oracle r horacle k).symm

end Cslib.Query
