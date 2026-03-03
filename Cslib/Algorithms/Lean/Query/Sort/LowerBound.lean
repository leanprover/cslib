/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Eric Wieser
-/
module

public import Cslib.Algorithms.Lean.Query.LowerBound
public import Cslib.Algorithms.Lean.Query.Sort.MonadicSort
public import Cslib.Algorithms.Lean.Query.Sort.QueryTree
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.FinRange
public import Mathlib.SetTheory.Cardinal.Order

/-! # Comparison Sorting Lower Bound

`IsMonadicSort.lowerBound_infinite`: any correct comparison sort on an infinite type
has query complexity at least `⌈log₂(n!)⌉` for every input size `n`.

The proof constructs `n!` distinct total orders on `α` (one per permutation of `n`
embedded elements), shows they produce distinct sorted outputs via `queryTree_correct`,
and applies `QueryTree.exists_queriesOn_ge_clog`.
-/

open Std.Do Cslib.Query

public section

namespace Cslib.Query

/-- Specializing `IsMonadicSort` to `OracleQueryTree` gives the `QueryTree` evaluation property
    needed for lower bound proofs. For any total order `r`, evaluating the sort's decision tree
    with `r`'s comparison function produces a sorted permutation. -/
theorem IsMonadicSort.queryTree_correct
    {sort : ∀ {m : Type → Type} [Monad m], (α × α → m Bool) → List α → m (List α)}
    (h : IsMonadicSort sort)
    (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Total r]
    (xs : List α) :
    let oracle := fun p : α × α => decide (r p.1 p.2)
    let result := (sort (fun p => QueryTree.ask p) xs :
      QueryTree (α × α) Bool (List α)).eval oracle
    result.Perm xs ∧ result.Pairwise r := by
  have hcmp : PureReturn
      (m := OracleQueryTree (α × α) Bool (fun p => decide (r p.1 p.2)))
      (fun p => QueryTree.ask p) (fun p => decide (r p.1 p.2)) :=
    fun p => by simp [Triple, OracleQueryTree.wp_eq]
  exact ⟨@h.perm _ .pure _ OracleQueryTree.instWPMonad _ hcmp.nonFailing xs trivial,
    @h.sorted r _ _ _ _ .pure _ OracleQueryTree.instWPMonad _ hcmp xs trivial⟩

open Classical in
/-- A total order on an infinite type `α` that orders `n` embedded elements
    (via `Infinite.natEmbedding`) according to `σ⁻¹`, with embedded elements
    preceding all others, and a well-ordering among non-embedded elements. -/
private noncomputable def infinitePermOrder [Infinite α] (n : Nat)
    (σ : Equiv.Perm (Fin n)) (a b : α) : Prop :=
  if ha : ∃ i : Fin n, (Infinite.natEmbedding α) i.val = a then
    if hb : ∃ j : Fin n, (Infinite.natEmbedding α) j.val = b then
      σ.symm ha.choose ≤ σ.symm hb.choose
    else True
  else
    if _ : ∃ j : Fin n, (Infinite.natEmbedding α) j.val = b then False
    else @LE.le α (IsWellOrder.linearOrder (α := α) WellOrderingRel).toLE a b

private noncomputable instance [Infinite α] :
    DecidableRel (infinitePermOrder (α := α) n σ) := Classical.decRel _

private theorem infinitePermOrder.choose_eq [Infinite α] {i : Fin n}
    (h : ∃ j : Fin n, (Infinite.natEmbedding α) j.val = (Infinite.natEmbedding α) i.val) :
    h.choose = i := by
  grind

private instance [Infinite α] :
    IsTrans α (infinitePermOrder (α := α) n σ) where
  trans a b c hab hbc := by
    letI : LinearOrder α := IsWellOrder.linearOrder WellOrderingRel
    unfold infinitePermOrder at *
    by_cases ha : ∃ i : Fin n, (Infinite.natEmbedding α) i.val = a <;>
    by_cases hb : ∃ j : Fin n, (Infinite.natEmbedding α) j.val = b <;>
    by_cases hc : ∃ k : Fin n, (Infinite.natEmbedding α) k.val = c <;>
    grind

private instance [Infinite α] :
    Std.Total (infinitePermOrder (α := α) n σ) where
  total a b := by
    letI : LinearOrder α := IsWellOrder.linearOrder WellOrderingRel
    unfold infinitePermOrder
    by_cases ha : ∃ i : Fin n, (Infinite.natEmbedding α) i.val = a
    · simp only [dite_else_true]
      grind
    · simp_all only [reduceDIte, dite_eq_ite, if_true_left]
      grind

-- This should be a global attribute in Mathlib
attribute [local grind inj] Equiv.injective in
private instance [Infinite α] :
    Std.Antisymm (infinitePermOrder (α := α) n σ) where
  antisymm a b hab hba := by
    letI : LinearOrder α := IsWellOrder.linearOrder WellOrderingRel
    simp only [infinitePermOrder] at hab hba
    by_cases ha : ∃ i : Fin n, (Infinite.natEmbedding α) i.val = a <;>
    by_cases hb : ∃ j : Fin n, (Infinite.natEmbedding α) j.val = b <;>
      simp_all only [↓reduceDIte, not_exists] <;> grind

/-- `infinitePermOrder` restricted to embedded values matches `σ⁻¹(·) ≤ σ⁻¹(·)`. -/
@[grind =]
private theorem infinitePermOrder_on_embedded [Infinite α] {i j : Fin n} :
    infinitePermOrder (α := α) n σ ((Infinite.natEmbedding α) i.val)
      ((Infinite.natEmbedding α) j.val) ↔ σ.symm i ≤ σ.symm j := by
  have hi : ∃ k : Fin n, (Infinite.natEmbedding α) k.val = (Infinite.natEmbedding α) i.val :=
    ⟨i, rfl⟩
  have hj : ∃ k : Fin n, (Infinite.natEmbedding α) k.val = (Infinite.natEmbedding α) j.val :=
    ⟨j, rfl⟩
  grind [infinitePermOrder]

/-- `map (ι ∘ Fin.val ∘ σ) (finRange n)` is pairwise sorted by `infinitePermOrder n σ`. -/
private theorem pairwise_map_infinitePermOrder [Infinite α] (σ : Equiv.Perm (Fin n)) :
    List.Pairwise (infinitePermOrder (α := α) n σ)
      ((List.finRange n).map (fun i => (Infinite.natEmbedding α) (σ i).val)) := by
  rw [List.pairwise_map]
  exact (List.pairwise_le_finRange n).imp fun hab => by grind

/-- `map (ι ∘ Fin.val ∘ σ) (finRange n)` is a permutation of `map (ι ∘ Fin.val) (finRange n)`. -/
private theorem map_perm_of_infinite_embedding [Infinite α] (σ : Equiv.Perm (Fin n)) :
    ((List.finRange n).map (fun i => (Infinite.natEmbedding α) (σ i).val)).Perm
      ((List.finRange n).map (fun i => (Infinite.natEmbedding α) i.val)) := by
  rw [show (fun i => (Infinite.natEmbedding α) (σ i).val) =
      (fun i => (Infinite.natEmbedding α) i.val) ∘ σ from rfl]
  -- TODO: some more general lemma should be `@[grind]`:
  grind [Equiv.Perm.map_finRange_perm]

/-- Different permutations give different `map (ι ∘ Fin.val ∘ σ) (finRange n)`. -/
private theorem map_infinite_embedding_injective [Infinite α] :
    Function.Injective (fun σ : Equiv.Perm (Fin n) =>
      (List.finRange n).map (fun i => (Infinite.natEmbedding α) (σ i).val)) := by
  intro σ τ h
  exact Equiv.ext fun i => by
    have := List.map_inj_left.mp h i (List.mem_finRange i)
    grind

/-- Any correct comparison sort on an infinite type has query complexity at least `⌈log₂(n!)⌉`
    for every input size `n`. -/
theorem IsMonadicSort.lowerBound_infinite [Infinite α]
    {sort : ∀ {m : Type → Type} [Monad m], (α × α → m Bool) → List α → m (List α)}
    (h : IsMonadicSort sort) :
    LowerBound sort List.length (fun n => Nat.clog 2 (Nat.factorial n)) := by
  intro n
  set ι := Infinite.natEmbedding α
  refine ⟨(List.finRange n).map (fun i => ι i.val), by simp, ?_⟩
  set xs := (List.finRange n).map (fun i => ι i.val)
  set tree := (sort (fun p => QueryTree.ask p) xs : QueryTree (α × α) Bool (List α))
  have hcard : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Fintype.card_perm, Fintype.card_fin]
  let e := Fintype.equivFinOfCardEq hcard
  let oracles : Fin (Nat.factorial n) → (α × α → Bool) :=
    fun i p => decide (infinitePermOrder n (e.symm i) p.1 p.2)
  have h_inj : Function.Injective (fun i => tree.eval (oracles i)) := by
    intro i j h_eval
    suffices key : ∀ i, tree.eval (oracles i) =
        (List.finRange n).map (fun k => ι ((e.symm i) k).val) by
      have h_eval' : tree.eval (oracles i) = tree.eval (oracles j) := h_eval
      rw [key, key] at h_eval'
      exact e.symm.injective (map_infinite_embedding_injective h_eval')
    intro i
    have hc := h.queryTree_correct (infinitePermOrder (α := α) n (e.symm i)) xs
    exact hc.1.trans (map_perm_of_infinite_embedding (e.symm i)).symm |>.eq_of_pairwise'
      hc.2 (pairwise_map_infinitePermOrder (e.symm i))
  obtain ⟨i, hi⟩ := QueryTree.exists_queriesOn_ge_clog tree oracles (Nat.factorial_pos n) h_inj
  exact ⟨oracles i, hi⟩

end Cslib.Query

end -- public section
