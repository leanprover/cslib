/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas, Eric Wieser
-/
module

public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.IsSort
public import Cslib.Algorithms.Lean.Query.Sort.QueryTree
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.FinRange
public import Mathlib.SetTheory.Cardinal.Order

/-! # Comparison Sorting Lower Bound

`IsSort.lowerBound_infinite`: any correct comparison sort on an infinite type
has query complexity at least `⌈log₂(n!)⌉` for every input size `n`.

The proof constructs `n!` distinct total orders on `α` (one per permutation of `n`
embedded elements), shows they produce distinct sorted outputs, and applies
`QueryTree.exists_queriesOn_ge_clog`.

## FreeM-to-QueryTree Bridge

Since `FreeM (LEQuery α) β` uses an existentially quantified response type per query
(via `FreeM.liftBind`), while `QueryTree` has a fixed response type `R`, we provide a
conversion `FreeM.toQueryTree` that exploits the fact that `LEQuery α` only has one
constructor returning `Bool`. This lets us apply the combinatorial depth lemma on
`QueryTree` and transfer results back to `FreeM`.
-/

open Cslib Cslib.Query

public section

-- ## FreeM-to-QueryTree bridge for LEQuery

namespace Cslib.Query

/-- Convert a `FreeM`-oracle to a `QueryTree`-oracle for `LEQuery`. -/
@[expose] def toQTOracle (oracle : {ι : Type} → LEQuery α ι → ι) : (α × α) → Bool :=
  fun (a, b) => oracle (.le a b)

/-- Convert a `QueryTree`-oracle to a `FreeM`-oracle for `LEQuery`. -/
@[expose] def fromQTOracle (f : (α × α) → Bool) : {ι : Type} → LEQuery α ι → ι
  | _, .le a b => f (a, b)

@[simp] theorem fromQTOracle_le (f : (α × α) → Bool) (a b : α) :
    fromQTOracle f (.le a b) = f (a, b) := rfl

@[simp] theorem toQTOracle_fromQTOracle (f : (α × α) → Bool) :
    toQTOracle (fromQTOracle f) = f := rfl

end Cslib.Query

namespace Cslib.FreeM

/-- Convert a `FreeM (LEQuery α)` program to a `QueryTree (α × α) Bool` decision tree. -/
@[expose] def toQueryTree : FreeM (LEQuery α) β → QueryTree (α × α) Bool β
  | .pure a => .pure a
  | .liftBind (.le a b) cont => .query (a, b) (fun r => toQueryTree (cont r))

/-- Evaluation is preserved by the FreeM-to-QueryTree conversion. -/
@[simp] theorem toQueryTree_eval (oracle : {ι : Type} → LEQuery α ι → ι) :
    (p : FreeM (LEQuery α) β) →
    p.toQueryTree.eval (toQTOracle oracle) = p.eval oracle
  | .pure _ => rfl
  | .liftBind (.le a b) cont => by
    simp only [toQueryTree, QueryTree.eval_query, FreeM.eval, toQTOracle]
    exact toQueryTree_eval oracle (cont (oracle (.le a b)))

/-- Query count is preserved by the FreeM-to-QueryTree conversion. -/
@[simp] theorem toQueryTree_queriesOn (oracle : {ι : Type} → LEQuery α ι → ι) :
    (p : FreeM (LEQuery α) β) →
    p.toQueryTree.queriesOn (toQTOracle oracle) = p.queriesOn oracle
  | .pure _ => rfl
  | .liftBind (.le a b) cont => by
    simp only [toQueryTree, QueryTree.queriesOn_query, FreeM.queriesOn, toQTOracle]
    exact congrArg (1 + ·) (toQueryTree_queriesOn oracle (cont (oracle (.le a b))))

end Cslib.FreeM

namespace Cslib.Query

-- ## infinitePermOrder: constructing n! distinct total orders

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
  grind [Equiv.Perm.map_finRange_perm]

/-- Different permutations give different `map (ι ∘ Fin.val ∘ σ) (finRange n)`. -/
private theorem map_infinite_embedding_injective [Infinite α] :
    Function.Injective (fun σ : Equiv.Perm (Fin n) =>
      (List.finRange n).map (fun i => (Infinite.natEmbedding α) (σ i).val)) := by
  intro σ τ h
  exact Equiv.ext fun i => by
    have := List.map_inj_left.mp h i (List.mem_finRange i)
    grind

-- ## Main theorem

/-- Any correct comparison sort on an infinite type has query complexity at least `⌈log₂(n!)⌉`
    for every input size `n`. -/
theorem IsSort.lowerBound_infinite [Infinite α]
    {sort : List α → FreeM (LEQuery α) (List α)}
    (h : IsSort sort) :
    LowerBound sort List.length (fun n => Nat.clog 2 (Nat.factorial n)) := by
  intro n
  set ι := Infinite.natEmbedding α
  refine ⟨(List.finRange n).map (fun i => ι i.val), by simp, ?_⟩
  set xs := (List.finRange n).map (fun i => ι i.val)
  set tree := (sort xs).toQueryTree
  have hcard : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Fintype.card_perm, Fintype.card_fin]
  let e := Fintype.equivFinOfCardEq hcard
  -- Define FreeM-level oracles, then derive QueryTree oracles from them
  let progOracles : Fin (Nat.factorial n) → ({ι : Type} → LEQuery α ι → ι) :=
    fun i => fromQTOracle (fun p => decide (infinitePermOrder n (e.symm i) p.1 p.2))
  let qtOracles : Fin (Nat.factorial n) → ((α × α) → Bool) :=
    fun i => toQTOracle (progOracles i)
  -- Each oracle produces a unique sorted output
  have h_inj : Function.Injective (fun i => tree.eval (qtOracles i)) := by
    intro i j h_eval
    suffices key : ∀ i, (sort xs).eval (progOracles i) =
        (List.finRange n).map (fun k => ι ((e.symm i) k).val) by
      simp only [tree, qtOracles, FreeM.toQueryTree_eval] at h_eval
      rw [key, key] at h_eval
      exact e.symm.injective (map_infinite_embedding_injective h_eval)
    intro i
    have h_perm := h.perm xs (progOracles i)
    have h_sorted := h.sorted xs (progOracles i)
      (infinitePermOrder (α := α) n (e.symm i))
      (fun a b => by simp [progOracles])
    exact h_perm.trans (map_perm_of_infinite_embedding (e.symm i)).symm |>.eq_of_pairwise'
      h_sorted (pairwise_map_infinitePermOrder (e.symm i))
  -- Apply the depth lemma
  obtain ⟨i, hi⟩ := QueryTree.exists_queriesOn_ge_clog tree qtOracles (Nat.factorial_pos n) h_inj
  refine ⟨progOracles i, ?_⟩
  simp only [tree, qtOracles, FreeM.toQueryTree_queriesOn] at hi
  exact hi

end Cslib.Query

end -- public section
