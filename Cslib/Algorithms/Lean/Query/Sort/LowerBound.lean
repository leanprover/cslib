/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas, Eric Wieser
-/
module

public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.IsSort
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
`FreeM.exists_countQueries_ge_clog` with `LEQuery.finiteResponse` /
`LEQuery.cardResponse_le_two` witnessing that all responses come from `Bool`
(cardinality 2).
-/

open Cslib Cslib.Query

public section

theorem Function.Injective.extend_sum_inl_inr (f : α → β) (hf : Function.Injective f) :
    Function.Injective (Function.extend f (Sum.inl : α → α ⊕ β) (Sum.inr : β → α ⊕ β)) := by
  intro x y h
  have h_cases (z : β) : (∃ a, f a = z) ∨ (Function.extend f Sum.inl Sum.inr z = Sum.inr z) := by
    rw [Classical.or_iff_not_imp_left]
    simp +contextual
  rcases h_cases x with ⟨a, rfl⟩ | hx <;> rcases h_cases y with ⟨b, rfl⟩ | hy
  · rw [hf.extend_apply, hf.extend_apply] at h
    exact congr_arg f (Sum.inl.inj h)
  · rw [hf.extend_apply, hy] at h; contradiction
  · rw [hx, hf.extend_apply] at h; contradiction
  · rw [hx, hy] at h
    exact Sum.inr.inj h

instance [Std.Total r] : Std.Total (InvImage r f) where
  total x y := Std.Total.total (f x) (f y)

namespace Cslib.Query

/-! ## InfinitePermOrder: constructing n! distinct total orders -/

/-- Distinguish `n` elements of an infinite type. -/
private noncomputable def infinitePrefix [Infinite α] : α → Fin n ⊕ α :=
  Function.extend (Infinite.natEmbedding α <| Fin.val ·) .inl .inr

@[simp, grind =] private lemma infinitePrefix_natEmbedding_finVal [Infinite α] {n : ℕ} (i : Fin n) :
    infinitePrefix (Infinite.natEmbedding α i.val) = .inl i :=
  (Infinite.natEmbedding α).injective.comp Fin.val_injective |>.extend_apply _ _ _

private theorem infinitePrefix_injective [Infinite α] :
    Function.Injective (infinitePrefix : α → Fin n ⊕ α) :=
  ((Infinite.natEmbedding α).injective.comp Fin.val_injective).extend_sum_inl_inr

/-- A total order on an infinite type `α` that orders `n` embedded elements
    (via `Infinite.natEmbedding`) according to `σ⁻¹`, with embedded elements
    preceding all others, and a well-ordering among non-embedded elements. -/
private noncomputable def InfinitePermOrder [Infinite α] (n : Nat)
    (σ : Equiv.Perm (Fin n)) : α → α → Prop :=
  letI := IsWellOrder.linearOrder (α := α) WellOrderingRel
  InvImage (Sum.Lex (InvImage (· ≤ ·) σ.symm) (· ≤ ·)) infinitePrefix

private noncomputable instance [Infinite α] :
    DecidableRel (InfinitePermOrder (α := α) n σ) := Classical.decRel _

private instance [Infinite α] :
    IsTrans α (InfinitePermOrder (α := α) n σ) := by
  unfold InfinitePermOrder
  infer_instance

private instance [Infinite α] :
    Std.Total (InfinitePermOrder (α := α) n σ) := by
  unfold InfinitePermOrder
  infer_instance

private instance [Infinite α] :
    Std.Antisymm (InfinitePermOrder (α := α) n σ) := by
  have : Std.Antisymm (InvImage (· ≤ ·) σ.symm) := σ.symm.injective.antisymm_onFun _
  exact infinitePrefix_injective.antisymm_onFun _

/-- `InfinitePermOrder` restricted to embedded values matches `σ⁻¹(·) ≤ σ⁻¹(·)`. -/
@[grind =]
private theorem InfinitePermOrder_on_embedded [Infinite α] {i j : Fin n} :
    InfinitePermOrder (α := α) n σ ((Infinite.natEmbedding α) i.val)
      ((Infinite.natEmbedding α) j.val) ↔ σ.symm i ≤ σ.symm j := by
  simp [InfinitePermOrder, InvImage]

/-- `map (ι ∘ Fin.val ∘ σ) (finRange n)` is pairwise sorted by `InfinitePermOrder n σ`. -/
private theorem pairwise_map_InfinitePermOrder [Infinite α] (σ : Equiv.Perm (Fin n)) :
    List.Pairwise (InfinitePermOrder (α := α) n σ)
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

/-! ## Main theorem -/

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
  have hcard : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Fintype.card_perm, Fintype.card_fin]
  let e := Fintype.equivFinOfCardEq hcard
  let progOracles : Fin (Nat.factorial n) → ({ι : Type} → LEQuery α ι → ι) :=
    fun i => LEQuery.oracleOf fun a b => decide (InfinitePermOrder n (e.symm i) a b)
  -- Each oracle produces a unique sorted output
  have eval_eq_map (i) : (sort xs).eval (progOracles i) =
      (List.finRange n).map (fun k => ι ((e.symm i) k).val) := by
    have h_perm := h.perm xs (progOracles i)
    have h_sorted := h.sorted xs (progOracles i)
      (InfinitePermOrder (α := α) n (e.symm i))
      (fun a b => by simp [progOracles])
    exact h_perm.trans (map_perm_of_infinite_embedding (e.symm i)).symm |>.eq_of_pairwise'
      h_sorted (pairwise_map_InfinitePermOrder (e.symm i))
  have h_inj : Function.Injective (fun i => (sort xs).eval (progOracles i)) := by
    intro i j h_eval
    dsimp only at h_eval
    rw [eval_eq_map, eval_eq_map] at h_eval
    exact e.symm.injective (map_infinite_embedding_injective h_eval)
  -- Apply the FreeM lower-bound lemma directly
  obtain ⟨i, hi⟩ := FreeM.exists_countQueries_ge_clog 2
    LEQuery.finiteResponse LEQuery.cardResponse_le_two
    (sort xs) progOracles (Nat.factorial_pos n) h_inj
  exact ⟨progOracles i, hi⟩

end Cslib.Query
