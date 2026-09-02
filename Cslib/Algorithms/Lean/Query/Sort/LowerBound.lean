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

/-! ## PrefixPermOrder: constructing n! distinct total orders -/

open scoped Cardinal

variable {n : ℕ}

/-- A constrained version of `Infinite.natEmbedding`. -/
private noncomputable def finEmbedding (h : n ≤ #α) : Fin n ↪ α :=
  Nonempty.some <| by rwa [← Cardinal.le_def, Cardinal.mk_fin]

/-- Distinguish `n` elements of a type. -/
private noncomputable def finPrefix (h : ↑n ≤ #α) : α → Fin n ⊕ α :=
  Function.extend (finEmbedding h) .inl .inr

@[simp, grind =] private lemma finPrefix_natEmbedding_finVal (h : n ≤ #α) (i : Fin n) :
    finPrefix h (finEmbedding h i) = .inl i :=
  (finEmbedding h).injective.extend_apply _ _ _

private theorem finPrefix_injective (h : ↑n ≤ #α) :
    Function.Injective (finPrefix h) :=
  (finEmbedding h).injective.extend_sum_inl_inr

/-- A total order on an type `α` with at least `n` elements, that orders `n` embedded elements
    (via `finEmbedding) according to `σ⁻¹`, with embedded elements
    preceding all others, and a well-ordering among non-embedded elements. -/
private noncomputable def PrefixPermOrder (h : ↑n ≤ #α)
    (σ : Equiv.Perm (Fin n)) : α → α → Prop :=
  letI := IsWellOrder.linearOrder (α := α) WellOrderingRel
  InvImage (Sum.Lex (InvImage (· ≤ ·) σ.symm) (· ≤ ·)) (finPrefix h)

private noncomputable instance (h : ↑n ≤ #α) :
    DecidableRel (PrefixPermOrder h σ) := Classical.decRel _

private instance (h : ↑n ≤ #α) :
    IsTrans α (PrefixPermOrder h σ) := by
  unfold PrefixPermOrder
  infer_instance

private instance (h : ↑n ≤ #α) :
    Std.Total (PrefixPermOrder h σ) := by
  unfold PrefixPermOrder
  infer_instance

private instance (h : ↑n ≤ #α) :
    Std.Antisymm (PrefixPermOrder h σ) := by
  have : Std.Antisymm (InvImage (· ≤ ·) σ.symm) := σ.symm.injective.antisymm_onFun _
  exact finPrefix_injective h |>.antisymm_onFun _

/-- `PrefixPermOrder` restricted to embedded values matches `σ⁻¹(·) ≤ σ⁻¹(·)`. -/
@[grind =]
private theorem PrefixPermOrder_on_embedded (h : ↑n ≤ #α) {i j : Fin n} :
    PrefixPermOrder h σ (finEmbedding h i) (finEmbedding h j) ↔ σ.symm i ≤ σ.symm j := by
  simp [PrefixPermOrder, InvImage]

/-- `map (ι ∘ σ) (finRange n)` is pairwise sorted by `PrefixPermOrder n σ`. -/
private theorem pairwise_map_PrefixPermOrder (h : ↑n ≤ #α) (σ : Equiv.Perm (Fin n)) :
    List.Pairwise (PrefixPermOrder h σ)
      ((List.finRange n).map (fun i => finEmbedding h (σ i))) := by
  rw [List.pairwise_map]
  exact (List.pairwise_le_finRange n).imp fun hab => by grind

/-- `map (ι ∘ σ) (finRange n)` is a permutation of `map ι (finRange n)`. -/
private theorem map_perm_of_finEmbedding (h : ↑n ≤ #α) (σ : Equiv.Perm (Fin n)) :
    ((List.finRange n).map (fun i => finEmbedding h (σ i))).Perm
      ((List.finRange n).map (fun i => finEmbedding h i)) := by
  rw [show (fun i => finEmbedding h (σ i)) =
      (fun i => finEmbedding h i) ∘ σ from rfl]
  grind [Equiv.Perm.map_finRange_perm]

/-- Different permutations give different `map (ι ∘ σ) (finRange n)`. -/
private theorem map_finEmbedding_injective (h : ↑n ≤ #α) :
    Function.Injective (fun σ : Equiv.Perm (Fin n) =>
      (List.finRange n).map (fun i => finEmbedding h (σ i))) := by
  intro σ τ h
  ext i
  have := List.map_inj_left.mp h i (List.mem_finRange i)
  grind

/-! ## Main theorem -/

/-- Any correct comparison sort on an infinite type has query complexity at least `⌈log₂(n!)⌉`
    for every input size `n`. -/
theorem IsSort.lowerBound_infinite [Infinite α]
    {sort : List α → FreeM (LEQuery α) (List α)}
    (hs : IsSort sort) :
    LowerBound sort List.length (fun n => Nat.clog 2 (Nat.factorial n)) := by
  intro n
  have h : n ≤ #α := by
    grw [Cardinal.natCast_le_aleph0, ← Cardinal.infinite_iff]
    infer_instance
  set ι := finEmbedding h
  refine ⟨(List.finRange n).map ι, by simp, ?_⟩
  set xs := (List.finRange n).map ι
  have hcard : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Fintype.card_perm, Fintype.card_fin]
  let e := Fintype.equivFinOfCardEq hcard
  let progOracles : Fin (Nat.factorial n) → ({ι : Type} → LEQuery α ι → ι) :=
    fun i => LEQuery.oracleOf fun a b => decide (PrefixPermOrder h (e.symm i) a b)
  -- Each oracle produces a unique sorted output
  have eval_eq_map (i) : (sort xs).eval (progOracles i) =
      (List.finRange n).map (fun k => ι (e.symm i k)) := by
    have h_perm := hs.perm xs (progOracles i)
    have h_sorted := hs.sorted xs (progOracles i)
      (PrefixPermOrder h (e.symm i))
      (fun a b => by simp [progOracles])
    exact h_perm.trans (map_perm_of_finEmbedding h (e.symm i)).symm |>.eq_of_pairwise'
      h_sorted (pairwise_map_PrefixPermOrder h (e.symm i))
  have h_inj : Function.Injective (fun i => (sort xs).eval (progOracles i)) := by
    intro i j h_eval
    dsimp only at h_eval
    rw [eval_eq_map, eval_eq_map] at h_eval
    exact e.symm.injective (map_finEmbedding_injective h h_eval)
  -- Apply the FreeM lower-bound lemma directly
  obtain ⟨i, hi⟩ := FreeM.exists_countQueries_ge_clog 2
    LEQuery.finiteResponse LEQuery.cardResponse_le_two
    (sort xs) progOracles (Nat.factorial_pos n) h_inj
  exact ⟨progOracles i, hi⟩

end Cslib.Query
