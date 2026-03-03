/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.QueryTree

/-! # Lower-Bound Lemma for Binary Query Trees

`QueryTree.exists_queriesOn_ge_clog`: if `n` oracles produce `n` distinct evaluation results
from a binary query tree, then one of those oracles makes at least `⌈log₂ n⌉` queries.

The proof uses the adversarial/partition argument: at each query node, the `n` oracles split by
their answer; the larger group (size ≥ ⌈n/2⌉) still produces distinct results in the
corresponding subtree, and the induction proceeds there.
-/

open Cslib.Query

public section

namespace Cslib.Query.QueryTree

/-- In a partition of `Fin n` by a Boolean function into two groups, the larger group has
    size at least `⌈n/2⌉ = (n + 1) / 2`. -/
private theorem exists_large_fiber (p : Fin n → Bool) :
    ∃ b : Bool, (n + 1) / 2 ≤ Fintype.card {i : Fin n // p i = b} := by
  by_contra h
  push_neg at h
  have key : Fintype.card {i : Fin n // p i = true} +
      Fintype.card {i : Fin n // p i = false} = n := by
    have := Fintype.card_congr (α := {i : Fin n // p i = true} ⊕ {i : Fin n // p i = false})
      (β := Fin n)
      { toFun := fun s => match s with | .inl ⟨i, _⟩ => i | .inr ⟨i, _⟩ => i
        invFun := fun i => if h : p i = true then .inl ⟨i, h⟩
          else .inr ⟨i, Bool.eq_false_iff.mpr h⟩
        left_inv := fun s => by rcases s with ⟨i, hi⟩ | ⟨i, hi⟩ <;> simp_all
        right_inv := fun i => by simp only; split_ifs <;> rfl }
    rw [Fintype.card_sum, Fintype.card_fin] at this; exact this
  have ht := h true
  have hf := h false
  omega

/-- If `n` oracles produce `n` distinct evaluation results from a binary query tree,
    then one of those oracles makes at least `⌈log₂ n⌉` queries.

    This is the core combinatorial lemma for query complexity lower bounds.
    The proof uses the adversarial/partition argument: at each query node, the `n` oracles
    split by their answer to the query; the larger group (size ≥ ⌈n/2⌉) still produces
    distinct results in the corresponding subtree, and the induction proceeds there. -/
theorem exists_queriesOn_ge_clog
    (t : QueryTree Q Bool α) (oracles : Fin n → (Q → Bool))
    (hn : 0 < n)
    (h_inj : Function.Injective (fun i => t.eval (oracles i))) :
    ∃ i : Fin n, t.queriesOn (oracles i) ≥ Nat.clog 2 n := by
  induction t generalizing n with
  | pure a =>
    -- All oracles evaluate to the same `a`, so injectivity forces n ≤ 1
    have : n ≤ 1 := by
      by_contra h
      push_neg at h
      exact absurd (h_inj (show a = a from rfl))
        (show (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ by simp [Fin.ext_iff])
    exact ⟨⟨0, hn⟩, by simp [queriesOn, Nat.clog_of_right_le_one this]⟩
  | query q cont ih =>
    -- Partition oracles by their answer to query q
    obtain ⟨b, hm⟩ := exists_large_fiber (fun i => oracles i q)
    set m := Fintype.card {i : Fin n // oracles i q = b}
    -- Re-index the larger fiber as Fin m
    let e := Fintype.equivFin {i : Fin n // oracles i q = b}
    let oracles' : Fin m → (Q → Bool) := fun j => oracles (e.symm j).val
    -- Injectivity transfers to the subtree
    have h_inj' : Function.Injective (fun j => (cont b).eval (oracles' j)) := by
      intro j₁ j₂ h
      have hj₁ := (e.symm j₁).property
      have hj₂ := (e.symm j₂).property
      -- eval through query q cont with oracle answering b goes to cont b
      have he : ∀ j, (QueryTree.query q cont).eval (oracles (e.symm j).val) =
          (cont b).eval (oracles (e.symm j).val) := by
        intro j; simp [eval, (e.symm j).property]
      have := h_inj (show (QueryTree.query q cont).eval (oracles (e.symm j₁).val) =
          (QueryTree.query q cont).eval (oracles (e.symm j₂).val) by rw [he, he]; exact h)
      exact e.symm.injective (Subtype.val_injective this ▸ rfl)
    -- Apply IH to the subtree
    have hm_pos : 0 < m := by omega
    obtain ⟨j, hj⟩ := ih b oracles' hm_pos h_inj'
    -- Lift back to Fin n and add 1 for the root query
    refine ⟨(e.symm j).val, ?_⟩
    have hqb : oracles (e.symm j).val q = b := (e.symm j).property
    simp only [queriesOn_query, hqb]
    -- 1 + queriesOn on subtree ≥ 1 + clog 2 m ≥ clog 2 n
    calc Nat.clog 2 n
        ≤ 1 + Nat.clog 2 m := by
          by_cases h1 : n ≤ 1
          · simp [Nat.clog_of_right_le_one h1]
          · push_neg at h1
            rw [Nat.clog_of_two_le (by omega) (by omega)]
            have := Nat.clog_mono_right 2 (show (n + 2 - 1) / 2 ≤ m by omega)
            omega
      _ ≤ 1 + (cont b).queriesOn (oracles' j) := by omega
      _ = 1 + (cont b).queriesOn (oracles (e.symm j).val) := rfl

end Cslib.Query.QueryTree

end -- public section
