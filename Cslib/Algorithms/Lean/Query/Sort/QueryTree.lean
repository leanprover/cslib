/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Kim Morrison, Shreyas Srinivas
-/
module

public import Cslib.Algorithms.Lean.Query.QueryTree
public import Mathlib.Data.Set.Function
public import Mathlib.Combinatorics.Pigeonhole

/-! # Lower-Bound Lemma for Query Trees

`QueryTree.exists_queriesOn_ge_clog`: if `n` oracles produce `n` distinct evaluation results
from a query tree with `Fintype` responses, then one of those oracles makes at least
`⌈log_{|R|} n⌉` queries.

The proof uses the adversarial/partition argument: at each query node, the `n` oracles split by
their answer into `|R|` groups; the largest group (size ≥ ⌈n/|R|⌉) still produces distinct results
in the corresponding subtree, and the induction proceeds there.

The proof works over an arbitrary `Finset ι` of oracle indices (avoiding re-indexing via
`Fintype.equivFin`), then derives the `Fin n` version as a corollary.
-/

open Cslib.Query

public section

namespace Cslib.Query.QueryTree

/-- Finset-based version: if the oracles indexed by `S` produce `|S|`-many distinct evaluation
    results, then some oracle in `S` makes at least `⌈log_{|R|} |S|⌉` queries. -/
private theorem exists_mem_queriesOn_ge_clog [Fintype R]
    {ι : Type} (t : QueryTree Q R α) (S : Finset ι) (hS : S.Nonempty)
    (oracles : ι → (Q → R))
    (h_inj : Set.InjOn (fun i => t.eval (oracles i)) ↑S) :
    ∃ i ∈ S, t.queriesOn (oracles i) ≥ Nat.clog (Fintype.card R) S.card := by
  classical
  induction t generalizing ι S with
  | pure a =>
    obtain ⟨i, hi⟩ := hS
    exact ⟨i, hi, by simp [queriesOn, Nat.clog_of_right_le_one
      (Finset.card_le_one.mpr fun _ ha _ hb => h_inj ha hb rfl)]⟩
  | query q cont ih =>
    by_cases hle : S.card ≤ 1
    · obtain ⟨i, hi⟩ := hS; exact ⟨i, hi, by simp [Nat.clog_of_right_le_one hle]⟩
    · push Not at hle
      by_cases hR : Fintype.card R ≤ 1
      · obtain ⟨i, hi⟩ := hS; exact ⟨i, hi, by simp [Nat.clog_of_left_le_one hR]⟩
      · push Not at hR
        -- Find b : R such that S.filter (oracles · q = b) has ≥ ⌈|S|/|R|⌉ elements
        have ⟨b, _, hb⟩ : ∃ b ∈ Finset.univ (α := R),
            (S.card - 1) / Fintype.card R < (S.filter (fun i => oracles i q = b)).card := by
          apply Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
            (fun a _ => Finset.mem_univ (oracles a q))
          simp only [Finset.card_univ]
          calc Fintype.card R * ((S.card - 1) / Fintype.card R)
              = (S.card - 1) / Fintype.card R * Fintype.card R := Nat.mul_comm ..
            _ ≤ S.card - 1 := Nat.div_mul_le_self _ _
            _ < S.card := by omega
        set S' := S.filter (fun i => oracles i q = b)
        have hS' : S'.Nonempty :=
          Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hb)
        -- Restricted injectivity: eval through query q cont agrees with cont b on S'
        have h_inj' : Set.InjOn (fun i => (cont b).eval (oracles i)) ↑S' := by
          intro i hi j hj heq
          have him := Finset.mem_coe.mp hi |> Finset.mem_filter.mp
          have hjm := Finset.mem_coe.mp hj |> Finset.mem_filter.mp
          exact h_inj (Finset.mem_coe.mpr him.1) (Finset.mem_coe.mpr hjm.1)
            (by simp [eval, him.2, hjm.2, heq])
        obtain ⟨i, hi, hiq⟩ := ih b S' hS' oracles h_inj'
        have him := Finset.mem_filter.mp hi
        refine ⟨i, him.1, ?_⟩
        simp only [queriesOn_query, him.2]
        calc Nat.clog (Fintype.card R) S.card
            ≤ 1 + Nat.clog (Fintype.card R) S'.card := by
              rw [Nat.clog_of_two_le (by omega) (by omega)]
              have h_ceil : (S.card + Fintype.card R - 1) / Fintype.card R =
                  (S.card - 1) / Fintype.card R + 1 := by
                rw [show S.card + Fintype.card R - 1 = S.card - 1 + Fintype.card R from by omega]
                exact Nat.add_div_right (S.card - 1) (by omega)
              have := Nat.clog_mono_right (Fintype.card R)
                (show (S.card + Fintype.card R - 1) / Fintype.card R ≤ S'.card by omega)
              omega
          _ ≤ 1 + (cont b).queriesOn (oracles i) := by omega

/-- If `n` oracles produce `n` distinct evaluation results from a query tree with `Fintype`
    responses, then one of those oracles makes at least `⌈log_{|R|} n⌉` queries.

    This is the core combinatorial lemma for query complexity lower bounds.
    The proof uses the adversarial/partition argument: at each query node, the `n` oracles
    split by their answer to the query; the largest group (size ≥ ⌈n/|R|⌉) still produces
    distinct results in the corresponding subtree, and the induction proceeds there. -/
theorem exists_queriesOn_ge_clog [Fintype R]
    (t : QueryTree Q R α) (oracles : Fin n → (Q → R))
    (hn : 0 < n)
    (h_inj : Function.Injective (fun i => t.eval (oracles i))) :
    ∃ i : Fin n, t.queriesOn (oracles i) ≥ Nat.clog (Fintype.card R) n := by
  have ⟨i, _, hi⟩ := exists_mem_queriesOn_ge_clog t Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) oracles (h_inj.injOn)
  rw [Finset.card_univ, Fintype.card_fin] at hi
  exact ⟨i, hi⟩

end Cslib.Query.QueryTree

end -- public section
