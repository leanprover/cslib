/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup

/-! # Chains with a designated start and end

This file defines `List.IsChainFromTo`, a variant of `List.IsChain` that also fixes the first and
last element of the chain.

The lemma `List.IsChainFromTo.exists_length_lt_of_not_nodup` shows that a chain with duplicates can
always be shortened.
-/

@[expose] public section

variable {α : Type*} {r : α → α → Prop} {chain : List α} {a b : α}

/-- A "chain from to" is a list of elements where adjacent elements relate to each other
(cf. `List.IsChain`) and start and end with specific elements. -/
structure List.IsChainFromTo {α : Type*} (r : α → α → Prop) (chain : List α) (a b : α) : Prop where
  isChain : chain.IsChain r
  ne_nil : chain ≠ []
  head_eq : chain.head ne_nil = a
  getLast_eq : chain.getLast ne_nil = b

attribute [grind →] List.IsChainFromTo.head_eq List.IsChainFromTo.getLast_eq

/-- Create a `List.IsChainFromTo` from a non-empty `List.IsChain`. -/
theorem List.IsChainFromTo.of_isChain_ne_nil
    (chain : List α) (hc : chain.IsChain r) (h_ne_nil : chain ≠ []) :
    List.IsChainFromTo r chain (chain.head h_ne_nil) (chain.getLast h_ne_nil) :=
  ⟨hc, h_ne_nil, rfl, rfl⟩

@[simp, grind ←]
lemma List.IsChainFromTo.singleton {a : α} : List.IsChainFromTo r [a] a a :=
  ⟨List.IsChain.singleton a, by simp, rfl, rfl⟩

/-- If there is an `r`-chain from `a` to `b` with duplicates, then there is a shorter `r`-chain
from `a` to `b` (the one that skips the part between the duplicates). -/
lemma List.IsChainFromTo.exists_length_lt_of_not_nodup
    (hc : chain.IsChainFromTo r a b)
    (h_dup : ¬ chain.Nodup) :
    ∃ chain' : List α, chain'.IsChainFromTo r a b ∧ chain'.length < chain.length := by
  simp only [nodup_iff_getElem?_ne_getElem?, not_forall, not_not] at h_dup
  obtain ⟨i, j, h_ij, h_lt, h_eq⟩ := h_dup
  use chain.take i ++ chain.drop j
  split_ands
  · apply IsChainFromTo.mk ..
    · apply (hc.isChain.take _).append (hc.isChain.drop _)
      grind [List.head?_drop, hc.isChain.getElem (i := i - 1)]
    · grind [append_eq_nil_iff, drop_eq_nil_iff]
    · grind
    · grind
  · grind

lemma List.IsChainFromTo.exists_noDup (hc : chain.IsChainFromTo r a b) :
    ∃ chain' : List α, chain'.IsChainFromTo r a b ∧ chain'.Nodup := by
  induction hn : chain.length using Nat.strong_induction_on generalizing chain with
  | h n ih =>
    by_cases h_dup : chain.Nodup
    · use chain, hc, h_dup
    · obtain ⟨chain', hc', hlen⟩ := hc.exists_length_lt_of_not_nodup h_dup
      exact ih chain'.length (hn ▸ hlen) hc' rfl
