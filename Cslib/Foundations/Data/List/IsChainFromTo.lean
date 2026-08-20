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
  head : chain.head ne_nil = a
  last : chain.getLast ne_nil = b

/-- Create a `List.IsChainFromTo` from a non-empty `List.IsChain`. -/
theorem List.IsChainFromTo.of_isChain_ne_nil
    (chain : List α) (hc : chain.IsChain r) (h_ne_nil : chain ≠ []) :
    List.IsChainFromTo r chain (chain.head h_ne_nil) (chain.getLast h_ne_nil) :=
  ⟨hc, h_ne_nil, rfl, rfl⟩

/-- Restatement of `head_eq`, but tagged with grind. -/
@[grind →]
lemma List.IsChainFromTo.head_eq (hc : chain.IsChainFromTo r a b) :
    chain.head hc.ne_nil = a :=
  hc.head

/-- Restatement of `getLast_eq`, but tagged with grind. -/
@[grind →]
lemma List.IsChainFromTo.last_eq (hc : chain.IsChainFromTo r a b) :
    chain.getLast hc.ne_nil = b :=
  hc.last

@[simp, grind ←]
lemma List.IsChainFromTo.singleton {a : α} : List.IsChainFromTo r [a] a a :=
  ⟨List.IsChain.singleton a, by simp, rfl, rfl⟩

/-- If there is an `r`-chain from `a` to `b` with duplicates, then there is a shorter `r`-chain
from `a` to `b` (the one that skips the part between the duplicates).
Note that applying this method iteratively does not necessarily lead to the shortest `r`-chain
from `a` to `b`, since we always keep the initial and final segment. -/
lemma List.IsChainFromTo.exists_length_lt_of_not_nodup
    (hc : chain.IsChainFromTo r a b)
    (h_dup : ¬ chain.Nodup) :
    ∃ chain' : List α, chain'.IsChainFromTo r a b ∧ chain'.length < chain.length := by
  rw [nodup_iff_getElem?_ne_getElem?] at h_dup
  push Not at h_dup
  obtain ⟨i, j, h_ij, h_lt, h_eq⟩ := h_dup
  use chain.take i ++ chain.drop j
  constructor
  · apply IsChainFromTo.mk ((hc.isChain.take _).append (hc.isChain.drop _) ?_)
      (by simp; omega) (by grind) (by grind)
    intro x hx y hy
    rw [List.head?_drop] at hy
    have := hc.isChain.getElem (i := i - 1)
    grind
  · grind
