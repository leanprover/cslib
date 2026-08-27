/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup
public import Mathlib.Logic.Relation

/-! # Chains with a designated start and end

This file defines `List.IsChainFromTo`, a variant of `List.IsChain` that also fixes the first and
last element of the chain. Such a chain is an explicit witness for the fact that its end point is
reachable from its start point, and its length bounds the number of steps that are needed.

## Main definitions

* `List.IsChainFromTo r chain a b`: `chain` is a non-empty list whose adjacent elements are related
  by `r`, whose first element is `a` and whose last element is `b`.

## Main results

* `List.IsChainFromTo.reflTransGen`: the start and the end of a chain are related by
  `Relation.ReflTransGen`.
* `List.IsChainFromTo.head_induction_on`: induction on a chain, peeling off elements at the start.
* `List.IsChainFromTo.exists_length_lt_of_not_nodup`: a chain with duplicates can always be
  shortened.
* `List.IsChainFromTo.exists_nodup`: iterating the above yields a chain without duplicates.
-/

@[expose] public section

namespace List

variable {α : Type*} {r : α → α → Prop} {chain : List α} {a b c : α}

/-- A "chain from to" is a list of elements where adjacent elements relate to each other
(cf. `List.IsChain`) and start and end with specific elements. -/
structure IsChainFromTo {α : Type*} (r : α → α → Prop) (chain : List α) (a b : α) : Prop where
  isChain : chain.IsChain r
  ne_nil : chain ≠ []
  head_eq : chain.head ne_nil = a
  getLast_eq : chain.getLast ne_nil = b

attribute [scoped grind →] IsChainFromTo.head_eq IsChainFromTo.getLast_eq

/-- A chain has at least one element. -/
@[scoped grind →]
lemma IsChainFromTo.length_pos (hc : chain.IsChainFromTo r a b) : 0 < chain.length :=
  List.length_pos_iff.mpr hc.ne_nil

/-- The first element of an `r`-chain from `a` to `b` is `a`. -/
@[scoped grind →]
lemma IsChainFromTo.getElem_zero (hc : chain.IsChainFromTo r a b) :
    chain[0]'hc.length_pos = a := by
  rw [List.getElem_zero]
  exact hc.head_eq

/-- The last element of an `r`-chain from `a` to `b` is `b`. -/
@[scoped grind →]
lemma IsChainFromTo.getElem_length_sub_one (hc : chain.IsChainFromTo r a b) :
    chain[chain.length - 1]'(by have := hc.length_pos; lia) = b := by
  rw [List.getElem_length_sub_one_eq_getLast]
  exact hc.getLast_eq

/-- The start and the end of an `r`-chain are reflexively-transitively related by `r`. -/
theorem IsChainFromTo.reflTransGen (hc : chain.IsChainFromTo r a b) :
    Relation.ReflTransGen r a b := by
  simpa [hc.head_eq, hc.getLast_eq] using
    List.relationReflTransGen_of_exists_isChain chain hc.isChain hc.ne_nil

/-- Create a `List.IsChainFromTo` from a non-empty `List.IsChain`. -/
theorem IsChain.isChainFromTo_of_ne_nil
    {chain : List α} (hc : chain.IsChain r) (h_ne_nil : chain ≠ []) :
    List.IsChainFromTo r chain (chain.head h_ne_nil) (chain.getLast h_ne_nil) :=
  ⟨hc, h_ne_nil, rfl, rfl⟩

/-- A one-element list is an `r`-chain from that element to itself. -/
@[simp, scoped grind ←]
lemma isChainFromTo_singleton : List.IsChainFromTo r [a] a a :=
  ⟨List.IsChain.singleton a, by simp, rfl, rfl⟩

/-- Prepend an `r`-related element to the start of the chain. -/
lemma IsChainFromTo.cons (h : r a b) (hc : chain.IsChainFromTo r b c) :
    (a :: chain).IsChainFromTo r a c where
  isChain := hc.isChain.cons_of_ne_nil hc.ne_nil (hc.head_eq.symm ▸ h)
  ne_nil := cons_ne_nil a chain
  head_eq := head_cons
  getLast_eq := hc.getLast_eq ▸ chain.getLast_cons hc.ne_nil

@[simp, scoped grind =]
lemma isChainFromTo_pair_iff {a a' b b' : α} :
    List.IsChainFromTo r [a, b] a' b' ↔ r a b ∧ a = a' ∧ b = b' := by
  constructor
  · rintro ⟨hc, _, rfl, rfl⟩
    simpa using hc
  · rintro ⟨h, rfl, rfl⟩
    constructor <;> simp_all

/-- Removing the head yields a valid chain. -/
lemma IsChainFromTo.of_cons_cons {x y : α} (hc : (x :: y :: chain).IsChainFromTo r a b) :
    (y :: chain).IsChainFromTo r y b :=
  ⟨hc.isChain.of_cons, cons_ne_nil _ _, head_cons, by grind⟩

/-- Appending a chain and the tail of a second one whose start point equals the end point of the
first yields a valid chain. -/
lemma IsChainFromTo.append_tail (hc : chain.IsChainFromTo r a b) {chain' : List α}
    (hc' : chain'.IsChainFromTo r b c) : (chain ++ chain'.tail).IsChainFromTo r a c where
  isChain := by
    have hb : chain.dropLast ++ [b] = chain :=
      hc.getLast_eq ▸ chain.dropLast_append_getLast hc.ne_nil
    have hb' : [b] ++ chain'.tail = chain' := by simp [←hc'.head_eq]
    rw [←hb] at hc ⊢
    exact hc.isChain.append_overlap (l₃ := chain'.tail) (hb'.symm ▸ hc'.isChain) (cons_ne_nil b [])
  ne_nil := append_ne_nil_of_left_ne_nil hc.ne_nil _
  head_eq := head_append_left hc.ne_nil |>.trans hc.head_eq
  getLast_eq := by grind

/-- Add an `r`-related element to the end of the chain. -/
lemma IsChainFromTo.snoc (hc : chain.IsChainFromTo r a b) (h : r b c) :
    (chain ++ [c]).IsChainFromTo r a c :=
  append_tail hc (chain' := [b, c]) (by simpa)

/-- Appending a chain, dropping its last element and another chain whose start point equals
the end point of the first chain yields a valid chain. -/
lemma IsChainFromTo.append_dropLast (hc : chain.IsChainFromTo r a b) {chain' : List α}
    (hc' : chain'.IsChainFromTo r b c) : (chain.dropLast ++ chain').IsChainFromTo r a c := by
  convert hc.append_tail hc' using 1
  nth_rw 1 [←chain'.cons_head_tail hc'.ne_nil, hc'.head_eq, append_cons, ←hc.getLast_eq,
    dropLast_concat_getLast hc.ne_nil]

/-- Taking the first `i + 1` elements of a chain yields a chain from the same start point to
`chain[i]`. -/
lemma IsChainFromTo.take (hc : chain.IsChainFromTo r a b) {i : ℕ} (hi : i < chain.length) :
    (chain.take (i + 1)).IsChainFromTo r a chain[i] := by
  have : chain.take (i + 1) ≠ [] := by grind only [length_nil, min_def, length_take]
  exact ⟨hc.isChain.take _, this, by grind, by grind [chain.getLast_take this]⟩

/-- Dropping the first `i` elements of a chain yields a chain from `chain[i]` to the same end
point. -/
lemma IsChainFromTo.drop (hc : chain.IsChainFromTo r a b) {i : ℕ} (hi : i < chain.length) :
    (chain.drop i).IsChainFromTo r chain[i] b := by
  have : chain.drop i ≠ [] := ne_nil_iff_length_pos.mpr <| chain.lt_length_drop hi
  refine ⟨hc.isChain.drop _, this, chain.head_drop this, hc.getLast_eq ▸ chain.getLast_drop this⟩

@[elab_as_elim]
lemma IsChainFromTo.head_induction_on
    {motive : ∀ {chain : List α} {a b : α}, chain.IsChainFromTo r a b → Prop}
    (h_refl : ∀ {a : α}, motive (isChainFromTo_singleton (r := r) (a := a)))
    (h_head : ∀ {a b c : α} {chain : List α} (hab : r a b) (hc : chain.IsChainFromTo r b c),
      motive hc → motive (hc.cons hab))
    {chain : List α} {a b : α} (hc : chain.IsChainFromTo r a b) : motive hc := by
  induction htail : chain.tail generalizing chain a with
  | nil => grind => have : chain = [a]; finish
  | cons a' tail ih =>
    obtain rfl : chain = a :: a' :: tail := by grind
    obtain ⟨hrel, hchain⟩ := isChain_cons_cons.mp hc.isChain
    have : (a' :: tail).IsChainFromTo r a' b := hc.of_cons_cons
    exact h_head hrel this (ih this rfl)

/-- Any element of an `r`-chain from `a` to `b` is reflexively-transitively related from `a`. -/
lemma IsChainFromTo.reflTransGen_of_mem (hc : chain.IsChainFromTo r a b) {x : α} (mem : x ∈ chain) :
    Relation.ReflTransGen r a x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
  exact (hc.take hi).reflTransGen

/-- Any element of an `r`-chain from `a` to `b` is reflexively-transitively related to `b`. -/
lemma IsChainFromTo.reflTransGen_of_mem' (hc : chain.IsChainFromTo r a b) {x : α}
    (mem : x ∈ chain) :
    Relation.ReflTransGen r x b := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
  exact (hc.drop hi).reflTransGen

/-- If there is an `r`-chain from `a` to `b` with duplicates, then there is a shorter `r`-chain
from `a` to `b` (the one that skips the part between the duplicates). -/
lemma IsChainFromTo.exists_length_lt_of_not_nodup
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

/-- For any `r`-chain from `a` to `b` there is one without duplicates. -/
lemma IsChainFromTo.exists_nodup (hc : chain.IsChainFromTo r a b) :
    ∃ chain' : List α, chain'.IsChainFromTo r a b ∧ chain'.Nodup := by
  induction hn : chain.length using Nat.strong_induction_on generalizing chain with
  | h n ih =>
    by_cases h_dup : chain.Nodup
    · use chain, hc, h_dup
    · obtain ⟨chain', hc', hlen⟩ := hc.exists_length_lt_of_not_nodup h_dup
      exact ih chain'.length (hn ▸ hlen) hc' rfl

end List
