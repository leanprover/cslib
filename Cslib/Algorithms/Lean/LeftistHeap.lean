/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Nat.Log

/-!
# Verified Leftist Heap Priority Queue and Heapsort

This file formalizes Chris Okasaki's **Leftist Heap** priority queue together with an associated
heapsort algorithm inside the `TimeM ℕ` time complexity monad.

## Cost Model

- Each element comparison (`x ≤ y`) costs **1 tick** (`✓`).
- Structural pattern matching, node allocation, and cached rank comparisons (`b.rank ≤ a.rank`)
  are metadata operations costing **0 element comparisons**.

## Main Definitions

- `Cslib.Algorithms.Lean.LeftistHeap`: heap-ordered binary tree with cached node ranks.
- `Cslib.Algorithms.Lean.LeftistHeap.IsLeftist`: structural leftist invariant ensuring the right
  spine is shortest and cached ranks equal right-spine lengths.
- `Cslib.Algorithms.Lean.LeftistHeap.IsHeapOrdered`: min-heap ordering invariant.
- `Cslib.Algorithms.Lean.LeftistHeap.Valid`: combined leftist and heap-order invariant.
- `Cslib.Algorithms.Lean.LeftistHeap.merge`, `insert`, `findMin?`, `deleteMin?`: core priority
  queue operations in `TimeM ℕ`.
- `Cslib.Algorithms.Lean.LeftistHeap.fromList`, `popAll`, `heapSort`: heap construction, repeated
  minimum extraction, and verified $O(n \log n)$ heapsort.

## Main Results

- `two_pow_rank_le_size_add_one` and `rank_le_log`: for any leftist heap `h`,
  $2^{\mathrm{rank}(h)} \le |h| + 1$, hence $\mathrm{rank}(h) \le \lfloor \log_2(|h| + 1) \rfloor$.
- `toMultiset_merge`, `size_merge`, `valid_merge`: functional correctness of `merge`.
- `findMin?_isMin`, `valid_deleteMin?`, `toMultiset_deleteMin?`: correctness of min extraction.
- `heapSort_perm` and `heapSort_sorted`: `heapSort` produces a sorted permutation of its input.
- `merge_time_le_rank`, `merge_time_le_log`, `insert_time_le_log`, `deleteMin?_time_le_log`,
  and `heapSort_time_le`: explicit logarithmic and $O(n \log n)$ comparison bounds.

## References

- [Chris Okasaki, *Purely Functional Data Structures*][Okasaki1998]
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- Okasaki's leftist heap: a binary tree storing a cached right-spine rank at each node. -/
inductive LeftistHeap (α : Type u) : Type u where
  /-- The empty leftist heap. -/
  | nil : LeftistHeap α
  /-- A heap node storing cached `rank`, root element `val`, and `left` and `right` subheaps. -/
  | node (rank : ℕ) (val : α) (left right : LeftistHeap α) : LeftistHeap α
  deriving Repr, DecidableEq

namespace LeftistHeap

open TimeM
open scoped List

section Structure

variable {α : Type u}

instance : Inhabited (LeftistHeap α) := ⟨nil⟩

instance : EmptyCollection (LeftistHeap α) := ⟨nil⟩

/-- Returns `true` if and only if the heap is `nil`. -/
def isEmpty : LeftistHeap α → Bool
  | nil => true
  | node _ _ _ _ => false

@[simp] theorem isEmpty_nil : (nil : LeftistHeap α).isEmpty = true := rfl

@[simp] theorem isEmpty_node (rk : ℕ) (x : α) (l r : LeftistHeap α) :
    (node rk x l r).isEmpty = false := rfl

/-- `h.isEmpty = true` if and only if `h = nil`. -/
@[simp]
theorem isEmpty_iff {h : LeftistHeap α} : h.isEmpty = true ↔ h = nil := by
  cases h <;> simp

/-- Cached rank of a leftist heap (`0` for `nil`, stored rank `r` for `node r _ _ _`). -/
def rank : LeftistHeap α → ℕ
  | nil => 0
  | node r _ _ _ => r

@[simp, grind =] theorem rank_nil : (nil : LeftistHeap α).rank = 0 := rfl

@[simp, grind =] theorem rank_node (r : ℕ) (x : α) (l right : LeftistHeap α) :
    (node r x l right).rank = r := rfl

/-- Number of elements stored in the heap. -/
@[simp, grind =]
def size : LeftistHeap α → ℕ
  | nil => 0
  | node _ _ l r => l.size + r.size + 1

/-- Length of the right spine (the path along right children to `nil`). -/
@[simp, grind =]
def rightSpine : LeftistHeap α → ℕ
  | nil => 0
  | node _ _ _ r => r.rightSpine + 1

/-- Multiset of all elements stored in the heap. -/
@[simp]
def toMultiset : LeftistHeap α → Multiset α
  | nil => 0
  | node _ x l r => x ::ₘ (l.toMultiset + r.toMultiset)

/-- The cardinality of `h.toMultiset` equals `h.size`. -/
@[simp]
theorem card_toMultiset (h : LeftistHeap α) : h.toMultiset.card = h.size := by
  induction h with
  | nil => rfl
  | node _ _ l r ihl ihr =>
    simp only [toMultiset, Multiset.card_cons, Multiset.card_add, ihl, ihr, size]

/-- A heap has size `0` if and only if it is `nil`. -/
@[simp]
theorem size_eq_zero_iff {h : LeftistHeap α} : h.size = 0 ↔ h = nil := by
  cases h <;> simp

/-- Structural leftist invariant: every node has leftist children, left rank at least right rank,
and cached rank equal to `right.rank + 1`. -/
@[simp]
def IsLeftist : LeftistHeap α → Prop
  | nil => True
  | node rk _ l r => l.IsLeftist ∧ r.IsLeftist ∧ r.rank ≤ l.rank ∧ rk = r.rank + 1

/-- Heap-order invariant: at every node, the root element is less than or equal to all elements
in both subtrees, and both subtrees are recursively heap-ordered. -/
@[simp]
def IsHeapOrdered [LE α] : LeftistHeap α → Prop
  | nil => True
  | node _ x l r =>
      (∀ y ∈ l.toMultiset, x ≤ y) ∧ (∀ y ∈ r.toMultiset, x ≤ y) ∧
      l.IsHeapOrdered ∧ r.IsHeapOrdered

/-- Full validity invariant of a leftist heap: both structurally leftist and heap-ordered. -/
def Valid [LE α] (h : LeftistHeap α) : Prop :=
  h.IsLeftist ∧ h.IsHeapOrdered

/-- The empty heap is valid. -/
@[simp]
theorem valid_nil [LE α] : (nil : LeftistHeap α).Valid :=
  ⟨trivial, trivial⟩

/-- In a heap-ordered node, the root element is less than or equal to every element in the heap. -/
theorem root_le_of_isHeapOrdered [Preorder α] {rk : ℕ} {x : α} {l r : LeftistHeap α}
    (ho : (node rk x l r).IsHeapOrdered) {y : α} (hy : y ∈ (node rk x l r).toMultiset) :
    x ≤ y := by
  simp only [toMultiset, Multiset.mem_cons, Multiset.mem_add] at hy
  rcases hy with rfl | hyl | hyr
  · exact le_rfl
  · exact ho.1 y hyl
  · exact ho.2.1 y hyr

/-- For any leftist heap, the cached `rank` equals the length of its `rightSpine`. -/
theorem rank_eq_rightSpine {h : LeftistHeap α} (hl : h.IsLeftist) : h.rank = h.rightSpine := by
  induction h with
  | nil => rfl
  | node rk _ _ r _ ihr =>
    obtain ⟨_, hlr, _, hrk⟩ := hl
    rw [rank, rightSpine, hrk, ihr hlr]

/-- Fundamental exponential size lower bound: a leftist heap of rank $r$ has at least $2^r - 1$
elements, i.e., $2^{\mathrm{rank}(h)} \le |h| + 1$. -/
theorem two_pow_rank_le_size_add_one {h : LeftistHeap α} (hl : h.IsLeftist) :
    2 ^ h.rank ≤ h.size + 1 := by
  induction h with
  | nil => simp
  | node rk _ l r ihl ihr =>
    obtain ⟨hll, hlr, hrle, hrk⟩ := hl
    have hpow : 2 ^ r.rank ≤ 2 ^ l.rank := Nat.pow_le_pow_right (by omega) hrle
    have h1 := ihl hll
    have h2 := ihr hlr
    rw [rank, hrk, Nat.pow_succ, size]
    omega

/-- Logarithmic rank bound: for any leftist heap `h`, $\mathrm{rank}(h) \le \log_2(|h| + 1)$. -/
theorem rank_le_log {h : LeftistHeap α} (hl : h.IsLeftist) :
    h.rank ≤ Nat.log 2 (h.size + 1) :=
  Nat.le_log_of_pow_le (by omega) (two_pow_rank_le_size_add_one hl)

/-- Smart node constructor maintaining the leftist property by placing the larger-rank child on
the left. Performs only a rank comparison (0 element comparisons). -/
def mkNode (x : α) (a b : LeftistHeap α) : LeftistHeap α :=
  if b.rank ≤ a.rank then
    node (b.rank + 1) x a b
  else
    node (a.rank + 1) x b a

/-- `mkNode` preserves the multiset of elements, inserting `x`. -/
@[simp]
theorem toMultiset_mkNode (x : α) (a b : LeftistHeap α) :
    (mkNode x a b).toMultiset = x ::ₘ (a.toMultiset + b.toMultiset) := by
  unfold mkNode
  split_ifs
  · rfl
  · simp only [toMultiset]
    rw [Multiset.add_comm]

/-- `mkNode` has size `a.size + b.size + 1`. -/
@[simp]
theorem size_mkNode (x : α) (a b : LeftistHeap α) :
    (mkNode x a b).size = a.size + b.size + 1 := by
  rw [← card_toMultiset, toMultiset_mkNode, Multiset.card_cons, Multiset.card_add,
    card_toMultiset, card_toMultiset]

/-- `mkNode` preserves the structural leftist invariant. -/
theorem isLeftist_mkNode {x : α} {a b : LeftistHeap α}
    (ha : a.IsLeftist) (hb : b.IsLeftist) : (mkNode x a b).IsLeftist := by
  unfold mkNode
  split_ifs with h
  · exact ⟨ha, hb, h, rfl⟩
  · exact ⟨hb, ha, Nat.le_of_not_ge h, rfl⟩

/-- `mkNode` preserves the heap-order invariant when `x` bounds both subtrees. -/
theorem isHeapOrdered_mkNode [LE α] {x : α} {a b : LeftistHeap α}
    (hxa : ∀ y ∈ a.toMultiset, x ≤ y) (hxb : ∀ y ∈ b.toMultiset, x ≤ y)
    (ha : a.IsHeapOrdered) (hb : b.IsHeapOrdered) : (mkNode x a b).IsHeapOrdered := by
  unfold mkNode
  split_ifs
  · exact ⟨hxa, hxb, ha, hb⟩
  · exact ⟨hxb, hxa, hb, ha⟩

/-- Constructs a singleton leftist heap containing `x` (0 element comparisons). -/
def singleton (x : α) : LeftistHeap α :=
  node 1 x nil nil

/-- Rank of a singleton heap is `1`. -/
@[simp]
theorem rank_singleton (x : α) : (singleton x).rank = 1 := rfl

/-- Size of a singleton heap is `1`. -/
@[simp]
theorem size_singleton (x : α) : (singleton x).size = 1 := rfl

/-- Multiset of a singleton heap is `{x}`. -/
@[simp]
theorem toMultiset_singleton (x : α) : (singleton x).toMultiset = {x} := rfl

/-- A singleton heap is structurally leftist. -/
@[simp]
theorem isLeftist_singleton (x : α) : (singleton x).IsLeftist :=
  ⟨trivial, trivial, le_rfl, rfl⟩

/-- A singleton heap is heap-ordered. -/
@[simp]
theorem isHeapOrdered_singleton [LE α] (x : α) : (singleton x).IsHeapOrdered := by
  simp [singleton]

/-- A singleton heap is valid. -/
@[simp]
theorem valid_singleton [LE α] (x : α) : (singleton x).Valid :=
  ⟨isLeftist_singleton x, isHeapOrdered_singleton x⟩

/-- Inspects the minimum element at the root of the heap, if non-empty (0 comparisons). -/
def findMin? : LeftistHeap α → Option α
  | nil => none
  | node _ x _ _ => some x

@[simp] theorem findMin?_nil : (nil : LeftistHeap α).findMin? = none := rfl

@[simp] theorem findMin?_node (rk : ℕ) (x : α) (l r : LeftistHeap α) :
    (node rk x l r).findMin? = some x := rfl

/-- `findMin?` returns `none` if and only if the heap is `nil`. -/
@[simp]
theorem findMin?_eq_none_iff {h : LeftistHeap α} : h.findMin? = none ↔ h = nil := by
  cases h <;> simp

end Structure

section Operations

variable {α : Type u} [LinearOrder α]

/-- Merges two leftist heaps in `TimeM ℕ`, charging 1 tick per element comparison `x ≤ y`. -/
def merge : LeftistHeap α → LeftistHeap α → TimeM ℕ (LeftistHeap α)
  | nil, h₂ => pure h₂
  | node rk₁ x l₁ r₁, nil => pure (node rk₁ x l₁ r₁)
  | node rk₁ x l₁ r₁, node rk₂ y l₂ r₂ =>
    if x ≤ y then do
      ✓ mkNode x l₁ <$> merge r₁ (node rk₂ y l₂ r₂)
    else do
      ✓ mkNode y l₂ <$> merge (node rk₁ x l₁ r₁) r₂
termination_by h₁ h₂ => h₁.size + h₂.size

/-- Inserts an element `x` into a leftist heap `h` by merging a singleton heap with `h`. -/
def insert (x : α) (h : LeftistHeap α) : TimeM ℕ (LeftistHeap α) :=
  merge (singleton x) h

/-- Removes and returns the minimum element together with the merged subheaps, if non-empty. -/
def deleteMin? : LeftistHeap α → TimeM ℕ (Option (α × LeftistHeap α))
  | nil => pure none
  | node _ x l r => (fun h' => some (x, h')) <$> merge l r

/-- Builds a leftist heap by successively inserting all elements of a list. -/
def fromList : List α → TimeM ℕ (LeftistHeap α)
  | [] => pure nil
  | x :: xs => do
    let h ← fromList xs
    insert x h

/-- Repeatedly extracts up to `n` minimum elements from `h` in non-decreasing order. -/
def popAll : ℕ → LeftistHeap α → TimeM ℕ (List α)
  | 0, _ => pure []
  | n + 1, h => do
    match ← deleteMin? h with
    | none => pure []
    | some (x, h') => (x :: ·) <$> popAll n h'

/-- Sorts a list in non-decreasing order using a leftist heap priority queue. -/
def heapSort (xs : List α) : TimeM ℕ (List α) := do
  let h ← fromList xs
  popAll h.size h

/-! ### Functional Correctness -/

/-- `merge` computes the disjoint union (sum) of the multisets of both heaps. -/
@[simp]
theorem toMultiset_merge (h₁ h₂ : LeftistHeap α) :
    ⟪merge h₁ h₂⟫.toMultiset = h₁.toMultiset + h₂.toMultiset := by
  fun_induction merge h₁ h₂ with
  | case1 h₂ => simp
  | case2 rk₁ x l₁ r₁ => simp
  | case3 rk₁ x l₁ r₁ rk₂ y l₂ r₂ hxy ih =>
    simp only [ret_bind, ret_map, toMultiset_mkNode, ih, toMultiset]
    rw [Multiset.cons_add, Multiset.add_assoc]
  | case4 rk₁ x l₁ r₁ rk₂ y l₂ r₂ hxy ih =>
    simp only [ret_bind, ret_map, toMultiset_mkNode, ih, toMultiset]
    rw [Multiset.add_cons, ← Multiset.add_assoc l₂.toMultiset,
      Multiset.add_comm l₂.toMultiset, Multiset.add_assoc]

/-- `merge` sums the sizes of both heaps. -/
@[simp]
theorem size_merge (h₁ h₂ : LeftistHeap α) :
    ⟪merge h₁ h₂⟫.size = h₁.size + h₂.size := by
  rw [← card_toMultiset, toMultiset_merge, Multiset.card_add, card_toMultiset, card_toMultiset]

/-- `merge` preserves the structural leftist invariant. -/
theorem isLeftist_merge {h₁ h₂ : LeftistHeap α}
    (hl₁ : h₁.IsLeftist) (hl₂ : h₂.IsLeftist) : ⟪merge h₁ h₂⟫.IsLeftist := by
  fun_induction merge h₁ h₂ with
  | case1 => exact hl₂
  | case2 => exact hl₁
  | case3 rk₁ x l₁ r₁ rk₂ y l₂ r₂ hxy ih =>
    simp only [ret_bind, ret_map]
    exact isLeftist_mkNode hl₁.1 (ih hl₁.2.1 hl₂)
  | case4 rk₁ x l₁ r₁ rk₂ y l₂ r₂ hxy ih =>
    simp only [ret_bind, ret_map]
    exact isLeftist_mkNode hl₂.1 (ih hl₁ hl₂.2.1)

/-- `merge` preserves the heap-order invariant. -/
theorem isHeapOrdered_merge {h₁ h₂ : LeftistHeap α}
    (ho₁ : h₁.IsHeapOrdered) (ho₂ : h₂.IsHeapOrdered) : ⟪merge h₁ h₂⟫.IsHeapOrdered := by
  fun_induction merge h₁ h₂ with
  | case1 => exact ho₂
  | case2 => exact ho₁
  | case3 rk₁ x l₁ r₁ rk₂ y l₂ r₂ hxy ih =>
    simp only [ret_bind, ret_map]
    refine isHeapOrdered_mkNode ho₁.1 ?_ ho₁.2.2.1 (ih ho₁.2.2.2 ho₂)
    intro z hz
    rw [toMultiset_merge, Multiset.mem_add] at hz
    rcases hz with hzr | hz₂
    · exact ho₁.2.1 z hzr
    · exact le_trans hxy (root_le_of_isHeapOrdered ho₂ hz₂)
  | case4 rk₁ x l₁ r₁ rk₂ y l₂ r₂ hxy ih =>
    have hyx : y ≤ x := le_of_not_ge hxy
    simp only [ret_bind, ret_map]
    refine isHeapOrdered_mkNode ho₂.1 ?_ ho₂.2.2.1 (ih ho₁ ho₂.2.2.2)
    intro z hz
    rw [toMultiset_merge, Multiset.mem_add] at hz
    rcases hz with hz₁ | hzr
    · exact le_trans hyx (root_le_of_isHeapOrdered ho₁ hz₁)
    · exact ho₂.2.1 z hzr

/-- `merge` preserves full heap validity. -/
theorem valid_merge {h₁ h₂ : LeftistHeap α}
    (hv₁ : h₁.Valid) (hv₂ : h₂.Valid) : ⟪merge h₁ h₂⟫.Valid :=
  ⟨isLeftist_merge hv₁.1 hv₂.1, isHeapOrdered_merge hv₁.2 hv₂.2⟩

/-- `insert` adds `x` to the heap's multiset. -/
@[simp]
theorem toMultiset_insert (x : α) (h : LeftistHeap α) :
    ⟪insert x h⟫.toMultiset = x ::ₘ h.toMultiset := by
  simp [insert]

/-- `insert` increments the size of the heap by `1`. -/
@[simp]
theorem size_insert (x : α) (h : LeftistHeap α) :
    ⟪insert x h⟫.size = h.size + 1 := by
  rw [insert, size_merge, size_singleton, Nat.add_comm]

/-- `insert` preserves the structural leftist invariant. -/
theorem isLeftist_insert {x : α} {h : LeftistHeap α} (hl : h.IsLeftist) :
    ⟪insert x h⟫.IsLeftist :=
  isLeftist_merge (isLeftist_singleton x) hl

/-- `insert` preserves full heap validity. -/
theorem valid_insert {x : α} {h : LeftistHeap α} (hv : h.Valid) :
    ⟪insert x h⟫.Valid :=
  valid_merge (valid_singleton x) hv

/-- If `findMin?` returns `some m` on a valid heap `h`, then `m` belongs to `h` and is a minimum
element of `h`. -/
theorem findMin?_isMin {h : LeftistHeap α} {m : α}
    (hv : h.Valid) (hm : h.findMin? = some m) :
    m ∈ h.toMultiset ∧ ∀ y ∈ h.toMultiset, m ≤ y := by
  cases h with
  | nil => simp at hm
  | node rk x l r =>
    simp only [findMin?_node, Option.some.injEq] at hm
    subst hm
    exact ⟨Multiset.mem_cons_self _ _, fun y hy => root_le_of_isHeapOrdered hv.2 hy⟩

/-- `deleteMin?` preserves the structural leftist invariant on the residual heap. -/
theorem isLeftist_deleteMin? {h h' : LeftistHeap α} {m : α}
    (hl : h.IsLeftist) (hd : ⟪deleteMin? h⟫ = some (m, h')) : h'.IsLeftist := by
  cases h with
  | nil => simp [deleteMin?] at hd
  | node rk x l r =>
    simp only [deleteMin?, ret_map, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨_, rfl⟩ := hd
    exact isLeftist_merge hl.1 hl.2.1

/-- `deleteMin?` preserves the heap-order invariant on the residual heap. -/
theorem isHeapOrdered_deleteMin? {h h' : LeftistHeap α} {m : α}
    (ho : h.IsHeapOrdered) (hd : ⟪deleteMin? h⟫ = some (m, h')) : h'.IsHeapOrdered := by
  cases h with
  | nil => simp [deleteMin?] at hd
  | node rk x l r =>
    simp only [deleteMin?, ret_map, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨_, rfl⟩ := hd
    exact isHeapOrdered_merge ho.2.2.1 ho.2.2.2

/-- `deleteMin?` preserves full heap validity on the residual heap. -/
theorem valid_deleteMin? {h h' : LeftistHeap α} {m : α}
    (hv : h.Valid) (hd : ⟪deleteMin? h⟫ = some (m, h')) : h'.Valid :=
  ⟨isLeftist_deleteMin? hv.1 hd, isHeapOrdered_deleteMin? hv.2 hd⟩

/-- If `deleteMin?` returns `some (m, h')`, then `h`'s multiset is `m ::ₘ h'.toMultiset`. -/
theorem toMultiset_deleteMin? {h h' : LeftistHeap α} {m : α}
    (hd : ⟪deleteMin? h⟫ = some (m, h')) :
    h.toMultiset = m ::ₘ h'.toMultiset := by
  cases h with
  | nil => simp [deleteMin?] at hd
  | node rk x l r =>
    simp only [deleteMin?, ret_map, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [toMultiset, toMultiset_merge]

/-- If `deleteMin?` returns `some (m, h')`, then `h.size = h'.size + 1`. -/
theorem size_deleteMin? {h h' : LeftistHeap α} {m : α}
    (hd : ⟪deleteMin? h⟫ = some (m, h')) :
    h.size = h'.size + 1 := by
  have hm := congrArg Multiset.card (toMultiset_deleteMin? hd)
  simpa only [card_toMultiset, Multiset.card_cons] using hm

/-- `deleteMin?` returns `none` if and only if the heap is `nil`. -/
@[simp]
theorem deleteMin?_eq_none_iff {h : LeftistHeap α} : ⟪deleteMin? h⟫ = none ↔ h = nil := by
  cases h <;> simp [deleteMin?]

/-- If `deleteMin?` returns `some (m, h')` on a valid heap `h`, then `m` belongs to `h` and is a
minimum element of `h`. -/
theorem deleteMin?_isMin {h h' : LeftistHeap α} {m : α}
    (hv : h.Valid) (hd : ⟪deleteMin? h⟫ = some (m, h')) :
    m ∈ h.toMultiset ∧ ∀ y ∈ h.toMultiset, m ≤ y := by
  cases h with
  | nil => simp [deleteMin?] at hd
  | node rk x l r =>
    simp only [deleteMin?, ret_map, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, _⟩ := hd
    exact findMin?_isMin hv rfl

/-- `fromList` constructs a heap whose multiset matches the input list. -/
@[simp]
theorem toMultiset_fromList (xs : List α) :
    ⟪fromList xs⟫.toMultiset = (xs : Multiset α) := by
  induction xs with
  | nil => simp [fromList]
  | cons x xs ih => simp [fromList, ih]

/-- `fromList` constructs a heap whose size equals `xs.length`. -/
@[simp]
theorem size_fromList (xs : List α) : ⟪fromList xs⟫.size = xs.length := by
  rw [← card_toMultiset, toMultiset_fromList, Multiset.coe_card]

/-- `fromList` produces a structurally leftist heap. -/
theorem isLeftist_fromList (xs : List α) : ⟪fromList xs⟫.IsLeftist := by
  induction xs with
  | nil => exact trivial
  | cons x xs ih =>
    simp only [fromList, ret_bind]
    exact isLeftist_insert ih

/-- `fromList` produces a valid leftist heap. -/
theorem valid_fromList (xs : List α) : ⟪fromList xs⟫.Valid := by
  induction xs with
  | nil => exact valid_nil
  | cons x xs ih =>
    simp only [fromList, ret_bind]
    exact valid_insert ih

/-- Every element returned by `popAll n h` belongs to `h.toMultiset`. -/
theorem mem_popAll {n : ℕ} {h : LeftistHeap α} {y : α} (hy : y ∈ ⟪popAll n h⟫) :
    y ∈ h.toMultiset := by
  induction n generalizing h with
  | zero => simp [popAll] at hy
  | succ n ih =>
    cases h with
    | nil => simp [popAll, deleteMin?] at hy
    | node rk x l r =>
      simp only [popAll, deleteMin?, ret_bind, ret_map, List.mem_cons] at hy
      rcases hy with rfl | hy'
      · exact Multiset.mem_cons_self _ _
      · have hmem := ih hy'
        rw [toMultiset_merge] at hmem
        exact Multiset.mem_cons_of_mem hmem

/-- `popAll h.size h` extracts the exact multiset of elements stored in `h`. -/
theorem coe_popAll_eq {n : ℕ} {h : LeftistHeap α} (hn : h.size = n) :
    ((⟪popAll n h⟫ : List α) : Multiset α) = h.toMultiset := by
  induction n generalizing h with
  | zero =>
    rw [size_eq_zero_iff.mp hn]
    simp [popAll]
  | succ n ih =>
    cases h with
    | nil => simp at hn
    | node rk x l r =>
      simp only [size, Nat.add_right_cancel_iff] at hn
      simp only [popAll, deleteMin?, ret_bind, ret_map, ← Multiset.cons_coe, toMultiset]
      rw [ih (by rw [size_merge, hn]), toMultiset_merge]

/-- Extracting `h.size` elements via `popAll` yields a list with multiset `h.toMultiset`. -/
@[simp]
theorem coe_popAll (h : LeftistHeap α) :
    ((⟪popAll h.size h⟫ : List α) : Multiset α) = h.toMultiset :=
  coe_popAll_eq rfl

/-- `popAll` produces a sorted (`List.Pairwise (· ≤ ·)`) list whenever `h` is heap-ordered. -/
theorem popAll_sorted {n : ℕ} {h : LeftistHeap α} (ho : h.IsHeapOrdered) :
    List.Pairwise (· ≤ ·) ⟪popAll n h⟫ := by
  induction n generalizing h with
  | zero => simp [popAll]
  | succ n ih =>
    cases h with
    | nil => simp [popAll, deleteMin?]
    | node rk x l r =>
      simp only [popAll, deleteMin?, ret_bind, ret_map, List.pairwise_cons]
      refine ⟨fun y hy => ?_, ih (isHeapOrdered_merge ho.2.2.1 ho.2.2.2)⟩
      have hmem : y ∈ (node rk x l r).toMultiset := by
        have hm := mem_popAll hy
        rw [toMultiset_merge] at hm
        exact Multiset.mem_cons_of_mem hm
      exact root_le_of_isHeapOrdered ho hmem

/-- `heapSort xs` returns a permutation of `xs`. -/
theorem heapSort_perm (xs : List α) : ⟪heapSort xs⟫ ~ xs := by
  apply Multiset.coe_eq_coe.mp
  simp only [heapSort, ret_bind]
  rw [coe_popAll_eq rfl, toMultiset_fromList]

/-- `heapSort xs` returns a sorted list. -/
theorem heapSort_sorted (xs : List α) : List.Pairwise (· ≤ ·) ⟪heapSort xs⟫ := by
  simp only [heapSort, ret_bind]
  exact popAll_sorted (valid_fromList xs).2

/-- `heapSort xs` preserves the length of `xs`. -/
@[simp]
theorem length_heapSort (xs : List α) : ⟪heapSort xs⟫.length = xs.length :=
  (heapSort_perm xs).length_eq

/-- Full functional correctness of `heapSort`: the output is sorted and a permutation of `xs`. -/
theorem heapSort_correct (xs : List α) :
    List.Pairwise (· ≤ ·) ⟪heapSort xs⟫ ∧ ⟪heapSort xs⟫ ~ xs :=
  ⟨heapSort_sorted xs, heapSort_perm xs⟩

/-! ### Time Complexity Bounds -/

/-- Comparisons performed by `merge h₁ h₂` are bounded by `h₁.rightSpine + h₂.rightSpine`. -/
theorem merge_time_le_rightSpine (h₁ h₂ : LeftistHeap α) :
    (merge h₁ h₂).time ≤ h₁.rightSpine + h₂.rightSpine := by
  fun_induction merge h₁ h₂ with
  | case1 => simp
  | case2 => simp
  | case3 rk₁ x l₁ r₁ rk₂ y l₂ r₂ hxy ih =>
    simp only [rightSpine] at ih
    simp only [time_bind, time_tick, time_map, rightSpine]
    omega
  | case4 rk₁ x l₁ r₁ rk₂ y l₂ r₂ hxy ih =>
    simp only [rightSpine] at ih
    simp only [time_bind, time_tick, time_map, rightSpine]
    omega

/-- For leftist heaps `h₁` and `h₂`, `merge h₁ h₂` performs at most `h₁.rank + h₂.rank`
comparisons. -/
theorem merge_time_le_rank {h₁ h₂ : LeftistHeap α}
    (hl₁ : h₁.IsLeftist) (hl₂ : h₂.IsLeftist) :
    (merge h₁ h₂).time ≤ h₁.rank + h₂.rank := by
  rw [rank_eq_rightSpine hl₁, rank_eq_rightSpine hl₂]
  exact merge_time_le_rightSpine h₁ h₂

/-- Logarithmic comparison bound for `merge`: at most
$\lfloor \log_2(|h_1| + 1) \rfloor + \lfloor \log_2(|h_2| + 1) \rfloor$ comparisons. -/
theorem merge_time_le_log {h₁ h₂ : LeftistHeap α}
    (hl₁ : h₁.IsLeftist) (hl₂ : h₂.IsLeftist) :
    (merge h₁ h₂).time ≤ Nat.log 2 (h₁.size + 1) + Nat.log 2 (h₂.size + 1) :=
  Nat.le_trans (merge_time_le_rank hl₁ hl₂)
    (Nat.add_le_add (rank_le_log hl₁) (rank_le_log hl₂))

/-- Logarithmic comparison bound for `insert`: at most $\lfloor \log_2(|h| + 1) \rfloor + 1$
comparisons. -/
theorem insert_time_le_log {x : α} {h : LeftistHeap α} (hl : h.IsLeftist) :
    (insert x h).time ≤ Nat.log 2 (h.size + 1) + 1 := by
  have h1 := merge_time_le_rank (isLeftist_singleton x) hl
  have h2 := rank_le_log hl
  simp only [insert, rank_singleton] at h1 ⊢
  omega

/-- Logarithmic comparison bound for `deleteMin?`: at most $2 \lfloor \log_2(|h| + 1) \rfloor$
comparisons. -/
theorem deleteMin?_time_le_log {h : LeftistHeap α} (hl : h.IsLeftist) :
    (deleteMin? h).time ≤ 2 * Nat.log 2 (h.size + 1) := by
  cases h with
  | nil => simp [deleteMin?]
  | node rk x l r =>
    obtain ⟨hll, hlr, _, _⟩ := hl
    simp only [deleteMin?, time_map, size]
    have hm := merge_time_le_log hll hlr
    have hlog_l : Nat.log 2 (l.size + 1) ≤ Nat.log 2 (l.size + r.size + 1 + 1) :=
      Nat.log_mono_right (by omega)
    have hlog_r : Nat.log 2 (r.size + 1) ≤ Nat.log 2 (l.size + r.size + 1 + 1) :=
      Nat.log_mono_right (by omega)
    omega

/-- Building a leftist heap via `fromList xs` performs at most
`|xs| * log₂(|xs| + 1) + |xs|` comparisons. -/
theorem fromList_time_le_log (xs : List α) :
    (fromList xs).time ≤ xs.length * Nat.log 2 (xs.length + 1) + xs.length := by
  induction xs with
  | nil => simp [fromList]
  | cons x xs ih =>
    simp only [fromList, time_bind, List.length_cons]
    have hins := insert_time_le_log (x := x) (isLeftist_fromList xs)
    rw [size_fromList] at hins
    have hmono : Nat.log 2 (xs.length + 1) ≤ Nat.log 2 (xs.length + 1 + 1) :=
      Nat.log_mono_right (by omega)
    have hmul :
        xs.length * Nat.log 2 (xs.length + 1) ≤ xs.length * Nat.log 2 (xs.length + 1 + 1) :=
      Nat.mul_le_mul_left xs.length hmono
    have hrw :
        (xs.length + 1) * Nat.log 2 (xs.length + 1 + 1) =
          xs.length * Nat.log 2 (xs.length + 1 + 1) + Nat.log 2 (xs.length + 1 + 1) :=
      Nat.succ_mul xs.length _
    omega

/-- Extracting `n` minimums via `popAll n h` performs at most `2 * n * log₂(|h| + 1)`
comparisons. -/
theorem popAll_time_le_log {n : ℕ} {h : LeftistHeap α} (hl : h.IsLeftist) :
    (popAll n h).time ≤ 2 * n * Nat.log 2 (h.size + 1) := by
  induction n generalizing h with
  | zero => simp [popAll]
  | succ n ih =>
    simp only [popAll, time_bind]
    have hdel := deleteMin?_time_le_log hl
    cases h with
    | nil => simp [deleteMin?]
    | node rk x l r =>
      obtain ⟨hll, hlr, _, _⟩ := hl
      simp only [deleteMin?, ret_map, time_map] at hdel ⊢
      have h'l : ⟪merge l r⟫.IsLeftist := isLeftist_merge hll hlr
      have hpop := ih h'l
      have hsize : ⟪merge l r⟫.size + 1 ≤ (node rk x l r).size + 1 := by
        simp only [size_merge, size]
        omega
      have hmono :
          Nat.log 2 (⟪merge l r⟫.size + 1) ≤ Nat.log 2 ((node rk x l r).size + 1) :=
        Nat.log_mono_right hsize
      have hmul :
          2 * n * Nat.log 2 (⟪merge l r⟫.size + 1) ≤
            2 * n * Nat.log 2 ((node rk x l r).size + 1) :=
        Nat.mul_le_mul_left (2 * n) hmono
      have hrw :
          2 * (n + 1) * Nat.log 2 ((node rk x l r).size + 1) =
            2 * n * Nat.log 2 ((node rk x l r).size + 1) +
              2 * Nat.log 2 ((node rk x l r).size + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.right_distrib]
      omega

/-- Explicit $O(n \log n)$ comparison bound for `heapSort`: sorting a list `xs` of length $n$
performs at most $3 n \lfloor \log_2(n + 1) \rfloor + n$ element comparisons. -/
theorem heapSort_time_le (xs : List α) :
    (heapSort xs).time ≤ 3 * xs.length * Nat.log 2 (xs.length + 1) + xs.length := by
  simp only [heapSort, time_bind, size_fromList]
  have hfrom := fromList_time_le_log xs
  have hpop := popAll_time_le_log (n := xs.length) (isLeftist_fromList xs)
  rw [size_fromList] at hpop
  have hrw :
      3 * xs.length * Nat.log 2 (xs.length + 1) =
        xs.length * Nat.log 2 (xs.length + 1) + 2 * xs.length * Nat.log 2 (xs.length + 1) := by
    have h3 : 3 * xs.length = xs.length + 2 * xs.length := by omega
    rw [h3, Nat.right_distrib]
  omega

end Operations

end LeftistHeap

end Cslib.Algorithms.Lean
