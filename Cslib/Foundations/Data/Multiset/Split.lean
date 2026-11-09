/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.Multiset.Grind

/-! # Splitting multisets with list witnesses

Multisets are a quotient of lists, so a definition that produces data cannot inspect how a
multiset is built. In particular, it cannot compute a list that enumerates a multiset `s`
(`Multiset.toList` is noncomputable), so it cannot recurse over the elements of `s`. For
example, the summands of `s + t = ↑l` can only be presented as lists by scanning `l`.

The definitions in this file compute such list presentations. Each one takes an
equation between multisets in which one side is built from a list `l` that is already
available, and computes *list* witnesses for the unknown parts, together with the multiset
equations that relate them. Every witness is either `List.erase` of a list in hand or the
result of scanning a list in hand with `Multiset.scanToList`, so no choice is involved.

These functions are used by cut elimination for classical linear logic
(`Cslib.Logics.LinearLogic.CLL.CutFree`), which keeps the contexts of sequents as lists so that
cut elimination can be computed.

## Main definitions

* `Multiset.scanToListAdd`: list witnesses for both summands of `s + t = ↑l`.
* `Multiset.splitCons`: computable version of `Multiset.cons_eq_cons` for `a ::ₘ ↑l = b ::ₘ s`.
* `Multiset.splitConsAdd`: locates the head of `a ::ₘ ↑l = s + t` in one of the summands.
* `Multiset.splitReplicateCons`: decides whether the head of `b ::ₘ s = replicate n c + ↑l` is
  one of the copies of `c` or comes from `l`.
* `Multiset.splitReplicateAdd`: distributes `s + t = replicate n c + ↑l` over the summands.
-/

@[expose] public section

namespace Multiset

variable {α : Type*}

/-- If `0 = s + t`, then `t = 0`. -/
theorem eq_zero_of_zero_eq_add {s t : Multiset α} (h : 0 = s + t) : t = 0 :=
  le_zero.mp (h ▸ le_add_left t s)

variable [DecidableEq α]

/-- If `b ::ₘ s = ↑l`, then `s` is represented by the list `l.erase b`. -/
theorem eq_coe_erase_of_cons_eq {b : α} {s : Multiset α} {l : List α}
    (h : b ::ₘ s = l) : s = (l.erase b : List α) := by
  rw [← coe_erase, ← h, erase_cons_head]

/-- Given `s + t = ↑l`, computes lists representing `s` and `t` by scanning `l`
(see `Multiset.scanToList`). -/
def scanToListAdd (l : List α) {s t : Multiset α} (h : s + t = l) :
    {l₁ : List α // (l₁ : Multiset α) = s} × {l₂ : List α // (l₂ : Multiset α) = t} :=
  (scanToList l s (h ▸ le_add_right s t), scanToList l t (h ▸ le_add_left t s))

/-- Computable version of `Multiset.cons_eq_cons` when the left tail is a list `l`. Given
`a ::ₘ ↑l = b ::ₘ s`, either `a = b` and `↑l = s`, or the two tails share the residual
`l' = l.erase b`, that is, `↑l = b ::ₘ ↑l'` and `s = a ::ₘ ↑l'`. -/
def splitCons {a b : α} {l : List α} {s : Multiset α} (h : a ::ₘ (l : Multiset α) = b ::ₘ s) :
    (a = b ∧ (l : Multiset α) = s) ⊕'
      {l' : List α // (l : Multiset α) = b ::ₘ l' ∧ s = a ::ₘ l'} :=
  if hab : a = b then
    .inl ⟨hab, (cons_inj_right a).mp (hab ▸ h)⟩
  else
    have hbl : b ∈ (l : Multiset α) :=
      (mem_cons.mp (h ▸ mem_cons_self b s)).resolve_left (Ne.symm hab)
    have hl : (l : Multiset α) = b ::ₘ (l.erase b : Multiset α) := by
      rw [← coe_erase, cons_erase hbl]
    .inr ⟨l.erase b, hl, by
      rw [hl, cons_swap] at h
      exact ((cons_inj_right b).mp h).symm⟩

/-- Given `a ::ₘ ↑l = s + t`, locates `a` in one of the summands (`s` if possible) and computes
a list representing that summand without `a`, by scanning `l`. -/
def splitConsAdd {a : α} {l : List α} {s t : Multiset α} (h : a ::ₘ (l : Multiset α) = s + t) :
    {l' : List α // s = a ::ₘ l'} ⊕' {l' : List α // t = a ::ₘ l'} :=
  if ha : a ∈ s then
    let r := scanToList l (s.erase a) (erase_le_iff_le_cons.mpr (h ▸ le_add_right s t))
    .inl ⟨r.1, by rw [r.2, cons_erase ha]⟩
  else
    have hat : a ∈ t := (mem_add.mp (h ▸ mem_cons_self a l)).resolve_left ha
    let r := scanToList l (t.erase a) (erase_le_iff_le_cons.mpr (h ▸ le_add_left t s))
    .inr ⟨r.1, by rw [r.2, cons_erase hat]⟩

/-- The two ways in which the head `b` of `b ::ₘ s = replicate n c + ↑l` can arise
(see `Multiset.splitReplicateCons`). -/
inductive ReplicateConsSplit (c b : α) (n : ℕ) (l : List α) (s : Multiset α) : Type _ where
  /-- `b` is one of the `n` copies of `c`, and `s` contains the remaining `m = n - 1` copies. -/
  | replicate (m : ℕ) (hn : n = m + 1) (hb : b = c) (hs : s = replicate m c + l)
  /-- `b` comes from `l`, and `l'` is `l` without that occurrence of `b`. -/
  | list (l' : List α) (hl : (l : Multiset α) = b ::ₘ l') (hs : s = replicate n c + l')

/-- Given `b ::ₘ s = replicate n c + ↑l`, decides whether `b` is one of the copies of `c`
(preferred whenever `b = c` and `n ≠ 0`) or comes from `l`. In the latter case, the residual
list is `l.erase b`. -/
def splitReplicateCons {c b : α} {n : ℕ} {l : List α} {s : Multiset α}
    (h : b ::ₘ s = replicate n c + l) : ReplicateConsSplit c b n l s :=
  if hb : b = c ∧ n ≠ 0 then
    have hn : n = (n - 1) + 1 := by omega
    .replicate (n - 1) hn hb.1 (by
      rw [hn, replicate_succ, cons_add, hb.1] at h
      exact (cons_inj_right c).mp h)
  else
    have hbl : b ∈ (l : Multiset α) :=
      (mem_add.mp (h ▸ mem_cons_self b s)).resolve_left fun hr => hb (mem_replicate.mp hr).symm
    have hl : (l : Multiset α) = b ::ₘ (l.erase b : Multiset α) := by
      rw [← coe_erase, cons_erase hbl]
    .list (l.erase b) hl (by
      rw [hl, add_cons] at h
      exact (cons_inj_right b).mp h)

/-- A distribution of `s + t = replicate n c + ↑l` over the two summands: `s` receives `k₁`
copies of `c` and the list `l₁`, and `t` receives `k₂` copies of `c` and the list `l₂`
(see `Multiset.splitReplicateAdd`). -/
structure ReplicateAddSplit (c : α) (n : ℕ) (l : List α) (s t : Multiset α) where
  /-- The number of copies of `c` that go to `s`. -/
  k₁ : ℕ
  /-- The number of copies of `c` that go to `t`. -/
  k₂ : ℕ
  /-- The part of `l` that goes to `s`. -/
  l₁ : List α
  /-- The part of `l` that goes to `t`. -/
  l₂ : List α
  /-- Every copy of `c` goes to one of the summands. -/
  hn : n = k₁ + k₂
  /-- The decomposition of `s`. -/
  hs : s = replicate k₁ c + l₁
  /-- The decomposition of `t`. -/
  ht : t = replicate k₂ c + l₂
  /-- `l` is split between `l₁` and `l₂`. -/
  hl : (l : Multiset α) = l₁ + l₂

/-- Distributes `s + t = replicate n c + ↑l` over the summands. The copies of `c` are assigned
one at a time (to `s` while it contains `c`, then to `t`), and the lists `l₁` and `l₂` are
computed by scanning `l` (see `Multiset.scanToListAdd`). -/
def splitReplicateAdd {c : α} {l : List α} :
    {n : ℕ} → {s t : Multiset α} → s + t = replicate n c + l → ReplicateAddSplit c n l s t
  | 0, s, t, h =>
    have h : s + t = l := by rw [h, replicate_zero, Multiset.zero_add]
    let (⟨l₁, h₁⟩, ⟨l₂, h₂⟩) := scanToListAdd l h
    ⟨0, 0, l₁, l₂, rfl, by rw [h₁, replicate_zero, Multiset.zero_add],
      by rw [h₂, replicate_zero, Multiset.zero_add], by rw [h₁, h₂, h]⟩
  | n + 1, s, t, h =>
    if hcs : c ∈ s then
      -- One copy of `c` goes to `s`.
      let ⟨k₁, k₂, l₁, l₂, hn, hs, ht, hl⟩ :=
        splitReplicateAdd (n := n) (s := s.erase c) (t := t) (by
          have := cons_erase hcs
          grind only [multiset])
      ⟨k₁ + 1, k₂, l₁, l₂, by omega,
        by rw [← cons_erase hcs, hs, replicate_succ, cons_add], ht, hl⟩
    else
      -- One copy of `c` goes to `t`.
      have hc : c ∈ s + t := by rw [h, replicate_succ, cons_add]; exact mem_cons_self c _
      have hct : c ∈ t := (mem_add.mp hc).resolve_left hcs
      let ⟨k₁, k₂, l₁, l₂, hn, hs, ht, hl⟩ :=
        splitReplicateAdd (n := n) (s := s) (t := t.erase c) (by
          have := cons_erase hct
          grind only [multiset])
      ⟨k₁, k₂ + 1, l₁, l₂, by omega, hs,
        by rw [← cons_erase hct, ht, replicate_succ, cons_add], hl⟩

end Multiset
