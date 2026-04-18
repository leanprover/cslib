-- Authors: Sorrachai Yingchareonthawornchai and Weixuan Yuan
-- This definition of walk are well-defined for both directed and undirected simple graphs.

import Mathlib.Data.Sym.Sym2
set_option tactic.hygienic false
variable {α : Type*}


/- VertexSeq as a non-empty seq -/
@[grind] inductive VertexSeq (α : Type*)
  | singleton (v : α) : VertexSeq α
  | cons (w : VertexSeq α) (v : α) : VertexSeq α

namespace VertexSeq

/-! ## Basic accessors -/

/- The list of vertices visited by the walk, in order. -/
@[grind] def toList : VertexSeq α → List α
  | .singleton v => [v]
  | .cons p v => p.toList.cons v

/-- The first node does not count in the sequence. -/
@[grind] def length : VertexSeq α → ℕ
  | .singleton _ => 0
  | .cons w _ => 1 + w.length

@[grind] def head : VertexSeq α → α
  | .singleton v => v
  | .cons w _ => head w

@[grind] def tail : VertexSeq α → α
  | .singleton v => v
  | .cons _ v => v

@[simp, grind =] lemma singleton_head_eq (u : α) :
  (VertexSeq.singleton u).head = u := by simp [head]
@[simp, grind =] lemma singleton_tail_eq (u : α) :
  (VertexSeq.singleton u).tail = u := by simp [tail]

@[simp, grind =] lemma con_head_eq (w : VertexSeq α) (u : α) :
    (w.cons u).head = w.head := rfl

@[simp, grind =] lemma con_tail_eq (w : VertexSeq α) (u : α) :
    (w.cons u).tail = u := rfl

@[simp, grind ←] lemma head_mem_toList (w : VertexSeq α) : w.head ∈ w.toList := by
  induction w <;> grind [VertexSeq.head, VertexSeq.toList]

/-! ## dropHead, dropTail -/

@[grind] def dropHead : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons (.singleton _) v => .singleton v
  | .cons w v => .cons (dropHead w) v

@[grind] def dropTail : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w _ => w

/-! ## append, reverse, and their laws -/

@[grind] def append : VertexSeq α → VertexSeq α → VertexSeq α
  | w, .singleton v => .cons w v
  | w, .cons w2 v => .cons (append w w2) v

@[grind] def reverse : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v => append (.singleton v) (reverse w)

@[simp, grind =] lemma length_append (p q : VertexSeq α) :
  (p.append q).length = p.length + q.length + 1 := by
  fun_induction append p q <;> grind

@[simp, grind =] lemma singleton_reverse_eq (v : α) :
  (VertexSeq.singleton v).reverse = .singleton v := rfl

@[simp, grind =] lemma tail_on_tail (p q : VertexSeq α) : (p.append q).tail = q.tail := by
  fun_induction append <;> simp_all [tail]

@[simp, grind =] lemma head_on_head (p q : VertexSeq α) : (p.append q).head = p.head := by
  fun_induction append <;> simp_all

@[simp, grind =] lemma tail_on_tail_singleton (p : VertexSeq α) (x : α) :
    (p.append (.singleton x)).tail = x := by
  unfold append
  unfold tail
  split <;> aesop

@[simp, grind =] lemma head_on_head_singleton (p : VertexSeq α) (x : α) :
  ((VertexSeq.singleton x).append p).head = x := by
  unfold append
  unfold head
  split <;> aesop

@[simp, grind =] lemma append_assoc (p q r : VertexSeq α) :
    (p.append q).append r = p.append (q.append r) := by
  fun_induction append q r <;> simp_all [append]

@[simp, grind =] lemma reverse_append (p q : VertexSeq α) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  fun_induction append <;> simp_all [reverse]


@[simp, grind =] lemma reverse_reverse (p : VertexSeq α) : (p.reverse).reverse = p := by
  fun_induction reverse p <;> aesop


@[simp, grind =] lemma head_reverse (p : VertexSeq α) : (p.reverse).head = p.tail := by
  fun_induction reverse p <;> aesop


@[simp, grind =] lemma tail_reverse (p : VertexSeq α) : (p.reverse).tail = p.head := by
  fun_induction reverse p <;> aesop

@[simp, grind =] lemma dropTail_head (p : VertexSeq α) : p.dropTail.head = p.head := by
  fun_induction reverse p <;> aesop

/-! ## takeUntil, dropUntil, loopErase -/

/-- Take vertices until the first occurrence of `v` (including `v`). -/
@[simp, grind] def takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
  (h : v ∈ w.toList) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then takeUntil w2 v h2
    else .cons w2 x

/-- Drop vertices until the last occurrence of `v` (not including `v`). -/
@[simp, grind] def dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
  (h : v ∈ w.toList) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then .cons (dropUntil w2 v h2) x
    else .singleton x

@[simp] lemma takeUntil_length_le [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.takeUntil v h).length ≤ w.length := by
  fun_induction takeUntil w v h <;> grind

@[simp] lemma dropUntil_length_le [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.dropUntil v h).length ≤ w.length := by
  fun_induction dropUntil w v h <;> grind

@[simp, grind =] lemma head_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w.toList) :
    (takeUntil w v h).head = w.head := by
  induction w <;> grind

@[simp, grind =] lemma tail_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w.toList) :
    (takeUntil w v h).tail = v := by
  induction w <;> grind

@[simp, grind →] lemma mem_takeUntil [DecidableEq α] (w : VertexSeq α)
  (v x : α) (h : v ∈ w.toList) : x ∈ (takeUntil w v h).toList → x ∈ w.toList := by
  induction w generalizing v <;> grind

@[simp, grind =] lemma head_dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) :
    (w.dropUntil v h).head = v := by
  induction w <;> grind

@[simp, grind =] lemma tail_dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) :
    (w.dropUntil v h).tail = w.tail := by
  fun_induction VertexSeq.dropUntil w v h <;> simp [VertexSeq.tail]



@[simp, grind →] lemma mem_dropUntil [DecidableEq α] (w : VertexSeq α) (v x : α)
    (h : v ∈ w.toList) : x ∈ (w.dropUntil v h).toList → x ∈ w.toList := by
  induction w generalizing v <;> grind

@[grind] def loopErase [DecidableEq α] : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v =>
      if h : v ∈ w.toList then
        loopErase (takeUntil w v h)
      else
        .cons (loopErase w) v
  termination_by p => p.length
  decreasing_by
  · simp [length]; grind [takeUntil_length_le]
  · simp [length]

lemma mem_loopErase [DecidableEq α] (w : VertexSeq α) :
    ∀ {x : α}, x ∈ w.loopErase.toList → x ∈ w.toList := by
  fun_induction loopErase w <;> grind [toList, mem_takeUntil]

theorem loopErase_nodup [DecidableEq α] (w : VertexSeq α) : w.loopErase.toList.Nodup := by
  fun_induction VertexSeq.loopErase w <;> grind [toList, mem_loopErase]

@[simp] lemma head_loopErase [DecidableEq α] (w : VertexSeq α) : w.loopErase.head = w.head := by
  fun_induction loopErase w <;> simp_all

@[simp] lemma tail_loopErase [DecidableEq α] (w : VertexSeq α) : w.loopErase.tail = w.tail := by
  fun_induction loopErase w <;> simp_all

end VertexSeq

/-! ## IsWalk, Walk core data -/

@[grind] inductive IsWalk : VertexSeq α → Prop
  | singleton (v : α) : IsWalk (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsWalk w)
      (hneq : w.tail ≠ u)
    : IsWalk (.cons w u)

grind_pattern IsWalk.singleton => IsWalk (.singleton v)
grind_pattern IsWalk.cons => IsWalk (.cons w u)

structure Walk (α : Type*) where
  seq : VertexSeq α
  valid : IsWalk seq

namespace Walk
open VertexSeq

@[ext] lemma ext {w1 w2 : Walk α} (hseq : w1.seq = w2.seq) : w1 = w2 := by
  cases w1
  cases w2
  cases hseq
  rfl

/-! ## Basic IsWalk helper lemmas -/

@[simp, grind =>] lemma iswalk_prefix (w2 : VertexSeq α) (v : α)
    (valid : IsWalk (w2.cons v)) : IsWalk w2 := by
  cases valid
  grind

@[simp, grind <=] lemma tail_neq_of_iswalk (w2 : VertexSeq α) (v : α)
    (valid : IsWalk (w2.cons v)) : w2.tail ≠ v := by
  cases valid
  grind

@[grind ←]
lemma is_walk_two_seqs_append_of (w1 w2 : VertexSeq α)
  (h1 : IsWalk w1) (h2 : IsWalk w2) (hneq : w1.tail ≠ w2.head) :
    IsWalk (w1.append w2) := by
  fun_induction w1.append w2 <;> grind

@[grind ←]
theorem prepend_iswalk (p : VertexSeq α) (v : α) (h : IsWalk p) (h2 : p.head ≠ v) :
  IsWalk ((VertexSeq.singleton v).append p) := by grind

@[grind →, grind ←]
lemma isWalk_rev_if (w : VertexSeq α) : IsWalk w → IsWalk w.reverse := by
  intro h
  induction h <;> grind

@[grind →]
theorem is_walk_neq_of_append (p q : VertexSeq α) (h : IsWalk (p.append q))
  : IsWalk p ∧ IsWalk q ∧ p.tail ≠ q.head := by fun_induction append <;> grind

@[grind →]
lemma isWalk_rev_imp (w : VertexSeq α) : IsWalk w.reverse → IsWalk w := by
  fun_induction reverse <;> grind

@[simp, grind =]
lemma isWalk_rev_iff (w : VertexSeq α) : IsWalk w.reverse ↔ IsWalk w := by grind

lemma nodup_iswalk (w : VertexSeq α) (h : w.toList.Nodup) : IsWalk w := by
  induction w <;> grind

-- @[grind ←]
-- lemma prepend_iswalk' (w2 : VertexSeq α) (v : α)
--     (valid : IsWalk w2) (hneq : v ≠ w2.head) :
--   IsWalk ((VertexSeq.singleton v).append w2) := by
--   induction valid generalizing v with
--   | singleton x => grind [head, tail, append, IsWalk.singleton, IsWalk.cons]
--   | cons w u hw htail ih => grind [head, append, IsWalk.cons, tail_on_tail]


@[grind →]
lemma takeUntil_iswalk [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
  (hw : IsWalk w) :
    IsWalk (w.takeUntil v h) := by
  induction hw generalizing v <;> grind

@[grind →]
lemma dropUntil_iswalk [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) (hw : IsWalk w) :
    IsWalk (w.dropUntil v h) := by
  induction hw generalizing v <;> grind

lemma loopErase_iswalk [DecidableEq α] (w : VertexSeq α) : IsWalk w.loopErase := by
  grind [nodup_iswalk, loopErase_nodup]

/-! ## support, head, tail, length, dropTail for Walk -/

/-- The list of vertices visited by the walk, in order. -/
@[simp, grind] def support (w : Walk α) : List α := w.seq.toList

abbrev head (w : Walk α) : α := w.seq.head
abbrev tail (w : Walk α) : α := w.seq.tail
abbrev length (w : Walk α) : ℕ := w.seq.length

abbrev dropTail (w : Walk α) : Walk α :=
  { seq := w.seq.dropTail
    valid := by grind [Walk]}

def append_single (w : Walk α) (u : α) (h : u ≠ w.tail) : Walk α :=
  ⟨w.seq.cons u, .cons w.seq u w.valid (by aesop)⟩

@[simp, grind =]
lemma dropTail_head (w : Walk α) : w.dropTail.head = w.head := by
  cases w; induction valid <;> grind

@[simp, grind .]
lemma len_zero_of_drop_tail_eq_tail (w : Walk α) (h : w.dropTail.tail = w.tail) :
    w.length = 0 := by
  cases w; induction valid <;> grind

@[simp, grind ←]
lemma head_eq_tail_of_length_zero (w : Walk α) (h : w.length = 0)
  : w.head = w.tail := by
  cases w; induction valid <;> grind


/-! ## Walk append, reverse and related lemmas -/

@[grind ←]
lemma two_seqs_append_of (w1 w2 : Walk α) (hneq : w1.tail ≠ w2.head) :
    IsWalk (w1.seq.append w2.seq) := by
  cases w1; cases w2; grind

@[grind =]
def append (w1 w2 : Walk α) (h : w1.tail = w2.head) : Walk α :=
  if h1 : w1.length = 0 then w2
  else
    { seq := w1.dropTail.seq.append w2.seq
      valid := by grind [Walk]}

@[grind =]
def reverse (w : Walk α) : Walk α :=
  { seq := w.seq.reverse
    valid := by grind [Walk]}

@[simp, grind =] lemma head_reverse (w : Walk α) : (w.reverse).head = w.tail := by grind
@[simp, grind =] lemma tail_reverse (w : Walk α) : (w.reverse).tail = w.head := by grind
@[simp, grind =] lemma head_on_head (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).head = w1.head := by
  cases w1; induction valid <;> grind
@[simp, grind =] lemma tail_on_tail (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).tail = w2.tail := by grind

@[simp, grind =] lemma length_append (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).length = w1.length + w2.length := by
  unfold Walk.append
  by_cases h1 : w1.length = 0
  · grind
  · have hdrop : w1.dropTail.length + 1 = w1.length := by
      cases w1; induction valid <;> grind
    grind

/-! ## Path, cycle -/

@[grind] def IsPath (w : Walk α) : Prop := w.support.Nodup

abbrev toPath [DecidableEq α] (w : Walk α) : Walk α :=
  { seq := w.seq.loopErase
    valid := loopErase_iswalk w.seq }

theorem toPath_isPath [DecidableEq α] (w : Walk α) : IsPath (toPath w) := by
  unfold IsPath toPath support
  simpa using loopErase_nodup w.seq

lemma tail_toPath [DecidableEq α] (w : Walk α) : (toPath w).tail = w.tail := by
  grind [tail_loopErase]

lemma head_toPath [DecidableEq α] (w : Walk α) : (toPath w).head = w.head := by
  grind [head_loopErase]

def IsCycle (w : Walk α) : Prop :=
  3 ≤ w.length ∧ w.head = w.tail ∧ IsPath w.dropTail



/-! ## Some more helper lemmas -/
@[simp, grind .] lemma takeUntil_head_eq_singleton [DecidableEq α] (w : VertexSeq α)
  (h : w.head ∈ w.toList) :
  w.takeUntil w.head h = VertexSeq.singleton w.head := by
  induction w <;> grind

@[simp, grind .] lemma dropUntil_head_eq_self [DecidableEq α] (w : VertexSeq α)
  (h : w.head ∈ w.toList) :
  w.dropUntil w.head h = w := by
  induction w <;> grind

@[simp, grind →] lemma vertex_seq_split [DecidableEq α]
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList) (hne : v ≠ w.head) :
  (w.takeUntil v h).dropTail.append (w.dropUntil v h) = w := by
  induction w generalizing v <;> grind

@[simp, grind →] lemma walk_split [DecidableEq α]
  (w : Walk α) (u : α) (hu : u ∈ w.support) :
    w = Walk.append
      ⟨w.seq.takeUntil u hu, takeUntil_iswalk w.seq u hu w.valid⟩
      ⟨w.seq.dropUntil u hu, dropUntil_iswalk w.seq u hu w.valid⟩
      (by grind) := by
  by_cases h : u = w.head
  · ext; grind
  · ext; grind


/-! ## Re-rooting a cycle -/
/-- Re-root a cycle at any chosen vertex in its support. -/
@[simp, grind] def rerootCycle [DecidableEq α] (w : Walk α) (hcyc : IsCycle w)
    (u : α) (hu : u ∈ w.support) : Walk α :=
  Walk.append
    ⟨w.seq.dropUntil u hu, dropUntil_iswalk w.seq u hu w.valid⟩
    ⟨w.seq.takeUntil u hu, takeUntil_iswalk w.seq u hu w.valid⟩
    (by rcases hcyc with ⟨_, hht, _⟩; grind)

@[simp, grind =] lemma toList_append (p q : VertexSeq α) :
    (p.append q).toList = q.toList ++ p.toList := by
  induction q generalizing p <;> grind

lemma append_dropTail_eq_dropTail_append (w1 w2 : Walk α) (h : w1.tail = w2.head)
  (hlen : w2.head ≠ w2.tail) :
  (Walk.append w1 w2 h).dropTail = Walk.append w1 w2.dropTail (by grind) := by
  by_cases h1 : w1.length = 0
  · grind
  · ext; cases w2; induction valid <;> grind

lemma isCycle_rerootCycle [DecidableEq α] (w : Walk α) (hcyc : IsCycle w)
  (u : α) (hu : u ∈ w.support) :
  IsCycle (rerootCycle w hcyc u hu):= by
  have h2 : w.length = (w.rerootCycle hcyc u hu).length := by grind
  rcases hcyc with ⟨hlen, hht, hpath⟩
  refine ⟨?_, ?_, ?_⟩
  · grind
  · grind
  · by_cases h : u = w.head
    · have hz : w.length ≠ 0 := by omega
      grind
    · grind [append_dropTail_eq_dropTail_append]

end Walk
