/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/

module
public import Cslib.Init
public import Cslib.Algorithms.Lean.Graph.Graph
public import Mathlib.Data.Sym.Sym2

@[expose] public section

set_option tactic.hygienic false
variable {α : Type*}

/-!
# Vertex sequences and walks

This file defines vertex sequences (`VertexSeq`) and walks (`Walk`) for simple graphs.
The definitions are well-defined for both directed and undirected simple graphs.

A `VertexSeq` is a nonempty sequence of vertices, and a `Walk` is a vertex sequence
satisfying the `IsWalk` predicate, which requires that consecutive vertices are distinct.

## Main definitions

* `VertexSeq`: a nonempty sequence of vertices, defined inductively as either a singleton
  or a cons extension.
* `VertexSeq.takeUntil`: truncate a vertex sequence at the first occurrence of a given vertex.
* `VertexSeq.dropUntil`: drop the prefix up to the last occurrence of a given vertex.
* `VertexSeq.loopErase`: erase loops from a vertex sequence, producing a sequence with no
  repeated vertices.
* `IsWalk`: a predicate asserting that consecutive vertices in a `VertexSeq` are distinct.
* `Walk`: a bundled vertex sequence together with a proof of `IsWalk`.
* `Walk.IsPath`: a walk whose support has no duplicate vertices.
* `Walk.IsCycle`: a walk of length at least 3 whose head equals its tail and whose interior
  is a path.
* `Walk.toPath`: loop-erase a walk to obtain a path.
* `Walk.rerootCycle`: re-root a cycle at any vertex in its support.

## Main statements

* `VertexSeq.loopErase_nodup`: loop erasure produces a duplicate-free vertex list.
* `Walk.loopErase_iswalk`: loop erasure of any vertex sequence yields a valid walk.
* `Walk.toPath_isPath`: `Walk.toPath` produces a path.
* `Walk.isCycle_rerootCycle`: re-rooting a cycle at any vertex in its support yields a cycle.
-/

namespace Cslib.Algorithms.Lean

/-- A nonempty sequence of vertices, used as the underlying data for walks.
`singleton v` is the trivial sequence containing only `v`, and `cons w v` extends the
sequence `w` by appending vertex `v` at the end. -/
@[scoped grind] inductive VertexSeq (α : Type*)
  | singleton (v : α) : VertexSeq α
  | cons (w : VertexSeq α) (v : α) : VertexSeq α

namespace VertexSeq

/-! ## Basic accessors -/

/-- The list of vertices in the sequence, in order. -/
@[scoped grind] def toList : VertexSeq α → List α
  | .singleton v => [v]
  | .cons p v => p.toList.cons v

/-- The number of edges in the sequence, i.e., one less than the number of vertices.
A singleton has length 0. -/
@[scoped grind] def length : VertexSeq α → ℕ
  | .singleton _ => 0
  | .cons w _ => 1 + w.length

/-- The first vertex of the sequence. -/
@[scoped grind] def head : VertexSeq α → α
  | .singleton v => v
  | .cons w _ => head w

/-- The last vertex of the sequence. -/
@[scoped grind] def tail : VertexSeq α → α
  | .singleton v => v
  | .cons _ v => v

/-- The head of a singleton sequence is the vertex itself. -/
@[simp, scoped grind =] lemma singleton_head_eq (u : α) :
  (VertexSeq.singleton u).head = u := by simp [head]

/-- The tail of a singleton sequence is the vertex itself. -/
@[simp, scoped grind =] lemma singleton_tail_eq (u : α) :
  (VertexSeq.singleton u).tail = u := by simp [tail]

/-- The head of `w.cons u` is the head of `w`. -/
@[simp, scoped grind =] lemma con_head_eq (w : VertexSeq α) (u : α) :
    (w.cons u).head = w.head := rfl

/-- The tail of `w.cons u` is `u`. -/
@[simp, scoped grind =] lemma con_tail_eq (w : VertexSeq α) (u : α) :
    (w.cons u).tail = u := rfl

/-- The head of a vertex sequence belongs to its vertex list. -/
@[simp, scoped grind ←] lemma head_mem_toList (w : VertexSeq α) : w.head ∈ w.toList := by
  induction w <;> grind [VertexSeq.head, VertexSeq.toList]

/-! ## dropHead, dropTail -/

/-- Remove the first vertex from the sequence. A singleton is left unchanged. -/
@[scoped grind] def dropHead : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons (.singleton _) v => .singleton v
  | .cons w v => .cons (dropHead w) v

/-- Remove the last vertex from the sequence. A singleton is left unchanged. -/
@[scoped grind] def dropTail : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w _ => w

/-! ## append, reverse, and their laws -/

/-- Concatenate two vertex sequences by appending all vertices of the second sequence
after the first. -/
@[scoped grind] def append : VertexSeq α → VertexSeq α → VertexSeq α
  | w, .singleton v => .cons w v
  | w, .cons w2 v => .cons (append w w2) v

/-- Reverse the order of vertices in the sequence. -/
@[scoped grind] def reverse : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v => append (.singleton v) (reverse w)

/-- The length of the concatenation equals the sum of the lengths plus one. -/
@[simp, scoped grind =] lemma length_append (p q : VertexSeq α) :
  (p.append q).length = p.length + q.length + 1 := by
  fun_induction append p q <;> grind

/-- Reversing a singleton is a no-op. -/
@[simp, scoped grind =] lemma singleton_reverse_eq (v : α) :
  (VertexSeq.singleton v).reverse = .singleton v := rfl

/-- The tail of an appended sequence is the tail of the second sequence. -/
@[simp, scoped grind =] lemma tail_on_tail (p q : VertexSeq α) : (p.append q).tail = q.tail := by
  fun_induction append <;> simp_all [tail]

/-- The head of an appended sequence is the head of the first sequence. -/
@[simp, scoped grind =] lemma head_on_head (p q : VertexSeq α) : (p.append q).head = p.head := by
  fun_induction append <;> simp_all

/-- The tail of a sequence appended with a singleton is the singleton's vertex. -/
@[simp, scoped grind =] lemma tail_on_tail_singleton (p : VertexSeq α) (x : α) :
    (p.append (.singleton x)).tail = x := by
  unfold append
  unfold tail
  split <;> aesop

/-- The head of a singleton appended with a sequence is the singleton's vertex. -/
@[simp, scoped grind =] lemma head_on_head_singleton (p : VertexSeq α) (x : α) :
  ((VertexSeq.singleton x).append p).head = x := by
  unfold append
  unfold head
  split <;> aesop

/-- Append is associative. -/
@[simp, scoped grind =] lemma append_assoc (p q r : VertexSeq α) :
    (p.append q).append r = p.append (q.append r) := by
  fun_induction append q r <;> simp_all [append]

/-- Reversing a concatenation distributes as `q.reverse.append p.reverse`. -/
@[simp, scoped grind =] lemma reverse_append (p q : VertexSeq α) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  fun_induction append <;> simp_all [reverse]

/-- Reversing a vertex sequence twice yields the original sequence. -/
@[simp, scoped grind =] lemma reverse_reverse (p : VertexSeq α) : (p.reverse).reverse = p := by
  fun_induction reverse p <;> aesop

/-- The head of a reversed sequence is the tail of the original. -/
@[simp, scoped grind =] lemma head_reverse (p : VertexSeq α) : (p.reverse).head = p.tail := by
  fun_induction reverse p <;> aesop

/-- The tail of a reversed sequence is the head of the original. -/
@[simp, scoped grind =] lemma tail_reverse (p : VertexSeq α) : (p.reverse).tail = p.head := by
  fun_induction reverse p <;> aesop

/-- Dropping the tail preserves the head. -/
@[simp, scoped grind =] lemma dropTail_head (p : VertexSeq α) : p.dropTail.head = p.head := by
  fun_induction reverse p <;> aesop

/-! ## takeUntil, dropUntil, loopErase -/

/-- Truncate the sequence at the first occurrence of `v`, retaining `v` as the new tail. -/
@[simp, scoped grind] def takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
  (h : v ∈ w.toList) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then takeUntil w2 v h2
    else .cons w2 x

/-- Drop the prefix up to the last occurrence of `v`, retaining `v` as the new head. -/
@[simp, scoped grind] def dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
  (h : v ∈ w.toList) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then .cons (dropUntil w2 v h2) x
    else .singleton x

/-- `takeUntil` does not increase the length of the sequence. -/
@[simp] lemma takeUntil_length_le [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.takeUntil v h).length ≤ w.length := by
  fun_induction takeUntil w v h <;> grind

/-- `dropUntil` does not increase the length of the sequence. -/
@[simp] lemma dropUntil_length_le [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.dropUntil v h).length ≤ w.length := by
  fun_induction dropUntil w v h <;> grind

/-- The head of `takeUntil w v h` is the head of `w`. -/
@[simp, scoped grind =] lemma head_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (takeUntil w v h).head = w.head := by
  induction w <;> grind

/-- The tail of `takeUntil w v h` is `v`. -/
@[simp, scoped grind =] lemma tail_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (takeUntil w v h).tail = v := by
  induction w <;> grind

/-- Membership in `takeUntil` implies membership in the original sequence. -/
@[simp, scoped grind →] lemma mem_takeUntil [DecidableEq α] (w : VertexSeq α)
  (v x : α) (h : v ∈ w.toList) : x ∈ (takeUntil w v h).toList → x ∈ w.toList := by
  induction w generalizing v <;> grind

/-- The head of `dropUntil w v h` is `v`. -/
@[simp, scoped grind =] lemma head_dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) :
    (w.dropUntil v h).head = v := by
  induction w <;> grind

/-- The tail of `dropUntil w v h` is the tail of `w`. -/
@[simp, scoped grind =] lemma tail_dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) :
    (w.dropUntil v h).tail = w.tail := by
  fun_induction VertexSeq.dropUntil w v h <;> simp [VertexSeq.tail]

/-- Membership in `dropUntil` implies membership in the original sequence. -/
@[simp, scoped grind →] lemma mem_dropUntil [DecidableEq α] (w : VertexSeq α) (v x : α)
    (h : v ∈ w.toList) : x ∈ (w.dropUntil v h).toList → x ∈ w.toList := by
  induction w generalizing v <;> grind

/-- Erase all loops from a vertex sequence by repeatedly truncating at the first repeated
vertex. The result has no duplicate vertices. -/
@[scoped grind] def loopErase [DecidableEq α] : VertexSeq α → VertexSeq α
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

/-- Every vertex in the loop-erased sequence was present in the original. -/
lemma mem_loopErase [DecidableEq α] (w : VertexSeq α) :
    ∀ {x : α}, x ∈ w.loopErase.toList → x ∈ w.toList := by
  fun_induction loopErase w <;> grind [toList, mem_takeUntil]

/-- The vertex list of a loop-erased sequence has no duplicates. -/
theorem loopErase_nodup [DecidableEq α] (w : VertexSeq α) : w.loopErase.toList.Nodup := by
  fun_induction VertexSeq.loopErase w <;> grind [toList, mem_loopErase]

/-- Loop erasure preserves the head of the sequence. -/
@[simp] lemma head_loopErase [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.head = w.head := by
  fun_induction loopErase w <;> simp_all

/-- Loop erasure preserves the tail of the sequence. -/
@[simp] lemma tail_loopErase [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.tail = w.tail := by
  fun_induction loopErase w <;> simp_all

end VertexSeq

/-! ## IsWalk, Walk core data -/

/-- `IsWalk w` asserts that the vertex sequence `w` is a valid walk: every pair of
consecutive vertices is distinct. -/
@[scoped grind] inductive IsWalk : VertexSeq α → Prop
  | singleton (v : α) : IsWalk (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsWalk w)
      (hneq : w.tail ≠ u)
    : IsWalk (.cons w u)

scoped grind_pattern IsWalk.singleton => IsWalk (.singleton v)
scoped grind_pattern IsWalk.cons => IsWalk (.cons w u)

/-- A walk in a graph, consisting of a nonempty vertex sequence together with a proof that
consecutive vertices are distinct. -/
structure Walk (α : Type*) where
  /-- The underlying vertex sequence. -/
  seq : VertexSeq α
  /-- Proof that the vertex sequence is a valid walk. -/
  isWalk : IsWalk seq

namespace Walk
open VertexSeq

/-- Two walks are equal if and only if their underlying vertex sequences are equal. -/
@[ext] lemma ext {w1 w2 : Walk α} (hseq : w1.seq = w2.seq) : w1 = w2 := by
  cases w1
  cases w2
  cases hseq
  rfl

/-! ## Basic IsWalk helper lemmas -/

/-- The prefix of a valid walk is itself a valid walk. -/
@[simp, scoped grind =>] lemma iswalk_prefix (w2 : VertexSeq α) (v : α)
    (valid : IsWalk (w2.cons v)) : IsWalk w2 := by
  cases valid
  grind

/-- In a valid walk `w2.cons v`, the tail of `w2` differs from `v`. -/
@[simp, scoped grind <=] lemma tail_neq_of_iswalk (w2 : VertexSeq α) (v : α)
    (valid : IsWalk (w2.cons v)) : w2.tail ≠ v := by
  cases valid
  grind

/-- Appending two valid walks whose junction vertices are distinct yields a valid walk. -/
@[scoped grind ←]
lemma is_walk_two_seqs_append_of (w1 w2 : VertexSeq α)
  (h1 : IsWalk w1) (h2 : IsWalk w2) (hneq : w1.tail ≠ w2.head) :
    IsWalk (w1.append w2) := by
  fun_induction w1.append w2 <;> grind

/-- Prepending a singleton vertex to a valid walk yields a valid walk, provided the vertex
is distinct from the walk's head. -/
@[scoped grind ←]
theorem prepend_iswalk (p : VertexSeq α) (v : α) (h : IsWalk p) (h2 : p.head ≠ v) :
  IsWalk ((VertexSeq.singleton v).append p) := by grind

/-- Reversing a valid walk yields a valid walk. -/
@[scoped grind →, scoped grind ←]
lemma isWalk_rev_if (w : VertexSeq α) : IsWalk w → IsWalk w.reverse := by
  intro h
  induction h <;> grind

/-- Appending two sequences that form a valid walk implies each piece is a valid walk and
the junction vertices are distinct. -/
@[scoped grind →]
theorem is_walk_neq_of_append (p q : VertexSeq α) (h : IsWalk (p.append q))
  : IsWalk p ∧ IsWalk q ∧ p.tail ≠ q.head := by fun_induction append <;> grind

/-- If the reverse of a vertex sequence is a valid walk, then so is the original. -/
@[scoped grind →]
lemma isWalk_rev_imp (w : VertexSeq α) : IsWalk w.reverse → IsWalk w := by
  fun_induction reverse <;> grind

/-- A vertex sequence is a valid walk if and only if its reverse is. -/
@[simp, scoped grind =]
lemma isWalk_rev_iff (w : VertexSeq α) : IsWalk w.reverse ↔ IsWalk w := by grind

/-- A vertex sequence with no duplicate vertices is a valid walk. -/
lemma nodup_iswalk (w : VertexSeq α) (h : w.toList.Nodup) : IsWalk w := by
  induction w <;> grind

/-- Truncating a valid walk at a vertex in its list yields a valid walk. -/
@[scoped grind →]
lemma takeUntil_iswalk [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
  (hw : IsWalk w) :
    IsWalk (w.takeUntil v h) := by
  induction hw generalizing v <;> grind

/-- The suffix of a valid walk obtained by `dropUntil` is a valid walk. -/
@[scoped grind →]
lemma dropUntil_iswalk [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) (hw : IsWalk w) :
    IsWalk (w.dropUntil v h) := by
  induction hw generalizing v <;> grind

/-- The loop erasure of any vertex sequence is a valid walk. -/
lemma loopErase_iswalk [DecidableEq α] (w : VertexSeq α) : IsWalk w.loopErase := by
  grind [nodup_iswalk, loopErase_nodup]

/-! ## support, head, tail, length, dropTail for Walk -/

/-- The list of vertices visited by the walk, in order. -/
@[simp, scoped grind] def support (w : Walk α) : List α := w.seq.toList

/-- The first vertex of the walk. -/
abbrev head (w : Walk α) : α := w.seq.head

/-- The last vertex of the walk. -/
abbrev tail (w : Walk α) : α := w.seq.tail

/-- The number of edges in the walk. -/
abbrev length (w : Walk α) : ℕ := w.seq.length

/-- The walk obtained by removing the last vertex. -/
abbrev dropTail (w : Walk α) : Walk α :=
  { seq := w.seq.dropTail
    isWalk := by grind [Walk]}

/-- Extend a walk by appending a single vertex, given a proof that it differs from the
current tail. -/
def append_single (w : Walk α) (u : α) (h : u ≠ w.tail) : Walk α :=
  ⟨w.seq.cons u, .cons w.seq u w.isWalk (by aesop)⟩

/-- Dropping the tail of a walk preserves its head. -/
@[simp, scoped grind =]
lemma dropTail_head (w : Walk α) : w.dropTail.head = w.head := by
  cases w; induction isWalk <;> grind

/-- If the tail of `w.dropTail` equals `w.tail`, then `w` has length 0. -/
@[simp, scoped grind .]
lemma len_zero_of_drop_tail_eq_tail (w : Walk α) (h : w.dropTail.tail = w.tail) :
    w.length = 0 := by
  cases w; induction isWalk <;> grind

/-- A walk of length 0 has equal head and tail. -/
@[simp, scoped grind ←]
lemma head_eq_tail_of_length_zero (w : Walk α) (h : w.length = 0)
  : w.head = w.tail := by
  cases w; induction isWalk <;> grind


/-! ## Walk append, reverse and related lemmas -/

/-- Appending the underlying sequences of two walks yields a valid walk when their junction
vertices are distinct. -/
@[scoped grind ←]
lemma two_seqs_append_of (w1 w2 : Walk α) (hneq : w1.tail ≠ w2.head) :
    IsWalk (w1.seq.append w2.seq) := by
  cases w1; cases w2; grind

/-- Concatenate two walks whose tail and head agree. The shared vertex appears only once
in the result. -/
@[scoped grind =]
def append (w1 w2 : Walk α) (h : w1.tail = w2.head) : Walk α :=
  if h1 : w1.length = 0 then w2
  else
    { seq := w1.dropTail.seq.append w2.seq
      isWalk := by grind [Walk]}

/-- Reverse a walk, swapping its head and tail. -/
@[scoped grind =]
def reverse (w : Walk α) : Walk α :=
  { seq := w.seq.reverse
    isWalk := by grind [Walk]}

/-- The head of a reversed walk is the tail of the original. -/
@[simp, scoped grind =] lemma head_reverse (w : Walk α) : (w.reverse).head = w.tail := by grind

/-- The tail of a reversed walk is the head of the original. -/
@[simp, scoped grind =] lemma tail_reverse (w : Walk α) : (w.reverse).tail = w.head := by grind

/-- The head of an appended walk is the head of the first walk. -/
@[simp, scoped grind =] lemma head_on_head (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).head = w1.head := by
  cases w1; induction isWalk <;> grind

/-- The tail of an appended walk is the tail of the second walk. -/
@[simp, scoped grind =] lemma tail_on_tail (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).tail = w2.tail := by grind

/-- The length of an appended walk is the sum of the lengths of its parts. -/
@[simp, scoped grind =] lemma length_append (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).length = w1.length + w2.length := by
  unfold Walk.append
  by_cases h1 : w1.length = 0
  · grind
  · have hdrop : w1.dropTail.length + 1 = w1.length := by
      cases w1; induction isWalk <;> grind
    grind

/-! ## Path, cycle -/

/-- A walk is a *path* if its support has no duplicate vertices. -/
@[scoped grind] def IsPath (w : Walk α) : Prop := w.support.Nodup

/-- Loop-erase a walk to obtain a walk with no repeated vertices. -/
abbrev toPath [DecidableEq α] (w : Walk α) : Walk α :=
  { seq := w.seq.loopErase
    isWalk := loopErase_iswalk w.seq }

/-- The walk produced by `toPath` is a path. -/
theorem toPath_isPath [DecidableEq α] (w : Walk α) : IsPath (toPath w) := by
  unfold IsPath toPath support
  simpa using loopErase_nodup w.seq

/-- Loop erasure preserves the tail of a walk. -/
lemma tail_toPath [DecidableEq α] (w : Walk α) : (toPath w).tail = w.tail := by
  grind [tail_loopErase]

/-- Loop erasure preserves the head of a walk. -/
lemma head_toPath [DecidableEq α] (w : Walk α) : (toPath w).head = w.head := by
  grind [head_loopErase]

/-- A walk is a *cycle* if it has length at least 3, its head equals its tail, and the walk
with its tail dropped is a path. -/
def IsCycle (w : Walk α) : Prop :=
  3 ≤ w.length ∧ w.head = w.tail ∧ IsPath w.dropTail


/-! ## Some more helper lemmas -/

/-- Taking until the head of a sequence yields just the singleton of that head. -/
@[simp, scoped grind .] lemma takeUntil_head_eq_singleton [DecidableEq α] (w : VertexSeq α)
  (h : w.head ∈ w.toList) :
  w.takeUntil w.head h = VertexSeq.singleton w.head := by
  induction w <;> grind

/-- Dropping until the head of a sequence returns the original sequence. -/
@[simp, scoped grind .] lemma dropUntil_head_eq_self [DecidableEq α] (w : VertexSeq α)
  (h : w.head ∈ w.toList) :
  w.dropUntil w.head h = w := by
  induction w <;> grind

/-- A vertex sequence can be split at any interior vertex into a prefix (with tail dropped)
appended to a suffix. -/
@[simp, scoped grind →] lemma vertex_seq_split [DecidableEq α]
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList) (hne : v ≠ w.head) :
  (w.takeUntil v h).dropTail.append (w.dropUntil v h) = w := by
  induction w generalizing v <;> grind

/-- Any walk can be split at a vertex in its support into two sub-walks joined at that
vertex. -/
@[simp, scoped grind →] lemma walk_split [DecidableEq α]
  (w : Walk α) (u : α) (hu : u ∈ w.support) :
    w = Walk.append
      ⟨w.seq.takeUntil u hu, takeUntil_iswalk w.seq u hu w.isWalk⟩
      ⟨w.seq.dropUntil u hu, dropUntil_iswalk w.seq u hu w.isWalk⟩
      (by grind) := by
  by_cases h : u = w.head
  · ext; grind
  · ext; grind


/-! ## Re-rooting a cycle -/

/-- Re-root a cycle at any chosen vertex in its support. -/
@[simp, scoped grind] def rerootCycle [DecidableEq α] (w : Walk α) (hcyc : IsCycle w)
    (u : α) (hu : u ∈ w.support) : Walk α :=
  Walk.append
    ⟨w.seq.dropUntil u hu, dropUntil_iswalk w.seq u hu w.isWalk⟩
    ⟨w.seq.takeUntil u hu, takeUntil_iswalk w.seq u hu w.isWalk⟩
    (by rcases hcyc with ⟨_, hht, _⟩; grind)

/-- The vertex list of an appended vertex sequence is the concatenation in reverse order. -/
@[simp, scoped grind =] lemma toList_append (p q : VertexSeq α) :
    (p.append q).toList = q.toList ++ p.toList := by
  induction q generalizing p <;> grind

/-- Dropping the tail of an appended walk commutes with append when the second walk is
non-trivial. -/
lemma append_dropTail_eq_dropTail_append (w1 w2 : Walk α) (h : w1.tail = w2.head)
  (hlen : w2.head ≠ w2.tail) :
  (Walk.append w1 w2 h).dropTail = Walk.append w1 w2.dropTail (by grind) := by
  by_cases h1 : w1.length = 0
  · grind
  · ext; cases w2; induction isWalk <;> grind

/-- Re-rooting a cycle at any vertex in its support yields a cycle. -/
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

/-! ## Walks in a SimpleGraph -/

section WalksInGraphs

variable [DecidableEq α]

namespace VertexSeq

/-- `IsVertexSeqIn G w` asserts that the vertex sequence `w` is a walk in the simple
graph `G`: the first vertex belongs to `G` and every consecutive pair is an edge of `G`. -/
@[scoped grind] inductive IsVertexSeqIn (G : SimpleGraph α) : VertexSeq α → Prop
  | singleton (v : α) (hv : v ∈ V(G)) : IsVertexSeqIn G (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsVertexSeqIn G w)
      (he : s(w.tail, u) ∈ E(G)) :
      IsVertexSeqIn G (.cons w u)

/-- Abbreviation: `w` is a vertex sequence in `G`. -/
abbrev vertex_seq_in (w : VertexSeq α) (G : SimpleGraph α) := IsVertexSeqIn G w

/-- The set of edges traversed by the vertex sequence, as a `Finset` of unordered pairs. -/
abbrev edgeSet (w : VertexSeq α) : Finset (Sym2 α) :=
  match w with
  | .singleton _ => ∅
  | .cons w u => w.edgeSet ∪ {s(w.tail, u)}

/-- A vertex sequence is in `G` if and only if its head is a vertex of `G` and every edge
it traverses belongs to `G`. -/
@[simp] lemma is_vertex_seq_in_iff (G : SimpleGraph α) (p : VertexSeq α) :
  IsVertexSeqIn G p ↔ p.head ∈ V(G) ∧ p.edgeSet ⊆ E(G) := by
  induction p <;> grind

/-- The edge set of `takeUntil` is a subset of the original edge set. -/
lemma takeUntil_edgeSet (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) :
    (w.takeUntil v h).edgeSet ⊆ w.edgeSet := by
  induction w generalizing v
  · intro a ha; simp [takeUntil] at ha
  · by_cases h2 : v ∈ w_1.toList
    · grind
    · simp [takeUntil, h2]

/-- The edge set of a loop-erased sequence is a subset of the original edge set. -/
lemma loopErase_edgeSet (w : VertexSeq α) :
    w.loopErase.edgeSet ⊆ w.edgeSet := by
  suffices h : ∀ n : ℕ, ∀ w : VertexSeq α,
      w.length = n → w.loopErase.edgeSet ⊆ w.edgeSet by grind
  intro n; refine Nat.strong_induction_on n ?_
  intro n ih w hlen; cases w
  · intro a ha; simp [loopErase, edgeSet] at ha
  · by_cases hmem : v ∈ w_1.toList
    · grind [takeUntil_edgeSet, takeUntil_length_le]
    · intro a ha
      have ha' : a = s(w_1.loopErase.tail, v) ∨ a ∈ w_1.loopErase.edgeSet := by
        simpa [loopErase, hmem] using ha
      grind [tail_loopErase]

end VertexSeq
