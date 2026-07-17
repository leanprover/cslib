/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Cslib.Foundations.Data.BitstringEncoding
import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-!
# Polynomial-time computable functions between encoded types

This file abstracts the low-level `SingleTapeTM.PolyTimeComputable` predicate (about functions
`List Bool → List Bool`) into `IsComputableInPolyTime`, a predicate on functions `f : α → β`
between arbitrary types carrying a `BitstringEncoding`. It then develops a small library of
combinators establishing that standard functions on `Option`s, products and lists are
polynomial-time computable, which is what one needs to reason about complexity classes without
re-deriving Turing machines for every operation.

## Main results

* `IsComputableInPolyTime.comp`: closure under composition.
* `IsComputableInPolyTime.finite`: any function out of a finite type is polynomial-time computable.
* `IsComputableInPolyTime.optionMap`: `Option.map` preserves polynomial-time computability.
* `IsComputableInPolyTime_fst`: the first projection on encoded pairs of bitstrings, witnessed by
  the machines `takeFirstBlockComputer` and `undelimitBlockComputer`.
* `IsComputableInPolyTime_decode`: decoding a bitstring as a pair of bitstrings, witnessed by the
  validating parser `tagBlockComputer`.
-/

open Computability Turing

namespace ComplexityTheory

/--
A simple definition to abstract the notion of a poly-time Turing machine into a predicate.
-/
def IsComputableInPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) : Prop :=
  ∃ f' : List Bool → List Bool,
    Nonempty (Cslib.Turing.SingleTapeTM.PolyTimeComputable f') ∧
    ∀ x, f' (BitstringEncoding.encode x) = BitstringEncoding.encode (f x)

lemma IsComputableInPolyTime.comp {α β γ : Type}
    [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    {f : α → β} {g : β → γ}
    (hf : IsComputableInPolyTime f) (hg : IsComputableInPolyTime g) :
    IsComputableInPolyTime (g ∘ f) := by
  rcases hf with ⟨f', ⟨hft, hfe⟩⟩
  rcases hg with ⟨g', ⟨hgt, hge⟩⟩
  use g' ∘ f'
  constructor
  · exact Nonempty.intro ((Classical.choice hft).comp' (Classical.choice hgt))
  · intro x
    simp only [Function.comp_apply, hfe, hge]

/--
A function with a finite domain is always computable in polynomial time, since we can just
hardcode the output for each input.
-/
lemma IsComputableInPolyTime.finite {α β : Type}
    [Finite α] [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) : IsComputableInPolyTime f := by
  -- We hardcode the output for each input into a lookup table: over the finite set of encodings
  -- of `α`, the function `g` below decodes the input and re-encodes `f` of it. Any function with a
  -- finite domain of interest is polynomial-time computable via `ofFinsetDomain`.
  have : Fintype α := Fintype.ofFinite α
  set S : Finset (List Bool) := Finset.univ.image (BitstringEncoding.encode : α → List Bool)
    with hS
  set g : List Bool → List Bool :=
    fun s => (BitstringEncoding.decode s).elim [] fun x => BitstringEncoding.encode (f x) with hg
  refine ⟨fun s => if s ∈ S then g s else [],
    ⟨Cslib.Turing.SingleTapeTM.PolyTimeComputable.ofFinsetDomain g S⟩, ?_⟩
  intro x
  have hx : BitstringEncoding.encode x ∈ S := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
  simp only [hg, if_pos hx]
  simp

/--
If `f` is polynomial-time computable, then so is `Option.map f`. The underlying machine preserves
the leading `some`/`none` tag of the encoding and runs the machine for `f` on the payload.
-/
lemma IsComputableInPolyTime.optionMap {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} (hf : IsComputableInPolyTime f) :
    IsComputableInPolyTime (Option.map f) := by
  obtain ⟨f', ⟨hft, hfe⟩⟩ := hf
  refine ⟨Cslib.Turing.SingleTapeTM.onTailFun f', ⟨(Classical.choice hft).onTail⟩, ?_⟩
  intro o
  cases o with
  | none => rfl
  | some a =>
    change true :: f' (BitstringEncoding.encode a) = true :: BitstringEncoding.encode (f a)
    rw [hfe a]

/-!
### First projection of an encoded pair

The pair encoding is `encode (x, w) = delimit (encode x) ++ encode w`. We recover `encode x` in two
polynomial-time steps, following the structure of the encoding:

* `takeFirstBlock` keeps the leading self-delimiting block `delimit (encode x)`, dropping the rest.
  On a tape this is a scan to the end of the first block followed by erasing the suffix — no
  compaction, since the kept prefix stays in place.
* `undelimitBlock` turns a single self-delimiting block `delimit P` into its payload `P`. This is
  the genuine compaction (removing the framing bits), a quadratic-time single-tape operation.

Composing the two computes `Prod.fst` at the level of encodings.
-/

/-- Keep the leading self-delimiting block of a bitstring, dropping everything after it. On a pair
encoding `delimit (encode x) ++ encode w` this returns `delimit (encode x)`. -/
def takeFirstBlock : List Bool → List Bool
  | [] => []
  | false :: _ => [false]
  | true :: b :: rest => true :: b :: takeFirstBlock rest
  | [true] => [true]

/-- Strip the framing of a single self-delimiting block, returning its payload. On `delimit P` this
returns `P`. -/
def undelimitBlock : List Bool → List Bool
  | [] => []
  | false :: _ => []
  | true :: b :: rest => b :: undelimitBlock rest
  | [true] => []

@[simp]
lemma takeFirstBlock_delimit_append (P Q : List Bool) :
    takeFirstBlock (BitstringEncoding.delimit P ++ Q) = BitstringEncoding.delimit P := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [BitstringEncoding.delimit, List.cons_append, takeFirstBlock, ih]

@[simp]
lemma undelimitBlock_delimit (P : List Bool) :
    undelimitBlock (BitstringEncoding.delimit P) = P := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [BitstringEncoding.delimit, undelimitBlock, ih]

section TakeFirstBlockMachine

open Cslib.Turing Cslib.Turing.SingleTapeTM

/-! Small `StackTape`/`BiTape` helpers for reasoning about a left-to-right scan. -/

@[simp] lemma mapSome_head (l : List Bool) : (StackTape.mapSome l).head = l.head? := by
  cases l <;> rfl

@[simp] lemma mapSome_tail (l : List Bool) :
    (StackTape.mapSome l).tail = StackTape.mapSome l.tail := by
  cases l <;> rfl

@[simp] lemma cons_some_mapSome (a : Bool) (l : List Bool) :
    StackTape.cons (some a) (StackTape.mapSome l) = StackTape.mapSome (a :: l) := rfl

@[simp] lemma cons_head?_mapSome (l : List Bool) :
    StackTape.cons l.head? (StackTape.mapSome l.tail) = StackTape.mapSome l := by
  cases l <;> rfl

@[simp] lemma cons_none_empty : StackTape.cons none (∅ : StackTape Bool) = ∅ := rfl

@[simp] lemma mapSome_nil : StackTape.mapSome ([] : List Bool) = ∅ := rfl

@[simp] lemma empty_head : (∅ : StackTape Bool).head = none := rfl

@[simp] lemma empty_tail : (∅ : StackTape Bool).tail = ∅ := rfl

/-- Tape configuration during a left-to-right scan: `done` has already been scanned (it sits in the
left half, reversed) and `rest` lies under and to the right of the head. -/
def splitTape (done rest : List Bool) : BiTape Bool :=
  ⟨rest.head?, StackTape.mapSome done.reverse, StackTape.mapSome rest.tail⟩

@[simp] lemma splitTape_nil_left (rest : List Bool) : splitTape [] rest = BiTape.mk₁ rest := by
  cases rest <;> rfl

/-- Scanning one cell to the right (keeping it) moves it into the scanned prefix. -/
lemma splitTape_scan (done : List Bool) (c : Bool) (rest : List Bool) :
    ((splitTape done (c :: rest)).write (some c)).optionMove (some .right)
      = splitTape (done ++ [c]) rest := by
  simp only [splitTape, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight,
    List.head?_cons, List.tail_cons, mapSome_head, mapSome_tail, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, cons_some_mapSome]

/-- Rewinding one cell to the left undoes one scan step. -/
lemma splitTape_rewind (done : List Bool) (c : Bool) (rest : List Bool) :
    (splitTape (done ++ [c]) rest).optionMove (some .left) = splitTape done (c :: rest) := by
  simp only [splitTape, BiTape.optionMove, BiTape.move, BiTape.moveLeft, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, mapSome_head,
    mapSome_tail, List.head?_cons, List.tail_cons, cons_head?_mapSome]

/-- States of the `takeFirstBlock` machine. -/
inductive TFBState
  /-- Initial state (needed to distinguish empty input, which halts, from a full-input block). -/
  | scanStart
  /-- Scanning, expecting `true`/`false` at the start of a block cell pair. -/
  | scanTF
  /-- Scanning, expecting the payload bit after a `true`. -/
  | scanB
  /-- Erasing the suffix after the block-terminating `false`. -/
  | eraseQ
  /-- Rewinding leftward, skipping the erased (blank) suffix cells. -/
  | rewindSkipQ
  /-- Rewinding leftward through the block back to its start. -/
  | rewindBlock
  deriving DecidableEq, Fintype

/-- The machine keeping the leading self-delimiting block: scan to the end of the first block,
erase the suffix, and rewind to the start. No compaction is involved. -/
def takeFirstBlockComputer : SingleTapeTM Bool where
  State := TFBState
  q₀ := .scanStart
  tr q sym :=
    match q, sym with
    -- empty input: halt immediately with empty output
    | .scanStart, none => (⟨none, none⟩, none)
    | .scanStart, some true => (⟨some true, some .right⟩, some .scanB)
    | .scanStart, some false => (⟨some false, some .right⟩, some .eraseQ)
    -- end of input with the block spanning the whole input: rewind
    | .scanTF, none => (⟨none, none⟩, some .rewindSkipQ)
    | .scanTF, some true => (⟨some true, some .right⟩, some .scanB)
    | .scanTF, some false => (⟨some false, some .right⟩, some .eraseQ)
    -- end of input just after a lone `true`: rewind
    | .scanB, none => (⟨none, none⟩, some .rewindSkipQ)
    | .scanB, some b => (⟨some b, some .right⟩, some .scanTF)
    | .eraseQ, none => (⟨none, none⟩, some .rewindSkipQ)
    | .eraseQ, some _ => (⟨none, some .right⟩, some .eraseQ)
    | .rewindSkipQ, none => (⟨none, some .left⟩, some .rewindSkipQ)
    -- found the block's rightmost cell: switch to rewinding through the block (no move)
    | .rewindSkipQ, some b => (⟨some b, none⟩, some .rewindBlock)
    | .rewindBlock, some b => (⟨some b, some .left⟩, some .rewindBlock)
    -- reached the blank just left of the block: step back onto its first cell and halt
    | .rewindBlock, none => (⟨none, some .right⟩, none)

private lemma splitTape_head_cons (done : List Bool) (c : Bool) (rest : List Bool) :
    (splitTape done (c :: rest)).head = some c := rfl

/-! ### Scan phase single steps -/

private lemma tfb_scanStart_true (rest : List Bool) :
    takeFirstBlockComputer.TransitionRelation
      ⟨some .scanStart, BiTape.mk₁ (true :: rest)⟩ ⟨some .scanB, splitTape [true] rest⟩ := by
  rw [← splitTape_nil_left]; simp only [TransitionRelation, SingleTapeTM.step,
    takeFirstBlockComputer, splitTape_head_cons, splitTape_scan, List.nil_append]

private lemma tfb_scanStart_false (rest : List Bool) :
    takeFirstBlockComputer.TransitionRelation
      ⟨some .scanStart, BiTape.mk₁ (false :: rest)⟩ ⟨some .eraseQ, splitTape [false] rest⟩ := by
  rw [← splitTape_nil_left]; simp only [TransitionRelation, SingleTapeTM.step,
    takeFirstBlockComputer, splitTape_head_cons, splitTape_scan, List.nil_append]

private lemma tfb_scanTF_true (done rest : List Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .scanTF, splitTape done (true :: rest)⟩
      ⟨some .scanB, splitTape (done ++ [true]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma tfb_scanTF_false (done rest : List Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .scanTF, splitTape done (false :: rest)⟩
      ⟨some .eraseQ, splitTape (done ++ [false]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma tfb_scanB_step (done : List Bool) (b : Bool) (rest : List Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .scanB, splitTape done (b :: rest)⟩
      ⟨some .scanTF, splitTape (done ++ [b]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma tfb_scanTF_nil (done : List Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .scanTF, splitTape done []⟩
      ⟨some .rewindSkipQ, splitTape done []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, splitTape,
    List.head?_nil, List.tail_nil, BiTape.write, BiTape.optionMove]

private lemma tfb_scanB_nil (done : List Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .scanB, splitTape done []⟩
      ⟨some .rewindSkipQ, splitTape done []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, splitTape,
    List.head?_nil, List.tail_nil, BiTape.write, BiTape.optionMove]

/-! ### Erase phase -/

/-- The left half of the tape during the erase/rewind phases: `block` reversed, buried under `n`
blanks (the erased suffix cells). -/
private def blanksLeft (n : ℕ) (block : List Bool) : StackTape Bool :=
  (StackTape.cons none)^[n] (StackTape.mapSome block.reverse)

private lemma blanksLeft_succ (n : ℕ) (block : List Bool) :
    blanksLeft (n + 1) block = StackTape.cons none (blanksLeft n block) := by
  simp only [blanksLeft, Function.iterate_succ_apply']

/-- Tape while erasing the suffix: `block` (with `n` erased blanks) sits in the left half, `suffix`
lies under and to the right of the head. -/
private def eraseTape (n : ℕ) (block suffix : List Bool) : BiTape Bool :=
  ⟨suffix.head?, blanksLeft n block, StackTape.mapSome suffix.tail⟩

private lemma tfb_eraseQ_step (n : ℕ) (block : List Bool) (s : Bool) (suffix : List Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .eraseQ, eraseTape n block (s :: suffix)⟩
      ⟨some .eraseQ, eraseTape (n + 1) block suffix⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, eraseTape,
    List.head?_cons, List.tail_cons, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight,
    mapSome_head, mapSome_tail, blanksLeft_succ]

/-- Erasing the whole suffix, ending in the `eraseQ` state on an all-blank right half. -/
private lemma tfb_erase_phase (block suffix : List Bool) (n : ℕ) :
    Relation.RelatesInSteps takeFirstBlockComputer.TransitionRelation
      ⟨some .eraseQ, eraseTape n block suffix⟩
      ⟨some .eraseQ, eraseTape (n + suffix.length) block []⟩ suffix.length := by
  induction suffix generalizing n with
  | nil => simp only [List.length_nil, Nat.add_zero]; exact Relation.RelatesInSteps.refl _
  | cons s suffix ih =>
    have hstep := tfb_eraseQ_step n block s suffix
    have hrest := ih (n + 1)
    rw [show n + (s :: suffix).length = (n + 1) + suffix.length by simp; omega]
    exact Relation.RelatesInSteps.head _ _ _ _ hstep hrest

/-! ### Rewind phase -/

/-- Tape while rewinding leftward: `block` reversed under `n` blanks, head on the blanks. -/
private def rewindTape (n : ℕ) (block : List Bool) : BiTape Bool :=
  ⟨none, blanksLeft n block, ∅⟩

private lemma eraseTape_nil (n : ℕ) (block : List Bool) :
    eraseTape n block [] = rewindTape n block := rfl

/-- On reaching the end of the erased suffix, switch from erasing to rewinding. -/
private lemma tfb_eraseQ_nil (n : ℕ) (block : List Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .eraseQ, rewindTape n block⟩
      ⟨some .rewindSkipQ, rewindTape n block⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, rewindTape,
    BiTape.write, BiTape.optionMove]

/-- Rewinding one blank of the erased suffix. -/
private lemma tfb_rewindSkipQ_step (n : ℕ) (block : List Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .rewindSkipQ, rewindTape (n + 1) block⟩
      ⟨some .rewindSkipQ, rewindTape n block⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, rewindTape,
    blanksLeft_succ, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft,
    StackTape.head_cons, StackTape.tail_cons, cons_none_empty]

/-- Rewinding past all erased blanks. -/
private lemma tfb_rewindSkipQ_phase (n : ℕ) (block : List Bool) :
    Relation.RelatesInSteps takeFirstBlockComputer.TransitionRelation
      ⟨some .rewindSkipQ, rewindTape n block⟩ ⟨some .rewindSkipQ, rewindTape 0 block⟩ n := by
  induction n with
  | zero => exact Relation.RelatesInSteps.refl _
  | succ n ih =>
    exact Relation.RelatesInSteps.head _ _ _ _ (tfb_rewindSkipQ_step n block) ih

private lemma splitTape_write_head (done : List Bool) (c : Bool) (rest : List Bool) :
    (splitTape done (c :: rest)).write (some c) = splitTape done (c :: rest) := rfl

private lemma mk₁_eq (l : List Bool) :
    BiTape.mk₁ l = ⟨l.head?, ∅, StackTape.mapSome l.tail⟩ := by cases l <;> rfl

/-- On reaching the block's rightmost cell, step onto it (rewinding no further blanks). -/
private lemma tfb_rewindSkipQ_last (block' : List Bool) (c : Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .rewindSkipQ, rewindTape 0 (block' ++ [c])⟩
      ⟨some .rewindSkipQ, splitTape block' [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, rewindTape, blanksLeft,
    Function.iterate_zero, id_eq, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveLeft, mapSome_head, mapSome_tail, List.head?_cons, List.tail_cons, cons_none_empty,
    mapSome_nil, splitTape]

/-- Switch from skipping blanks to rewinding the block. -/
private lemma tfb_rewindSkipQ_to_block (block' : List Bool) (c : Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .rewindSkipQ, splitTape block' [c]⟩
      ⟨some .rewindBlock, splitTape block' [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, splitTape_head_cons,
    splitTape_write_head, BiTape.optionMove]

/-- Rewinding one block cell leftward (moving it back into the right half). -/
private lemma tfb_rewindBlock_step (D : List Bool) (d e : Bool) (rest : List Bool) :
    takeFirstBlockComputer.TransitionRelation ⟨some .rewindBlock, splitTape (D ++ [d]) (e :: rest)⟩
      ⟨some .rewindBlock, splitTape D (d :: e :: rest)⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, splitTape_head_cons,
    splitTape_write_head, splitTape_rewind]

/-- Rewinding the whole block back to the leftmost cell. -/
private lemma tfb_rewindBlock_phase :
    ∀ (done rest : List Bool), rest ≠ [] →
      Relation.RelatesInSteps takeFirstBlockComputer.TransitionRelation
        ⟨some .rewindBlock, splitTape done rest⟩
        ⟨some .rewindBlock, BiTape.mk₁ (done ++ rest)⟩ done.length := by
  intro done
  induction done using List.reverseRecOn with
  | nil => intro rest _; simp only [List.nil_append, splitTape_nil_left, List.length_nil]
           exact Relation.RelatesInSteps.refl _
  | append_singleton D d ih =>
    intro rest hrest
    obtain ⟨e, rest', rfl⟩ := List.exists_cons_of_ne_nil hrest
    have hstep := tfb_rewindBlock_step D d e rest'
    have hIH := ih (d :: e :: rest') (by simp)
    rw [List.length_append, List.length_singleton,
      show (D ++ [d]) ++ (e :: rest') = D ++ (d :: e :: rest') by simp]
    exact Relation.RelatesInSteps.head _ _ _ _ hstep hIH

/-- Final leftward step: step off the block onto the blank to its left. -/
private lemma tfb_rewindBlock_mk1 (block : List Bool) (hb : block ≠ []) :
    takeFirstBlockComputer.TransitionRelation ⟨some .rewindBlock, BiTape.mk₁ block⟩
      ⟨some .rewindBlock, ⟨none, ∅, StackTape.mapSome block⟩⟩ := by
  obtain ⟨e, block', rfl⟩ := List.exists_cons_of_ne_nil hb
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, BiTape.mk₁,
    BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft, empty_head, empty_tail,
    cons_some_mapSome]

/-- Final rightward step onto the first block cell, halting. -/
private lemma tfb_rewindBlock_final (block : List Bool) :
    takeFirstBlockComputer.TransitionRelation
      ⟨some .rewindBlock, ⟨none, ∅, StackTape.mapSome block⟩⟩ ⟨none, BiTape.mk₁ block⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveRight, mapSome_head, mapSome_tail, cons_none_empty,
    mk₁_eq]

/-- The full rewind: from the start of the rewind, reach the halting configuration on `block`. -/
private lemma tfb_rewind (n : ℕ) (block : List Bool) (hb : block ≠ []) :
    Relation.RelatesWithinSteps takeFirstBlockComputer.TransitionRelation
      ⟨some .rewindSkipQ, rewindTape n block⟩ ⟨none, BiTape.mk₁ block⟩ (n + block.length + 3) := by
  obtain ⟨block', c, rfl⟩ := (List.eq_nil_or_concat block).resolve_left hb
  rw [List.concat_eq_append]
  have h1 := Relation.RelatesWithinSteps.of_relatesInSteps
    (tfb_rewindSkipQ_phase n (block' ++ [c]))
  have h2 := Relation.RelatesWithinSteps.single (tfb_rewindSkipQ_last block' c)
  have h3 := Relation.RelatesWithinSteps.single (tfb_rewindSkipQ_to_block block' c)
  have h4 := Relation.RelatesWithinSteps.of_relatesInSteps
    (tfb_rewindBlock_phase block' [c] (by simp))
  have h5 := Relation.RelatesWithinSteps.single (tfb_rewindBlock_mk1 (block' ++ [c]) (by simp))
  have h6 := Relation.RelatesWithinSteps.single (tfb_rewindBlock_final (block' ++ [c]))
  have := (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6)))))
  refine this.of_le ?_
  simp only [List.length_append, List.length_singleton]
  omega

/-! ### Scan phase -/

private lemma eraseTape_zero (block suffix : List Bool) :
    eraseTape 0 block suffix = splitTape block suffix := rfl

private lemma splitTape_nil_eq_rewind (done : List Bool) :
    splitTape done [] = rewindTape 0 done := rfl

open Relation in
/-- The scan/erase phase: from the `scanTF` state, scan the leading block of `rest`, erase whatever
follows, and end poised to rewind the block `done ++ takeFirstBlock rest`. -/
private lemma tfb_scan_loop : ∀ (n : ℕ) (rest done : List Bool), rest.length = n →
    RelatesWithinSteps takeFirstBlockComputer.TransitionRelation
      ⟨some .scanTF, splitTape done rest⟩
      ⟨some .rewindSkipQ,
        rewindTape (rest.length - (takeFirstBlock rest).length) (done ++ takeFirstBlock rest)⟩
      (2 * rest.length + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro rest done hlen
    match rest with
    | [] =>
      simp only [takeFirstBlock, List.length_nil, Nat.sub_zero, List.append_nil, Nat.mul_zero,
        Nat.zero_add]
      exact RelatesWithinSteps.single (tfb_scanTF_nil done)
    | false :: rest' =>
      have hs := RelatesWithinSteps.single (tfb_scanTF_false done rest')
      have he := RelatesWithinSteps.of_relatesInSteps
        (tfb_erase_phase (done ++ [false]) rest' 0)
      have hn := RelatesWithinSteps.single (tfb_eraseQ_nil rest'.length (done ++ [false]))
      rw [eraseTape_zero, Nat.zero_add, eraseTape_nil] at he
      have hchain := hs.trans (he.trans hn)
      simp only [takeFirstBlock, List.length_cons]
      refine hchain.of_le ?_
      omega
    | true :: [] =>
      have h1 := RelatesWithinSteps.single (tfb_scanTF_true done [])
      have h2 := RelatesWithinSteps.single (tfb_scanB_nil (done ++ [true]))
      have hchain := h1.trans h2
      simp only [takeFirstBlock, List.length_cons, List.length_nil, Nat.sub_self]
      refine hchain.of_le ?_
      omega
    | true :: b :: rest'' =>
      have h1 := RelatesWithinSteps.single (tfb_scanTF_true done (b :: rest''))
      have h2 := RelatesWithinSteps.single (tfb_scanB_step (done ++ [true]) b rest'')
      have h3 := ih rest''.length (by simp only [List.length_cons] at hlen; omega)
        rest'' (done ++ [true] ++ [b]) rfl
      have hchain := h1.trans (h2.trans h3)
      simp only [takeFirstBlock, List.length_cons, List.append_assoc, List.singleton_append,
        Nat.add_sub_add_right] at hchain ⊢
      refine hchain.of_le ?_
      omega

private lemma tfb_scanStart_nil :
    takeFirstBlockComputer.TransitionRelation ⟨some .scanStart, BiTape.mk₁ []⟩
      ⟨none, BiTape.mk₁ []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, takeFirstBlockComputer, mk₁_eq, List.head?_nil,
    List.tail_nil, mapSome_nil, BiTape.write, BiTape.optionMove]

private lemma takeFirstBlock_ne_nil : ∀ {a : List Bool}, a ≠ [] → takeFirstBlock a ≠ [] := by
  intro a ha
  match a with
  | [] => exact absurd rfl ha
  | false :: _ => simp [takeFirstBlock]
  | true :: [] => simp [takeFirstBlock]
  | true :: _ :: _ => simp [takeFirstBlock]

private lemma takeFirstBlock_length_le : ∀ (n : ℕ) (a : List Bool), a.length = n →
    (takeFirstBlock a).length ≤ a.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hlen
    match a with
    | [] => simp [takeFirstBlock]
    | false :: rest => simp [takeFirstBlock]
    | true :: [] => simp [takeFirstBlock]
    | true :: b :: rest'' =>
      have := ih rest''.length (by simp only [List.length_cons] at hlen; omega) rest'' rfl
      simp only [takeFirstBlock, List.length_cons]
      omega

open Relation in
/-- The scan/erase phase from the initial state (differing from `scanTF` only on empty input). -/
private lemma tfb_scan_start : ∀ (input : List Bool), input ≠ [] →
    RelatesWithinSteps takeFirstBlockComputer.TransitionRelation
      ⟨some .scanStart, BiTape.mk₁ input⟩
      ⟨some .rewindSkipQ,
        rewindTape (input.length - (takeFirstBlock input).length) (takeFirstBlock input)⟩
      (2 * input.length + 1) := by
  intro input hne
  match input with
  | [] => exact absurd rfl hne
  | false :: rest =>
    have hs := RelatesWithinSteps.single (tfb_scanStart_false rest)
    have he := RelatesWithinSteps.of_relatesInSteps (tfb_erase_phase [false] rest 0)
    have hn := RelatesWithinSteps.single (tfb_eraseQ_nil rest.length [false])
    rw [eraseTape_zero, Nat.zero_add, eraseTape_nil] at he
    have hchain := hs.trans (he.trans hn)
    simp only [takeFirstBlock, List.length_cons]
    refine hchain.of_le ?_
    omega
  | true :: [] =>
    have hchain := (RelatesWithinSteps.single (tfb_scanStart_true [])).trans
      (RelatesWithinSteps.single (tfb_scanB_nil [true]))
    simp only [takeFirstBlock, List.length_cons, List.length_nil, Nat.sub_self]
    refine hchain.of_le ?_
    omega
  | true :: b :: rest' =>
    have h3 := tfb_scan_loop rest'.length rest' ([true] ++ [b]) rfl
    have hchain := (RelatesWithinSteps.single (tfb_scanStart_true (b :: rest'))).trans
      ((RelatesWithinSteps.single (tfb_scanB_step [true] b rest')).trans h3)
    simp only [takeFirstBlock, List.length_cons, List.singleton_append,
      Nat.add_sub_add_right] at hchain ⊢
    refine hchain.of_le ?_
    omega

open Relation Polynomial in
/-- The machine keeping the leading self-delimiting block: scan to the end of the first block, erase
the suffix, and rewind. No compaction is involved. -/
theorem PolyTimeComputable_takeFirstBlock :
    Nonempty (Cslib.Turing.SingleTapeTM.PolyTimeComputable takeFirstBlock) :=
  ⟨{ tm := takeFirstBlockComputer
     timeBound := fun n => 3 * n + 4
     poly := C 3 * X + C 4
     bounds := fun n => by simp only [eval_add, eval_mul, eval_C, eval_X]; omega
     outputsFunInTime := fun a => by
       simp only [OutputsWithinTime, initCfg, haltCfg]
       rcases eq_or_ne a [] with rfl | hne
       · exact (RelatesWithinSteps.single tfb_scanStart_nil).of_le (by simp)
       · have hblock : takeFirstBlock a ≠ [] := takeFirstBlock_ne_nil hne
         have hlen : (takeFirstBlock a).length ≤ a.length :=
           takeFirstBlock_length_le a.length a rfl
         have h1 := tfb_scan_start a hne
         have h2 := tfb_rewind (a.length - (takeFirstBlock a).length) (takeFirstBlock a) hblock
         refine (h1.trans h2).of_le ?_
         omega } ⟩

end TakeFirstBlockMachine

section UndelimitBlockMachine

open Cslib.Turing Cslib.Turing.SingleTapeTM

/-- States of the `undelimitBlock` machine. The machine works in two phases.

**Normalization** (`norm*` states): a left-to-right scan through the pair structure that rewrites
the input into an equivalent *well-formed* block `true b₁ … true bₖ false` with nothing after it —
appending the missing `false` terminator if the input ends mid-structure, turning a lone trailing
`true` into the terminator, and erasing any garbage after the terminator — then rewinds to the
start. During this scan the unread input is a contiguous run of non-blank cells, so the end of the
input is detectable as the first blank.

**Shuttle** (remaining states): builds the output (payload bits) at the front of the tape; a
growing region of blanks separates the finished output from the input still to be scanned, and the
head shuttles across this gap to carry each payload bit to the output frontier. The shuttle relies
on normalization: while seeking rightward across the gap it cannot tell gap blanks from the blanks
past the end of the input, so it only halts because a `false` terminator is guaranteed to be
present (and it leaves no garbage behind only because normalization already erased it). -/
inductive UBState
  /-- Normalizing: expecting `true` (pair marker) or `false` (terminator); on a blank the input
  ended mid-structure, so write the missing terminator and rewind. -/
  | normTF
  /-- Normalizing: expecting the payload bit after a `true`; a blank here means a lone trailing
  `true`, which is removed by turning it into the terminator. -/
  | normB
  /-- On the lone trailing `true`: overwrite it with the terminator `false`. -/
  | normFixLone
  /-- Erasing everything after the terminator. -/
  | normErase
  /-- Rewinding leftward over the blanks left by `normErase`. -/
  | normRewindSkip
  /-- Rewinding leftward through the normalized block; on the blank left of it, step right and
  start the shuttle. -/
  | normRewind
  /-- Shuttle start: at the first `true` of the first block cell pair (special-cased: the output
  is still empty). -/
  | initTrue
  /-- At the first payload bit (to be placed at the very front). -/
  | initBit
  /-- Depositing the carried bit `b` at the output frontier. -/
  | deposit (b : Bool)
  /-- Seeking rightward across the gap to the next input cell. -/
  | seekInput
  /-- Just consumed a `true`; at the payload bit to grab. -/
  | grabBit
  /-- Carrying payload bit `b` leftward across the gap to the frontier. -/
  | carry (b : Bool)
  /-- Erasing the rest of the input (used when the block is empty, i.e. starts with `false`). -/
  | eraseAll
  /-- Rewinding leftward, skipping the gap blanks. -/
  | rewindSkip
  /-- Rewinding leftward through the finished output block. -/
  | rewindBlock
  deriving DecidableEq, Fintype

/-- The machine stripping a single block's framing: it first normalizes the input to a well-formed
terminated block (see `UBState`), then compacts the payload bits to the front of the tape, a
quadratic-time single-tape shuttle. -/
def undelimitBlockComputer : SingleTapeTM Bool where
  State := UBState
  q₀ := .normTF
  tr q sym :=
    match q, sym with
    -- Phase 1: normalize the input to a well-formed block with nothing after it.
    | .normTF, some true => (⟨some true, some .right⟩, some .normB)   -- keep pair marker
    | .normTF, some false => (⟨some false, some .right⟩, some .normErase) -- keep terminator
    | .normTF, none => (⟨some false, none⟩, some .normRewind)        -- write missing terminator
    | .normB, some b => (⟨some b, some .right⟩, some .normTF)        -- keep payload bit
    | .normB, none => (⟨none, some .left⟩, some .normFixLone)        -- lone trailing `true`
    | .normFixLone, some _ => (⟨some false, none⟩, some .normRewind) -- lone `true` → terminator
    | .normFixLone, none => (⟨none, none⟩, none)                     -- unreachable
    | .normErase, some _ => (⟨none, some .right⟩, some .normErase)   -- erase garbage
    | .normErase, none => (⟨none, none⟩, some .normRewindSkip)       -- garbage done: rewind
    | .normRewindSkip, none => (⟨none, some .left⟩, some .normRewindSkip)
    | .normRewindSkip, some b => (⟨some b, none⟩, some .normRewind)  -- found the block's end
    | .normRewind, some b => (⟨some b, some .left⟩, some .normRewind)
    | .normRewind, none => (⟨none, some .right⟩, some .initTrue)     -- at the start: shuttle
    -- Phase 2: shuttle the payload bits to the front of the tape.
    | .initTrue, none => (⟨none, none⟩, none)                        -- empty input
    | .initTrue, some true => (⟨none, some .right⟩, some .initBit)   -- erase the first `true`
    | .initTrue, some false => (⟨none, some .right⟩, some .eraseAll) -- empty block: erase all
    | .initBit, none => (⟨none, none⟩, none)                         -- unreachable (normalized)
    | .initBit, some b => (⟨none, some .left⟩, some (.deposit b))    -- grab first bit, go to front
    | .deposit b, _ => (⟨some b, some .right⟩, some .seekInput)      -- write bit, advance to gap
    | .seekInput, none => (⟨none, some .right⟩, some .seekInput)     -- skip a gap blank
    | .seekInput, some true => (⟨none, some .right⟩, some .grabBit)  -- erase a `true`
    | .seekInput, some false => (⟨none, none⟩, some .rewindSkip)     -- terminator: finish
    | .grabBit, none => (⟨none, none⟩, some .rewindSkip)             -- unreachable (normalized)
    | .grabBit, some b => (⟨none, some .left⟩, some (.carry b))      -- grab bit, carry left
    | .carry b, none => (⟨none, some .left⟩, some (.carry b))        -- skip a gap blank
    | .carry b, some c => (⟨some c, some .right⟩, some (.deposit b)) -- reached output frontier
    | .eraseAll, none => (⟨none, none⟩, none)                        -- done erasing
    | .eraseAll, some _ => (⟨none, some .right⟩, some .eraseAll)     -- erase a cell
    | .rewindSkip, none => (⟨none, some .left⟩, some .rewindSkip)
    | .rewindSkip, some b => (⟨some b, none⟩, some .rewindBlock)
    | .rewindBlock, some b => (⟨some b, some .left⟩, some .rewindBlock)
    | .rewindBlock, none => (⟨none, some .right⟩, none)

/-! #### Facts about `undelimitBlock` and `delimit` -/

private lemma undelimitBlock_length_le : ∀ (n : ℕ) (a : List Bool), a.length = n →
    2 * (undelimitBlock a).length ≤ a.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hlen
    match a with
    | [] => simp [undelimitBlock]
    | false :: rest => simp [undelimitBlock]
    | true :: [] => simp [undelimitBlock]
    | true :: b :: rest'' =>
      have := ih rest''.length (by simp only [List.length_cons] at hlen; omega) rest'' rfl
      simp only [undelimitBlock, List.length_cons]
      omega

private lemma delimit_nil : BitstringEncoding.delimit [] = [false] := rfl

private lemma delimit_cons (b : Bool) (l : List Bool) :
    BitstringEncoding.delimit (b :: l) = true :: b :: BitstringEncoding.delimit l := rfl

private lemma delimit_undelimitBlock_nil :
    BitstringEncoding.delimit (undelimitBlock []) = [false] := rfl

private lemma delimit_undelimitBlock_false (rest : List Bool) :
    BitstringEncoding.delimit (undelimitBlock (false :: rest)) = [false] := rfl

private lemma delimit_undelimitBlock_singleton :
    BitstringEncoding.delimit (undelimitBlock [true]) = [false] := rfl

private lemma delimit_undelimitBlock_cons (b : Bool) (rest : List Bool) :
    BitstringEncoding.delimit (undelimitBlock (true :: b :: rest))
      = true :: b :: BitstringEncoding.delimit (undelimitBlock rest) := rfl

/-! #### Normalization phase: single steps

The scan steps mirror the `takeFirstBlock` machine's scan exactly (the same `splitTape`
configurations), with different endings: reaching the end of the input mid-structure writes the
missing terminator in place. -/

private lemma nm_scanTF_true (done rest : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .normTF, splitTape done (true :: rest)⟩
      ⟨some .normB, splitTape (done ++ [true]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma nm_scanTF_false (done rest : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .normTF, splitTape done (false :: rest)⟩
      ⟨some .normErase, splitTape (done ++ [false]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma nm_scanB_step (done : List Bool) (b : Bool) (rest : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .normB, splitTape done (b :: rest)⟩
      ⟨some .normTF, splitTape (done ++ [b]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, splitTape_head_cons,
    splitTape_scan]

/-- End of input while expecting a pair marker: write the missing terminator in place. -/
private lemma nm_scanTF_nil (done : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .normTF, splitTape done []⟩
      ⟨some .normRewind, splitTape done [false]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, splitTape,
    List.head?_nil, List.tail_nil, List.head?_cons, List.tail_cons, mapSome_nil, BiTape.write,
    BiTape.optionMove]

/-- End of input just after a pair marker (a lone trailing `true`): step back onto it. -/
private lemma nm_scanB_nil (done : List Bool) (c : Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .normB, splitTape (done ++ [c]) []⟩
      ⟨some .normFixLone, splitTape done [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, splitTape,
    List.head?_nil, List.tail_nil, List.head?_cons, List.tail_cons, BiTape.write, BiTape.optionMove,
    BiTape.move, BiTape.moveLeft, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, mapSome_head, mapSome_tail, mapSome_nil,
    cons_none_empty]

/-- Overwrite the lone trailing `true` with the terminator. -/
private lemma nm_fixLone (done : List Bool) (c : Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .normFixLone, splitTape done [c]⟩
      ⟨some .normRewind, splitTape done [false]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, splitTape,
    List.head?_cons, List.tail_cons, BiTape.write, BiTape.optionMove, mapSome_nil]

/-! #### Normalization phase: erasing the garbage after the terminator -/

private lemma nm_erase_step (n : ℕ) (block : List Bool) (s : Bool) (suffix : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .normErase, eraseTape n block (s :: suffix)⟩
      ⟨some .normErase, eraseTape (n + 1) block suffix⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, eraseTape,
    List.head?_cons, List.tail_cons, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight,
    mapSome_head, mapSome_tail, blanksLeft_succ]

private lemma nm_erase_phase (block suffix : List Bool) (n : ℕ) :
    Relation.RelatesInSteps undelimitBlockComputer.TransitionRelation
      ⟨some .normErase, eraseTape n block suffix⟩
      ⟨some .normErase, eraseTape (n + suffix.length) block []⟩ suffix.length := by
  induction suffix generalizing n with
  | nil => simp only [List.length_nil, Nat.add_zero]; exact Relation.RelatesInSteps.refl _
  | cons s suffix ih =>
    have hstep := nm_erase_step n block s suffix
    have hrest := ih (n + 1)
    rw [show n + (s :: suffix).length = (n + 1) + suffix.length by simp; omega]
    exact Relation.RelatesInSteps.head _ _ _ _ hstep hrest

private lemma nm_erase_nil (n : ℕ) (block : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .normErase, rewindTape n block⟩
      ⟨some .normRewindSkip, rewindTape n block⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, rewindTape,
    BiTape.write, BiTape.optionMove]

/-! #### Normalization phase: rewinding to the start (mirrors the `takeFirstBlock` rewind, but
hands off to the shuttle's `initTrue` state instead of halting) -/

private lemma nm_rewindSkip_step (n : ℕ) (block : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .normRewindSkip, rewindTape (n + 1) block⟩
      ⟨some .normRewindSkip, rewindTape n block⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, rewindTape,
    blanksLeft_succ, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft,
    StackTape.head_cons, StackTape.tail_cons, cons_none_empty]

private lemma nm_rewindSkip_phase (n : ℕ) (block : List Bool) :
    Relation.RelatesInSteps undelimitBlockComputer.TransitionRelation
      ⟨some .normRewindSkip, rewindTape n block⟩ ⟨some .normRewindSkip, rewindTape 0 block⟩ n := by
  induction n with
  | zero => exact Relation.RelatesInSteps.refl _
  | succ n ih =>
    exact Relation.RelatesInSteps.head _ _ _ _ (nm_rewindSkip_step n block) ih

private lemma nm_rewindSkip_last (block' : List Bool) (c : Bool) :
    undelimitBlockComputer.TransitionRelation
      ⟨some .normRewindSkip, rewindTape 0 (block' ++ [c])⟩
      ⟨some .normRewindSkip, splitTape block' [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, rewindTape, blanksLeft,
    Function.iterate_zero, id_eq, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveLeft, mapSome_head, mapSome_tail, List.head?_cons, List.tail_cons, cons_none_empty,
    mapSome_nil, splitTape]

private lemma nm_rewindSkip_to_block (block' : List Bool) (c : Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .normRewindSkip, splitTape block' [c]⟩
      ⟨some .normRewind, splitTape block' [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, splitTape_head_cons,
    splitTape_write_head, BiTape.optionMove]

private lemma nm_rewindBlock_step (D : List Bool) (d e : Bool) (rest : List Bool) :
    undelimitBlockComputer.TransitionRelation
      ⟨some .normRewind, splitTape (D ++ [d]) (e :: rest)⟩
      ⟨some .normRewind, splitTape D (d :: e :: rest)⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, splitTape_head_cons,
    splitTape_write_head, splitTape_rewind]

private lemma nm_rewindBlock_phase :
    ∀ (done rest : List Bool), rest ≠ [] →
      Relation.RelatesInSteps undelimitBlockComputer.TransitionRelation
        ⟨some .normRewind, splitTape done rest⟩
        ⟨some .normRewind, BiTape.mk₁ (done ++ rest)⟩ done.length := by
  intro done
  induction done using List.reverseRecOn with
  | nil => intro rest _; simp only [List.nil_append, splitTape_nil_left, List.length_nil]
           exact Relation.RelatesInSteps.refl _
  | append_singleton D d ih =>
    intro rest hrest
    obtain ⟨e, rest', rfl⟩ := List.exists_cons_of_ne_nil hrest
    have hstep := nm_rewindBlock_step D d e rest'
    have hIH := ih (d :: e :: rest') (by simp)
    rw [List.length_append, List.length_singleton,
      show (D ++ [d]) ++ (e :: rest') = D ++ (d :: e :: rest') by simp]
    exact Relation.RelatesInSteps.head _ _ _ _ hstep hIH

private lemma nm_rewind_mk1 (block : List Bool) (hb : block ≠ []) :
    undelimitBlockComputer.TransitionRelation ⟨some .normRewind, BiTape.mk₁ block⟩
      ⟨some .normRewind, ⟨none, ∅, StackTape.mapSome block⟩⟩ := by
  obtain ⟨e, block', rfl⟩ := List.exists_cons_of_ne_nil hb
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, BiTape.mk₁,
    BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft, empty_head, empty_tail,
    cons_some_mapSome]

/-- The final rightward step onto the first block cell, entering the shuttle phase. -/
private lemma nm_rewind_final (block : List Bool) :
    undelimitBlockComputer.TransitionRelation
      ⟨some .normRewind, ⟨none, ∅, StackTape.mapSome block⟩⟩
      ⟨some .initTrue, BiTape.mk₁ block⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveRight, mapSome_head, mapSome_tail, cons_none_empty,
    mk₁_eq]

/-- The full rewind from the skip state: reach the start of the block in state `initTrue`. -/
private lemma nm_rewind (n : ℕ) (block : List Bool) (hb : block ≠ []) :
    Relation.RelatesWithinSteps undelimitBlockComputer.TransitionRelation
      ⟨some .normRewindSkip, rewindTape n block⟩ ⟨some .initTrue, BiTape.mk₁ block⟩
      (n + block.length + 3) := by
  obtain ⟨block', c, rfl⟩ := (List.eq_nil_or_concat block).resolve_left hb
  rw [List.concat_eq_append]
  have h1 := Relation.RelatesWithinSteps.of_relatesInSteps
    (nm_rewindSkip_phase n (block' ++ [c]))
  have h2 := Relation.RelatesWithinSteps.single (nm_rewindSkip_last block' c)
  have h3 := Relation.RelatesWithinSteps.single (nm_rewindSkip_to_block block' c)
  have h4 := Relation.RelatesWithinSteps.of_relatesInSteps
    (nm_rewindBlock_phase block' [c] (by simp))
  have h5 := Relation.RelatesWithinSteps.single (nm_rewind_mk1 (block' ++ [c]) (by simp))
  have h6 := Relation.RelatesWithinSteps.single (nm_rewind_final (block' ++ [c]))
  have := h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
  refine this.of_le ?_
  simp only [List.length_append, List.length_singleton]
  omega

/-- Rewind starting on the last cell of the block itself (no erased blanks to skip). -/
private lemma nm_rewind_from_block (done : List Bool) :
    Relation.RelatesWithinSteps undelimitBlockComputer.TransitionRelation
      ⟨some .normRewind, splitTape done [false]⟩
      ⟨some .initTrue, BiTape.mk₁ (done ++ [false])⟩ (done.length + 2) := by
  have h4 := Relation.RelatesWithinSteps.of_relatesInSteps
    (nm_rewindBlock_phase done [false] (by simp))
  have h5 := Relation.RelatesWithinSteps.single (nm_rewind_mk1 (done ++ [false]) (by simp))
  have h6 := Relation.RelatesWithinSteps.single (nm_rewind_final (done ++ [false]))
  exact (h4.trans (h5.trans h6)).of_le (by omega)

/-! #### Normalization phase: the full scan -/

open Relation in
/-- The normalization scan: from `normTF`, scanning the pair structure of `rest` (with `done`
already scanned), the machine reaches the shuttle start on the well-formed block
`done ++ delimit (undelimitBlock rest)`. -/
private lemma nm_scan_loop : ∀ (n : ℕ) (rest done : List Bool), rest.length = n →
    RelatesWithinSteps undelimitBlockComputer.TransitionRelation
      ⟨some .normTF, splitTape done rest⟩
      ⟨some .initTrue,
        BiTape.mk₁ (done ++ BitstringEncoding.delimit (undelimitBlock rest))⟩
      (2 * rest.length + done.length + 6) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro rest done hlen
    match rest with
    | [] =>
      rw [delimit_undelimitBlock_nil]
      have hchain := (RelatesWithinSteps.single (nm_scanTF_nil done)).trans
        (nm_rewind_from_block done)
      refine hchain.of_le ?_
      simp only [List.length_nil]
      omega
    | false :: rest' =>
      rw [delimit_undelimitBlock_false]
      have hs := RelatesWithinSteps.single (nm_scanTF_false done rest')
      have he := RelatesWithinSteps.of_relatesInSteps
        (nm_erase_phase (done ++ [false]) rest' 0)
      rw [eraseTape_zero, Nat.zero_add, eraseTape_nil] at he
      have hn := RelatesWithinSteps.single (nm_erase_nil rest'.length (done ++ [false]))
      have hr := nm_rewind rest'.length (done ++ [false]) (by simp)
      have hchain := hs.trans (he.trans (hn.trans hr))
      refine hchain.of_le ?_
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega
    | true :: [] =>
      rw [delimit_undelimitBlock_singleton]
      have hchain := (RelatesWithinSteps.single (nm_scanTF_true done [])).trans
        ((RelatesWithinSteps.single (nm_scanB_nil done true)).trans
          ((RelatesWithinSteps.single (nm_fixLone done true)).trans
            (nm_rewind_from_block done)))
      refine hchain.of_le ?_
      simp only [List.length_cons, List.length_nil]
      omega
    | true :: b :: rest'' =>
      rw [delimit_undelimitBlock_cons]
      have h1 := RelatesWithinSteps.single (nm_scanTF_true done (b :: rest''))
      have h2 := RelatesWithinSteps.single (nm_scanB_step (done ++ [true]) b rest'')
      have h3 := ih rest''.length (by simp only [List.length_cons] at hlen; omega)
        rest'' (done ++ [true] ++ [b]) rfl
      have hchain := h1.trans (h2.trans h3)
      rw [show done ++ [true] ++ [b] ++ BitstringEncoding.delimit (undelimitBlock rest'')
        = done ++ true :: b :: BitstringEncoding.delimit (undelimitBlock rest'') by simp]
        at hchain
      refine hchain.of_le ?_
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega

/-- The normalization phase: on any input `a`, reach the shuttle start with the tape holding the
well-formed block `delimit (undelimitBlock a)`. -/
private lemma nm_phase (a : List Bool) :
    Relation.RelatesWithinSteps undelimitBlockComputer.TransitionRelation
      ⟨some .normTF, BiTape.mk₁ a⟩
      ⟨some .initTrue, BiTape.mk₁ (BitstringEncoding.delimit (undelimitBlock a))⟩
      (2 * a.length + 6) := by
  have h := nm_scan_loop a.length a [] rfl
  rw [splitTape_nil_left, List.nil_append, List.length_nil, Nat.add_zero] at h
  exact h

/-! #### Shuttle phase: tape configurations -/

/-- The right half of the tape during the shuttle: the unconsumed input `rem` buried under `k`
blanks (part of the gap). -/
private def blanksRight (k : ℕ) (rem : List Bool) : StackTape Bool :=
  (StackTape.cons none)^[k] (StackTape.mapSome rem)

private lemma blanksRight_succ (k : ℕ) (rem : List Bool) :
    blanksRight (k + 1) rem = StackTape.cons none (blanksRight k rem) := by
  simp only [blanksRight, Function.iterate_succ_apply']

private lemma blanksRight_zero (rem : List Bool) :
    blanksRight 0 rem = StackTape.mapSome rem := rfl

/-- Tape while shuttling with the head on a gap blank: `i` blanks (then the output `out`) to the
left, `k` blanks (then the unconsumed input `rem`) to the right. -/
private def shuttleTape (i k : ℕ) (out rem : List Bool) : BiTape Bool :=
  ⟨none, blanksLeft i out, blanksRight k rem⟩

/-- Tape with the head on the first cell of the unconsumed input `rem`, the whole gap of `g`
blanks (then the output `out`) to the left. -/
private def inputEdgeTape (g : ℕ) (out rem : List Bool) : BiTape Bool :=
  ⟨rem.head?, blanksLeft g out, StackTape.mapSome rem.tail⟩

/-! #### Shuttle phase: single steps -/

private lemma ub_seek_blank (i k : ℕ) (out rem : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .seekInput, shuttleTape i (k + 1) out rem⟩
      ⟨some .seekInput, shuttleTape (i + 1) k out rem⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, shuttleTape,
    blanksRight_succ, blanksLeft_succ, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveRight, StackTape.head_cons, StackTape.tail_cons]

private lemma ub_seek_onto (i : ℕ) (out rem : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .seekInput, shuttleTape i 0 out rem⟩
      ⟨some .seekInput, inputEdgeTape (i + 1) out rem⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, shuttleTape,
    inputEdgeTape, blanksRight_zero, blanksLeft_succ, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveRight, mapSome_head, mapSome_tail]

open Relation in
/-- Seeking rightward across the whole gap, ending on the first cell of the unconsumed input. -/
private lemma ub_seek_phase (k : ℕ) : ∀ (i : ℕ) (out rem : List Bool),
    RelatesInSteps undelimitBlockComputer.TransitionRelation
      ⟨some .seekInput, shuttleTape i k out rem⟩
      ⟨some .seekInput, inputEdgeTape (i + k + 1) out rem⟩ (k + 1) := by
  induction k with
  | zero =>
    intro i out rem
    rw [Nat.add_zero]
    exact RelatesInSteps.single (ub_seek_onto i out rem)
  | succ k ihk =>
    intro i out rem
    have h1 := ub_seek_blank i k out rem
    have h2 := ihk (i + 1) out rem
    rw [show i + 1 + k + 1 = i + (k + 1) + 1 by omega] at h2
    exact RelatesInSteps.head _ _ _ _ h1 h2

private lemma ub_seek_true (g : ℕ) (out : List Bool) (b : Bool) (rest : List Bool) :
    undelimitBlockComputer.TransitionRelation
      ⟨some .seekInput, inputEdgeTape g out (true :: b :: rest)⟩
      ⟨some .grabBit, inputEdgeTape (g + 1) out (b :: rest)⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, inputEdgeTape,
    List.head?_cons, List.tail_cons, blanksLeft_succ, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveRight, mapSome_head, mapSome_tail]

private lemma ub_grab (g : ℕ) (out : List Bool) (b : Bool) (rest : List Bool) :
    undelimitBlockComputer.TransitionRelation
      ⟨some .grabBit, inputEdgeTape (g + 1) out (b :: rest)⟩
      ⟨some (.carry b), shuttleTape g 1 out rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, inputEdgeTape,
    shuttleTape, List.head?_cons, List.tail_cons, blanksLeft_succ, blanksRight_succ,
    blanksRight_zero, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft,
    StackTape.head_cons, StackTape.tail_cons]

private lemma ub_carry_blank (b : Bool) (i k : ℕ) (out rem : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some (.carry b), shuttleTape (i + 1) k out rem⟩
      ⟨some (.carry b), shuttleTape i (k + 1) out rem⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, shuttleTape,
    blanksLeft_succ, blanksRight_succ, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveLeft, StackTape.head_cons, StackTape.tail_cons]

open Relation in
/-- Carrying the grabbed bit leftward across the gap to the output frontier. -/
private lemma ub_carry_phase (i : ℕ) : ∀ (k : ℕ) (b : Bool) (out rem : List Bool),
    RelatesInSteps undelimitBlockComputer.TransitionRelation
      ⟨some (.carry b), shuttleTape i k out rem⟩
      ⟨some (.carry b), shuttleTape 0 (i + k) out rem⟩ i := by
  induction i with
  | zero =>
    intro k b out rem
    rw [Nat.zero_add]
    exact RelatesInSteps.refl _
  | succ i ihi =>
    intro k b out rem
    have h1 := ub_carry_blank b i k out rem
    have h2 := ihi (k + 1) b out rem
    rw [show i + (k + 1) = i + 1 + k by omega] at h2
    exact RelatesInSteps.head _ _ _ _ h1 h2

private lemma ub_carry_edge (b : Bool) (k : ℕ) (out' : List Bool) (c : Bool) (rem : List Bool) :
    undelimitBlockComputer.TransitionRelation
      ⟨some (.carry b), shuttleTape 0 k (out' ++ [c]) rem⟩
      ⟨some (.carry b), ⟨some c, StackTape.mapSome out'.reverse, blanksRight (k + 1) rem⟩⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, shuttleTape,
    blanksLeft, Function.iterate_zero, id_eq, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, blanksRight_succ, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveLeft, mapSome_head, mapSome_tail, List.head?_cons,
    List.tail_cons]

private lemma ub_carry_deposit (b : Bool) (k : ℕ) (out' : List Bool) (c : Bool)
    (rem : List Bool) :
    undelimitBlockComputer.TransitionRelation
      ⟨some (.carry b), ⟨some c, StackTape.mapSome out'.reverse, blanksRight (k + 1) rem⟩⟩
      ⟨some (.deposit b), shuttleTape 0 k (out' ++ [c]) rem⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, shuttleTape,
    blanksLeft, Function.iterate_zero, id_eq, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, blanksRight_succ, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveRight, StackTape.head_cons, StackTape.tail_cons,
    cons_some_mapSome]

/-- Turning around at the output frontier: one step onto the last output bit, one step back. -/
private lemma ub_carry_turn (b : Bool) (k : ℕ) (out rem : List Bool) (hout : out ≠ []) :
    Relation.RelatesWithinSteps undelimitBlockComputer.TransitionRelation
      ⟨some (.carry b), shuttleTape 0 k out rem⟩
      ⟨some (.deposit b), shuttleTape 0 k out rem⟩ 2 := by
  obtain ⟨out', c, rfl⟩ := (List.eq_nil_or_concat out).resolve_left hout
  rw [List.concat_eq_append]
  exact (Relation.RelatesWithinSteps.single (ub_carry_edge b k out' c rem)).trans
    (Relation.RelatesWithinSteps.single (ub_carry_deposit b k out' c rem))

private lemma ub_deposit (b : Bool) (k : ℕ) (out rem : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some (.deposit b), shuttleTape 0 (k + 1) out rem⟩
      ⟨some .seekInput, shuttleTape 0 k (out ++ [b]) rem⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, shuttleTape,
    blanksLeft, Function.iterate_zero, id_eq, blanksRight_succ, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveRight, StackTape.head_cons, StackTape.tail_cons,
    cons_some_mapSome]

/-! #### Shuttle phase: entry and exit steps -/

private lemma ub_init_true (p : Bool) (rest : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .initTrue, BiTape.mk₁ (true :: p :: rest)⟩
      ⟨some .initBit, BiTape.mk₁ (p :: rest)⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, BiTape.mk₁,
    BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight, mapSome_head, mapSome_tail,
    List.head?_cons, List.tail_cons, cons_none_empty]

private lemma ub_init_bit (p : Bool) (rest : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .initBit, BiTape.mk₁ (p :: rest)⟩
      ⟨some (.deposit p), shuttleTape 0 1 [] rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, BiTape.mk₁,
    shuttleTape, blanksLeft, blanksRight_succ, blanksRight_zero, Function.iterate_zero, id_eq,
    List.reverse_nil, mapSome_nil, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft,
    empty_head, empty_tail]

private lemma ub_initTrue_false :
    undelimitBlockComputer.TransitionRelation ⟨some .initTrue, BiTape.mk₁ [false]⟩
      ⟨some .eraseAll, BiTape.mk₁ []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, BiTape.mk₁,
    BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight, empty_head, empty_tail,
    cons_none_empty, mapSome_nil, BiTape.empty_eq_nil, BiTape.nil]

private lemma ub_eraseAll_halt :
    undelimitBlockComputer.TransitionRelation ⟨some .eraseAll, BiTape.mk₁ []⟩
      ⟨none, BiTape.mk₁ []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, BiTape.mk₁,
    BiTape.write, BiTape.optionMove, BiTape.empty_eq_nil, BiTape.nil]

/-- Reaching the terminator: erase it and start the final rewind. -/
private lemma ub_seek_false (g : ℕ) (out : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .seekInput, inputEdgeTape g out [false]⟩
      ⟨some .rewindSkip, rewindTape g out⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, inputEdgeTape,
    rewindTape, List.head?_cons, List.tail_cons, mapSome_nil, BiTape.write, BiTape.optionMove]

/-! #### Shuttle phase: the final rewind (mirrors the `takeFirstBlock` rewind) -/

private lemma ub_rewindSkip_step (n : ℕ) (block : List Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .rewindSkip, rewindTape (n + 1) block⟩
      ⟨some .rewindSkip, rewindTape n block⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, rewindTape,
    blanksLeft_succ, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft,
    StackTape.head_cons, StackTape.tail_cons, cons_none_empty]

private lemma ub_rewindSkip_phase (n : ℕ) (block : List Bool) :
    Relation.RelatesInSteps undelimitBlockComputer.TransitionRelation
      ⟨some .rewindSkip, rewindTape n block⟩ ⟨some .rewindSkip, rewindTape 0 block⟩ n := by
  induction n with
  | zero => exact Relation.RelatesInSteps.refl _
  | succ n ih =>
    exact Relation.RelatesInSteps.head _ _ _ _ (ub_rewindSkip_step n block) ih

private lemma ub_rewindSkip_last (block' : List Bool) (c : Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .rewindSkip, rewindTape 0 (block' ++ [c])⟩
      ⟨some .rewindSkip, splitTape block' [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, rewindTape, blanksLeft,
    Function.iterate_zero, id_eq, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveLeft, mapSome_head, mapSome_tail, List.head?_cons, List.tail_cons, cons_none_empty,
    mapSome_nil, splitTape]

private lemma ub_rewindSkip_to_block (block' : List Bool) (c : Bool) :
    undelimitBlockComputer.TransitionRelation ⟨some .rewindSkip, splitTape block' [c]⟩
      ⟨some .rewindBlock, splitTape block' [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, splitTape_head_cons,
    splitTape_write_head, BiTape.optionMove]

private lemma ub_rewindBlock_step (D : List Bool) (d e : Bool) (rest : List Bool) :
    undelimitBlockComputer.TransitionRelation
      ⟨some .rewindBlock, splitTape (D ++ [d]) (e :: rest)⟩
      ⟨some .rewindBlock, splitTape D (d :: e :: rest)⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, splitTape_head_cons,
    splitTape_write_head, splitTape_rewind]

private lemma ub_rewindBlock_phase :
    ∀ (done rest : List Bool), rest ≠ [] →
      Relation.RelatesInSteps undelimitBlockComputer.TransitionRelation
        ⟨some .rewindBlock, splitTape done rest⟩
        ⟨some .rewindBlock, BiTape.mk₁ (done ++ rest)⟩ done.length := by
  intro done
  induction done using List.reverseRecOn with
  | nil => intro rest _; simp only [List.nil_append, splitTape_nil_left, List.length_nil]
           exact Relation.RelatesInSteps.refl _
  | append_singleton D d ih =>
    intro rest hrest
    obtain ⟨e, rest', rfl⟩ := List.exists_cons_of_ne_nil hrest
    have hstep := ub_rewindBlock_step D d e rest'
    have hIH := ih (d :: e :: rest') (by simp)
    rw [List.length_append, List.length_singleton,
      show (D ++ [d]) ++ (e :: rest') = D ++ (d :: e :: rest') by simp]
    exact Relation.RelatesInSteps.head _ _ _ _ hstep hIH

private lemma ub_rewindBlock_mk1 (block : List Bool) (hb : block ≠ []) :
    undelimitBlockComputer.TransitionRelation ⟨some .rewindBlock, BiTape.mk₁ block⟩
      ⟨some .rewindBlock, ⟨none, ∅, StackTape.mapSome block⟩⟩ := by
  obtain ⟨e, block', rfl⟩ := List.exists_cons_of_ne_nil hb
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, BiTape.mk₁,
    BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft, empty_head, empty_tail,
    cons_some_mapSome]

private lemma ub_rewindBlock_final (block : List Bool) :
    undelimitBlockComputer.TransitionRelation
      ⟨some .rewindBlock, ⟨none, ∅, StackTape.mapSome block⟩⟩ ⟨none, BiTape.mk₁ block⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, undelimitBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveRight, mapSome_head, mapSome_tail, cons_none_empty,
    mk₁_eq]

/-- The shuttle's full rewind: from the start of the rewind, reach the halting configuration. -/
private lemma ub_rewind (n : ℕ) (block : List Bool) (hb : block ≠ []) :
    Relation.RelatesWithinSteps undelimitBlockComputer.TransitionRelation
      ⟨some .rewindSkip, rewindTape n block⟩ ⟨none, BiTape.mk₁ block⟩
      (n + block.length + 3) := by
  obtain ⟨block', c, rfl⟩ := (List.eq_nil_or_concat block).resolve_left hb
  rw [List.concat_eq_append]
  have h1 := Relation.RelatesWithinSteps.of_relatesInSteps
    (ub_rewindSkip_phase n (block' ++ [c]))
  have h2 := Relation.RelatesWithinSteps.single (ub_rewindSkip_last block' c)
  have h3 := Relation.RelatesWithinSteps.single (ub_rewindSkip_to_block block' c)
  have h4 := Relation.RelatesWithinSteps.of_relatesInSteps
    (ub_rewindBlock_phase block' [c] (by simp))
  have h5 := Relation.RelatesWithinSteps.single (ub_rewindBlock_mk1 (block' ++ [c]) (by simp))
  have h6 := Relation.RelatesWithinSteps.single (ub_rewindBlock_final (block' ++ [c]))
  have := h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
  refine this.of_le ?_
  simp only [List.length_append, List.length_singleton]
  omega

/-! #### Shuttle phase: the main loop -/

/-- Step-count bound for the shuttle loop: with `j` output bits already deposited and `m` payload
bits remaining, each round trip costs `2 * j + 5` steps and the final rewind `3 * j + 4`. -/
private def ubLoopBound : ℕ → ℕ → ℕ
  | j, 0 => 3 * j + 4
  | j, m + 1 => (2 * j + 5) + ubLoopBound (j + 1) m

private lemma ubLoopBound_closed : ∀ (m j : ℕ),
    ubLoopBound j m = 2 * j * m + m * m + 7 * m + 3 * j + 4 := by
  intro m
  induction m with
  | zero => intro j; simp [ubLoopBound]
  | succ m ih =>
    intro j
    simp only [ubLoopBound, ih (j + 1)]
    ring

open Relation in
/-- The shuttle loop: with nonempty output `out` deposited and the gap sized `out.length`,
process the remaining well-formed input `delimit P` and halt on `out ++ P`. -/
private lemma ub_loop : ∀ (P out : List Bool), out ≠ [] →
    RelatesWithinSteps undelimitBlockComputer.TransitionRelation
      ⟨some .seekInput, shuttleTape 0 (out.length - 1) out (BitstringEncoding.delimit P)⟩
      ⟨none, BiTape.mk₁ (out ++ P)⟩ (ubLoopBound out.length P.length) := by
  intro P
  induction P with
  | nil =>
    intro out hout
    have hjpos : 1 ≤ out.length := List.length_pos_of_ne_nil hout
    rw [delimit_nil, List.append_nil]
    have h1 := RelatesWithinSteps.of_relatesInSteps
      (ub_seek_phase (out.length - 1) 0 out [false])
    rw [show 0 + (out.length - 1) + 1 = out.length by omega] at h1
    have h2 := RelatesWithinSteps.single (ub_seek_false out.length out)
    have h3 := ub_rewind out.length out hout
    have hchain := h1.trans (h2.trans h3)
    refine hchain.of_le ?_
    simp only [ubLoopBound, List.length_nil]
    omega
  | cons b P'' ih =>
    intro out hout
    have hjpos : 1 ≤ out.length := List.length_pos_of_ne_nil hout
    rw [delimit_cons]
    have h1 := RelatesWithinSteps.of_relatesInSteps
      (ub_seek_phase (out.length - 1) 0 out (true :: b :: BitstringEncoding.delimit P''))
    rw [show 0 + (out.length - 1) + 1 = out.length by omega] at h1
    have h2 := RelatesWithinSteps.single
      (ub_seek_true out.length out b (BitstringEncoding.delimit P''))
    have h3 := RelatesWithinSteps.single
      (ub_grab out.length out b (BitstringEncoding.delimit P''))
    have h4 := RelatesWithinSteps.of_relatesInSteps
      (ub_carry_phase out.length 1 b out (BitstringEncoding.delimit P''))
    have h5 := ub_carry_turn b (out.length + 1) out (BitstringEncoding.delimit P'') hout
    have h6 := RelatesWithinSteps.single
      (ub_deposit b out.length out (BitstringEncoding.delimit P''))
    have h7 := ih (out ++ [b]) (by simp)
    rw [show (out ++ [b]).length - 1 = out.length by simp] at h7
    have hchain := h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))
    rw [show out ++ [b] ++ P'' = out ++ b :: P'' by simp] at hchain
    refine hchain.of_le ?_
    simp only [ubLoopBound, List.length_cons, List.length_append, List.length_nil, Nat.zero_add]
    omega

open Relation in
/-- The full shuttle phase: on a well-formed block `delimit P`, halt on `P`. -/
private lemma ub_shuttle (P : List Bool) :
    RelatesWithinSteps undelimitBlockComputer.TransitionRelation
      ⟨some .initTrue, BiTape.mk₁ (BitstringEncoding.delimit P)⟩
      ⟨none, BiTape.mk₁ P⟩ (P.length * P.length + 7 * P.length + 2) := by
  match P with
  | [] =>
    rw [delimit_nil]
    have hchain := (RelatesWithinSteps.single ub_initTrue_false).trans
      (RelatesWithinSteps.single ub_eraseAll_halt)
    refine hchain.of_le ?_
    simp
  | p :: P' =>
    rw [delimit_cons]
    have h0 := RelatesWithinSteps.single (ub_init_true p (BitstringEncoding.delimit P'))
    have h1 := RelatesWithinSteps.single (ub_init_bit p (BitstringEncoding.delimit P'))
    have h2 := RelatesWithinSteps.single (ub_deposit p 0 [] (BitstringEncoding.delimit P'))
    rw [List.nil_append] at h2
    have h3 := ub_loop P' [p] (by simp)
    rw [show ([p] : List Bool).length - 1 = 0 from rfl] at h3
    have hchain := h0.trans (h1.trans (h2.trans h3))
    rw [List.singleton_append] at hchain
    refine hchain.of_le (le_of_eq ?_)
    rw [ubLoopBound_closed]
    simp only [List.length_cons, List.length_nil]
    ring

open Relation Polynomial in
/-- `undelimitBlock` is computable in polynomial time: `undelimitBlockComputer` computes it
within `2 * n ^ 2 + 10 * n + 16` steps. -/
theorem PolyTimeComputable_undelimitBlock :
    Nonempty (Cslib.Turing.SingleTapeTM.PolyTimeComputable undelimitBlock) :=
  ⟨{ tm := undelimitBlockComputer
     timeBound := fun n => 2 * (n * n) + 10 * n + 16
     poly := C 2 * X ^ 2 + C 10 * X + C 16
     bounds := fun n => by
       simp only [eval_add, eval_mul, eval_C, eval_X, pow_two]
       omega
     outputsFunInTime := fun a => by
       simp only [OutputsWithinTime, initCfg, haltCfg]
       have h1 := nm_phase a
       have h2 := ub_shuttle (undelimitBlock a)
       have hlen := undelimitBlock_length_le a.length a rfl
       refine (h1.trans h2).of_le ?_
       have hsq : 4 * ((undelimitBlock a).length * (undelimitBlock a).length)
           ≤ a.length * a.length := by
         calc 4 * ((undelimitBlock a).length * (undelimitBlock a).length)
             = (2 * (undelimitBlock a).length) * (2 * (undelimitBlock a).length) := by ring
           _ ≤ a.length * a.length := Nat.mul_le_mul hlen hlen
       have key : ∀ s n A B : ℕ, 2 * s ≤ n → 4 * A ≤ B →
           2 * n + 6 + (A + 7 * s + 2) ≤ 2 * B + 10 * n + 16 := by
         intro s n A B hsn hAB
         omega
       exact key _ _ _ _ hlen hsq } ⟩

end UndelimitBlockMachine

/-- The first projection on encoded pairs of bitstrings is polynomial-time computable, by
composing `takeFirstBlock` (drop everything after the first block) and `undelimitBlock`
(strip framing). -/
lemma IsComputableInPolyTime_fst :
    IsComputableInPolyTime (Prod.fst : Bitstring × Bitstring → Bitstring) := by
  obtain ⟨m1⟩ := PolyTimeComputable_takeFirstBlock
  obtain ⟨m2⟩ := PolyTimeComputable_undelimitBlock
  refine ⟨undelimitBlock ∘ takeFirstBlock, ⟨m1.comp' m2⟩, ?_⟩
  rintro ⟨x, w⟩
  change undelimitBlock (takeFirstBlock (BitstringEncoding.encode (x, w)))
    = BitstringEncoding.encode x
  have h : BitstringEncoding.encode (x, w)
      = BitstringEncoding.delimit (BitstringEncoding.encode x) ++ BitstringEncoding.encode w := rfl
  rw [h, takeFirstBlock_delimit_append, undelimitBlock_delimit]

/-!
### Decoding an encoded pair: a validating parser

Since `Bitstring` carries the identity encoding, `decode` for pairs of bitstrings sends `l` to
`some (x, w)` exactly when `l = delimit x ++ w`, i.e. when `l` begins with a well-formed
self-delimiting block, and to `none` otherwise. At the level of encodings this is the function
`tagBlock`, which prepends `true` (the `some` tag) to well-formed inputs and erases ill-formed
ones — a validating parser, computable in linear time by a single left-to-right scan followed by
a shift-right-by-one (accept) or a leftward erase (reject).
-/

section TagBlockMachine

open Cslib.Turing Cslib.Turing.SingleTapeTM

/-- Does the bitstring begin with a well-formed self-delimiting block? -/
def hasBlock : List Bool → Bool
  | [] => false
  | false :: _ => true
  | true :: _ :: rest => hasBlock rest
  | [true] => false

/-- Tag a bitstring with a leading `true` if it begins with a well-formed self-delimiting block,
and return the empty bitstring otherwise. On pair encodings this computes `encode ∘ decode`. -/
def tagBlock (l : List Bool) : List Bool :=
  bif hasBlock l then true :: l else []

private lemma hasBlock_eq_isSome_undelimit : ∀ (n : ℕ) (l : List Bool), l.length = n →
    hasBlock l = (BitstringEncoding.undelimit l).isSome := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hlen
    match l with
    | [] => rfl
    | false :: rest => rfl
    | true :: [] => rfl
    | true :: b :: rest =>
      have hrec := ih rest.length (by simp only [List.length_cons] at hlen; omega) rest rfl
      simp only [hasBlock, BitstringEncoding.undelimit, hrec]
      cases BitstringEncoding.undelimit rest <;> rfl

private lemma undelimit_eq_some : ∀ (n : ℕ) (l : List Bool), l.length = n →
    ∀ x w, BitstringEncoding.undelimit l = some (x, w) →
      l = BitstringEncoding.delimit x ++ w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hlen x w h
    match l with
    | [] => simp [BitstringEncoding.undelimit] at h
    | false :: rest =>
      simp only [BitstringEncoding.undelimit, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | true :: [] => simp [BitstringEncoding.undelimit] at h
    | true :: b :: rest =>
      simp only [BitstringEncoding.undelimit, Option.map_eq_some_iff] at h
      obtain ⟨⟨p₁, p₂⟩, hp, heq⟩ := h
      have hrec := ih rest.length (by simp only [List.length_cons] at hlen; omega) rest rfl
        p₁ p₂ hp
      obtain ⟨rfl, rfl⟩ : b :: p₁ = x ∧ p₂ = w := by simpa [Prod.ext_iff] using heq
      simp only [hrec, BitstringEncoding.delimit, List.cons_append]

/-- States of the `tagBlock` machine. -/
inductive TBState
  /-- Parsing: expecting a pair marker `true` or the block terminator `false`. -/
  | pTF
  /-- Parsing: expecting the payload bit after a marker. -/
  | pB
  /-- Terminator seen (input valid): scan to the end of the input. -/
  | pOk
  /-- Accept phase: reading the rightmost unshifted cell. -/
  | shRead
  /-- Accept phase: writing the carried bit one cell to the right. -/
  | shWrite (b : Bool)
  /-- Accept phase: stepping back over the moving blank gap. -/
  | shBack
  /-- Accept phase: writing the leading `true` tag and halting. -/
  | shTag
  /-- Reject phase: erasing the input leftward. -/
  | erL
  deriving DecidableEq, Fintype

/-- The validating parser: scan the input checking that it begins with a well-formed
self-delimiting block; if so, shift the input one cell to the right (right to left, carrying one
bit at a time) and write a leading `true`; otherwise erase the input. Computes `tagBlock` in
linear time. -/
def tagBlockComputer : SingleTapeTM Bool where
  State := TBState
  q₀ := .pTF
  tr q sym :=
    match q, sym with
    -- parse phase
    | .pTF, some true => (⟨some true, some .right⟩, some .pB)
    | .pTF, some false => (⟨some false, some .right⟩, some .pOk)
    | .pTF, none => (⟨none, some .left⟩, some .erL)          -- no terminator: reject
    | .pB, some b => (⟨some b, some .right⟩, some .pTF)
    | .pB, none => (⟨none, some .left⟩, some .erL)           -- lone marker: reject
    | .pOk, some b => (⟨some b, some .right⟩, some .pOk)
    | .pOk, none => (⟨none, some .left⟩, some .shRead)       -- accept: shift and tag
    -- accept phase: shift the input right one cell, working right to left
    | .shRead, some b => (⟨none, some .right⟩, some (.shWrite b))
    | .shRead, none => (⟨none, some .right⟩, some .shTag)    -- everything shifted
    | .shWrite b, _ => (⟨some b, some .left⟩, some .shBack)
    | .shBack, _ => (⟨none, some .left⟩, some .shRead)
    | .shTag, _ => (⟨some true, none⟩, none)
    -- reject phase
    | .erL, some _ => (⟨none, some .left⟩, some .erL)
    | .erL, none => (⟨none, none⟩, none)

/-! #### Parse phase -/

private lemma tb_pTF_true (done rest : List Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pTF, splitTape done (true :: rest)⟩
      ⟨some .pB, splitTape (done ++ [true]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma tb_pTF_false (done rest : List Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pTF, splitTape done (false :: rest)⟩
      ⟨some .pOk, splitTape (done ++ [false]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma tb_pB_step (done : List Bool) (b : Bool) (rest : List Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pB, splitTape done (b :: rest)⟩
      ⟨some .pTF, splitTape (done ++ [b]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma tb_pOk_step (done : List Bool) (b : Bool) (rest : List Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pOk, splitTape done (b :: rest)⟩
      ⟨some .pOk, splitTape (done ++ [b]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape_head_cons,
    splitTape_scan]

open Relation in
private lemma tb_pOk_scan : ∀ (rest done : List Bool),
    RelatesWithinSteps tagBlockComputer.TransitionRelation
      ⟨some .pOk, splitTape done rest⟩ ⟨some .pOk, splitTape (done ++ rest) []⟩ rest.length := by
  intro rest
  induction rest with
  | nil =>
    intro done
    rw [List.append_nil]
    simp only [List.length_nil]
    exact RelatesWithinSteps.refl _
  | cons b r ih =>
    intro done
    have h1 := RelatesWithinSteps.single (tb_pOk_step done b r)
    have h2 := ih (done ++ [b])
    rw [show done ++ [b] ++ r = done ++ b :: r by simp] at h2
    exact (h1.trans h2).of_le (by simp only [List.length_cons]; omega)

open Relation in
/-- The scan on inputs beginning with a well-formed block ends at the right end in `pOk`. -/
private lemma tb_scan_accept : ∀ (n : ℕ) (rest done : List Bool), rest.length = n →
    hasBlock rest = true →
    RelatesWithinSteps tagBlockComputer.TransitionRelation
      ⟨some .pTF, splitTape done rest⟩ ⟨some .pOk, splitTape (done ++ rest) []⟩ rest.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro rest done hlen hblock
    match rest with
    | [] => simp [hasBlock] at hblock
    | false :: r =>
      have h1 := RelatesWithinSteps.single (tb_pTF_false done r)
      have h2 := tb_pOk_scan r (done ++ [false])
      rw [show done ++ [false] ++ r = done ++ false :: r by simp] at h2
      exact (h1.trans h2).of_le (by simp only [List.length_cons]; omega)
    | true :: [] => simp [hasBlock] at hblock
    | true :: b :: r =>
      have h1 := RelatesWithinSteps.single (tb_pTF_true done (b :: r))
      have h2 := RelatesWithinSteps.single (tb_pB_step (done ++ [true]) b r)
      have h3 := ih r.length (by simp only [List.length_cons] at hlen; omega) r
        (done ++ [true] ++ [b]) rfl (by simpa [hasBlock] using hblock)
      rw [show done ++ [true] ++ [b] ++ r = done ++ true :: b :: r by simp] at h3
      refine (h1.trans (h2.trans h3)).of_le ?_
      simp only [List.length_cons]
      omega

/-! #### Accept phase: shift right by one and tag -/

/-- Tape during the accept-phase shift: `done ++ [c]` is still unshifted (head on `c`), and
`shifted` has been moved one cell to the right, separated by a single blank. -/
private def shiftTape (done : List Bool) (c : Bool) (shifted : List Bool) : BiTape Bool :=
  ⟨some c, StackTape.mapSome done.reverse, StackTape.cons none (StackTape.mapSome shifted)⟩

private lemma tb_pOk_exit (l' : List Bool) (c : Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pOk, splitTape (l' ++ [c]) []⟩
      ⟨some .shRead, shiftTape l' c []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, shiftTape,
    List.head?_nil, List.tail_nil, mapSome_nil, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveLeft, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, mapSome_head, mapSome_tail, List.head?_cons, List.tail_cons,
    cons_none_empty]

private lemma tb_shift_read (L : StackTape Bool) (c : Bool) (shifted : List Bool) :
    tagBlockComputer.TransitionRelation
      ⟨some .shRead, ⟨some c, L, StackTape.cons none (StackTape.mapSome shifted)⟩⟩
      ⟨some (.shWrite c), ⟨none, StackTape.cons none L, StackTape.mapSome shifted⟩⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveRight, StackTape.head_cons, StackTape.tail_cons]

private lemma tb_shift_write (L : StackTape Bool) (c : Bool) (shifted : List Bool) :
    tagBlockComputer.TransitionRelation
      ⟨some (.shWrite c), ⟨none, StackTape.cons none L, StackTape.mapSome shifted⟩⟩
      ⟨some .shBack, ⟨none, L, StackTape.mapSome (c :: shifted)⟩⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveLeft, StackTape.head_cons, StackTape.tail_cons,
    cons_some_mapSome]

private lemma tb_shift_back (D : List Bool) (c' : Bool) (rest : List Bool) :
    tagBlockComputer.TransitionRelation
      ⟨some .shBack, ⟨none, StackTape.mapSome (D ++ [c']).reverse, StackTape.mapSome rest⟩⟩
      ⟨some .shRead, shiftTape D c' rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, shiftTape,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft,
    mapSome_head, mapSome_tail, List.head?_cons, List.tail_cons]

private lemma tb_shift_back_nil (rest : List Bool) :
    tagBlockComputer.TransitionRelation
      ⟨some .shBack, ⟨none, ∅, StackTape.mapSome rest⟩⟩
      ⟨some .shRead, ⟨none, ∅, StackTape.cons none (StackTape.mapSome rest)⟩⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveLeft, empty_head, empty_tail]

private lemma tb_shift_read_nil (rest : List Bool) :
    tagBlockComputer.TransitionRelation
      ⟨some .shRead, ⟨none, ∅, StackTape.cons none (StackTape.mapSome rest)⟩⟩
      ⟨some .shTag, ⟨none, ∅, StackTape.mapSome rest⟩⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveRight, StackTape.head_cons, StackTape.tail_cons,
    cons_none_empty]

private lemma tb_shift_tag (rest : List Bool) :
    tagBlockComputer.TransitionRelation ⟨some .shTag, ⟨none, ∅, StackTape.mapSome rest⟩⟩
      ⟨none, BiTape.mk₁ (true :: rest)⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.mk₁, BiTape.write,
    BiTape.optionMove]

open Relation in
/-- The full shift-and-tag: from the rightmost cell, halt on `true :: input`. -/
private lemma tb_shift : ∀ (done : List Bool) (c : Bool) (shifted : List Bool),
    RelatesWithinSteps tagBlockComputer.TransitionRelation
      ⟨some .shRead, shiftTape done c shifted⟩
      ⟨none, BiTape.mk₁ (true :: (done ++ c :: shifted))⟩ (3 * done.length + 5) := by
  intro done
  induction done using List.reverseRecOn with
  | nil =>
    intro c shifted
    simp only [shiftTape, List.reverse_nil, mapSome_nil, List.nil_append, List.length_nil,
      Nat.mul_zero, Nat.zero_add]
    have h1 := RelatesWithinSteps.single (tb_shift_read ∅ c shifted)
    have h2 := RelatesWithinSteps.single (tb_shift_write ∅ c shifted)
    have h3 := RelatesWithinSteps.single (tb_shift_back_nil (c :: shifted))
    have h4 := RelatesWithinSteps.single (tb_shift_read_nil (c :: shifted))
    have h5 := RelatesWithinSteps.single (tb_shift_tag (c :: shifted))
    exact (h1.trans (h2.trans (h3.trans (h4.trans h5)))).of_le (by omega)
  | append_singleton D d ih =>
    intro c shifted
    have h1 := RelatesWithinSteps.single
      (tb_shift_read (StackTape.mapSome (D ++ [d]).reverse) c shifted)
    have h2 := RelatesWithinSteps.single
      (tb_shift_write (StackTape.mapSome (D ++ [d]).reverse) c shifted)
    have h3 := RelatesWithinSteps.single (tb_shift_back D d (c :: shifted))
    have h4 := ih d (c :: shifted)
    rw [show D ++ d :: c :: shifted = (D ++ [d]) ++ c :: shifted by simp] at h4
    have hchain := h1.trans (h2.trans (h3.trans h4))
    refine hchain.of_le ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-! #### Reject phase: erase the input -/

private lemma tb_pTF_reject (D : List Bool) (c : Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pTF, splitTape (D ++ [c]) []⟩
      ⟨some .erL, splitTape D [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, List.head?_nil,
    List.tail_nil, List.head?_cons, List.tail_cons, mapSome_nil, BiTape.write, BiTape.optionMove,
    BiTape.move, BiTape.moveLeft, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, mapSome_head, mapSome_tail, cons_none_empty]

private lemma tb_pB_reject (D : List Bool) (c : Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pB, splitTape (D ++ [c]) []⟩
      ⟨some .erL, splitTape D [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, List.head?_nil,
    List.tail_nil, List.head?_cons, List.tail_cons, mapSome_nil, BiTape.write, BiTape.optionMove,
    BiTape.move, BiTape.moveLeft, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, mapSome_head, mapSome_tail, cons_none_empty]

private lemma tb_pTF_reject_nil :
    tagBlockComputer.TransitionRelation ⟨some .pTF, splitTape [] []⟩
      ⟨some .erL, BiTape.mk₁ []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, List.head?_nil,
    List.tail_nil, List.reverse_nil, mapSome_nil, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveLeft, empty_head, empty_tail, cons_none_empty, BiTape.mk₁, BiTape.empty_eq_nil,
    BiTape.nil]

private lemma tb_erL_step (D : List Bool) (c' c : Bool) :
    tagBlockComputer.TransitionRelation ⟨some .erL, splitTape (D ++ [c']) [c]⟩
      ⟨some .erL, splitTape D [c']⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, List.head?_cons,
    List.tail_cons, mapSome_nil, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, mapSome_head, mapSome_tail, cons_none_empty]

private lemma tb_erL_last (c : Bool) :
    tagBlockComputer.TransitionRelation ⟨some .erL, splitTape [] [c]⟩
      ⟨some .erL, BiTape.mk₁ []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, List.head?_cons,
    List.tail_cons, mapSome_nil, List.reverse_nil, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveLeft, empty_head, empty_tail, cons_none_empty, BiTape.mk₁, BiTape.empty_eq_nil,
    BiTape.nil]

private lemma tb_erL_halt :
    tagBlockComputer.TransitionRelation ⟨some .erL, BiTape.mk₁ []⟩ ⟨none, BiTape.mk₁ []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.mk₁, BiTape.write,
    BiTape.optionMove, BiTape.empty_eq_nil, BiTape.nil]

open Relation in
private lemma tb_erase : ∀ (D : List Bool) (c : Bool),
    RelatesWithinSteps tagBlockComputer.TransitionRelation
      ⟨some .erL, splitTape D [c]⟩ ⟨none, BiTape.mk₁ []⟩ (D.length + 2) := by
  intro D
  induction D using List.reverseRecOn with
  | nil =>
    intro c
    exact ((RelatesWithinSteps.single (tb_erL_last c)).trans
      (RelatesWithinSteps.single tb_erL_halt)).of_le (by simp)
  | append_singleton D' c' ih =>
    intro c
    have hchain := (RelatesWithinSteps.single (tb_erL_step D' c' c)).trans (ih c')
    refine hchain.of_le ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

open Relation in
/-- The scan on inputs not beginning with a well-formed block ends by erasing everything. -/
private lemma tb_scan_reject : ∀ (n : ℕ) (rest done : List Bool), rest.length = n →
    hasBlock rest = false →
    RelatesWithinSteps tagBlockComputer.TransitionRelation
      ⟨some .pTF, splitTape done rest⟩ ⟨none, BiTape.mk₁ []⟩
      (2 * rest.length + done.length + 4) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro rest done hlen hblock
    match rest with
    | [] =>
      rcases List.eq_nil_or_concat done with rfl | ⟨D, c, rfl⟩
      · exact ((RelatesWithinSteps.single tb_pTF_reject_nil).trans
          (RelatesWithinSteps.single tb_erL_halt)).of_le (by simp)
      · rw [List.concat_eq_append]
        have hchain := (RelatesWithinSteps.single (tb_pTF_reject D c)).trans (tb_erase D c)
        refine hchain.of_le ?_
        simp only [List.length_nil, List.length_append, List.length_cons]
        omega
    | false :: r => simp [hasBlock] at hblock
    | true :: [] =>
      have h1 := RelatesWithinSteps.single (tb_pTF_true done [])
      have h2 := RelatesWithinSteps.single (tb_pB_reject done true)
      have h3 := tb_erase done true
      refine (h1.trans (h2.trans h3)).of_le ?_
      simp only [List.length_cons, List.length_nil]
      omega
    | true :: b :: r =>
      have h1 := RelatesWithinSteps.single (tb_pTF_true done (b :: r))
      have h2 := RelatesWithinSteps.single (tb_pB_step (done ++ [true]) b r)
      have h3 := ih r.length (by simp only [List.length_cons] at hlen; omega) r
        (done ++ [true] ++ [b]) rfl (by simpa [hasBlock] using hblock)
      refine (h1.trans (h2.trans h3)).of_le ?_
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega

open Relation Polynomial in
/-- `tagBlock` is computable in linear time by `tagBlockComputer`. -/
theorem PolyTimeComputable_tagBlock :
    Nonempty (Cslib.Turing.SingleTapeTM.PolyTimeComputable tagBlock) :=
  ⟨{ tm := tagBlockComputer
     timeBound := fun n => 4 * n + 4
     poly := C 4 * X + C 4
     bounds := fun n => by simp only [eval_add, eval_mul, eval_C, eval_X]; omega
     outputsFunInTime := fun a => by
       simp only [OutputsWithinTime, initCfg, haltCfg]
       cases hb : hasBlock a with
       | false =>
         have h := tb_scan_reject a.length a [] rfl hb
         rw [splitTape_nil_left] at h
         rw [show tagBlock a = [] by simp [tagBlock, hb]]
         refine h.of_le ?_
         simp only [List.length_nil]
         omega
       | true =>
         have hne : a ≠ [] := by rintro rfl; simp [hasBlock] at hb
         obtain ⟨l', c, rfl⟩ := (List.eq_nil_or_concat a).resolve_left hne
         rw [List.concat_eq_append] at hb ⊢
         have h1 := tb_scan_accept (l' ++ [c]).length (l' ++ [c]) [] rfl hb
         rw [splitTape_nil_left, List.nil_append] at h1
         have h2 := RelatesWithinSteps.single (tb_pOk_exit l' c)
         have h3 := tb_shift l' c []
         rw [show tagBlock (l' ++ [c]) = true :: (l' ++ [c]) by simp [tagBlock, hb]]
         refine (h1.trans (h2.trans h3)).of_le ?_
         simp only [List.length_append, List.length_cons, List.length_nil]
         omega } ⟩

private lemma encode_option_none :
    BitstringEncoding.encode (none : Option (Bitstring × Bitstring)) = ([] : List Bool) := rfl

private lemma encode_option_some (x w : List Bool) :
    BitstringEncoding.encode (some (Bitstring.ofList x, Bitstring.ofList w))
      = true :: (BitstringEncoding.delimit x ++ w) := rfl

/-- The `tagBlock` function computes `encode ∘ decode` for pairs of bitstrings, at the level of
raw `List Bool` inputs. -/
private lemma tagBlock_eq_encode_decodePair (l : List Bool) :
    tagBlock l
      = BitstringEncoding.encode
          (BitstringEncoding.decodePair (α := Bitstring) (β := Bitstring) l) := by
  cases h : BitstringEncoding.undelimit l with
  | none =>
    have hd : BitstringEncoding.decodePair (α := Bitstring) (β := Bitstring) l = none := by
      simp [BitstringEncoding.decodePair, h]
    have hb : hasBlock l = false := by
      rw [hasBlock_eq_isSome_undelimit l.length l rfl, h]; rfl
    rw [hd, encode_option_none]
    simp [tagBlock, hb]
  | some p =>
    obtain ⟨x, w⟩ := p
    have hd : BitstringEncoding.decodePair (α := Bitstring) (β := Bitstring) l
        = some (Bitstring.ofList x, Bitstring.ofList w) := by
      simp [BitstringEncoding.decodePair, h, BitstringEncoding.decode_bitstring]
    have hb : hasBlock l = true := by
      rw [hasBlock_eq_isSome_undelimit l.length l rfl, h]; rfl
    have hl : l = BitstringEncoding.delimit x ++ w :=
      undelimit_eq_some l.length l rfl x w h
    rw [hd, encode_option_some, ← hl]
    simp [tagBlock, hb]

end TagBlockMachine

/-- Decoding a bitstring as a pair of bitstrings is polynomial-time computable: the machine
validates that the input begins with a well-formed self-delimiting block, tagging it with a
leading `true` (the `some` tag) if so and erasing it otherwise. -/
lemma IsComputableInPolyTime_decode :
    IsComputableInPolyTime (α := Bitstring)
      (BitstringEncoding.decode (α := Bitstring × Bitstring)) := by
  obtain ⟨m⟩ := PolyTimeComputable_tagBlock
  refine ⟨tagBlock, ⟨m⟩, fun l =>
    (tagBlock_eq_encode_decodePair (BitstringEncoding.encode l)).trans ?_⟩
  -- `decodePair (encode l)` and `decode l` agree definitionally: `encode` on a `Bitstring` is
  -- the identity and `decode` on pairs is `decodePair`.
  rfl

end ComplexityTheory
