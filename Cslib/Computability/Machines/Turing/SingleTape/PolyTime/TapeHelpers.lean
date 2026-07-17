/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-!
# Tape configurations for single-tape scan/erase/rewind machines

This file collects the low-level `StackTape`/`BiTape` helpers shared by the polynomial-time machine
constructions in this directory (`takeFirstBlockComputer`, `undelimitBlockComputer`,
`tagBlockComputer`). They describe the tape configurations of a left-to-right scan and the
subsequent erase and rewind phases, together with the single-step rewrite lemmas that move between
adjacent configurations.

* `splitTape done rest`: mid-scan, with `rest` under and to the right of the head and `done`
  already scanned (in the reversed left half).
* `eraseTape n block suffix`: erasing the suffix after a block, `n` cells already blanked.
* `rewindTape n block`: rewinding leftward over the `n` blanks left by the erase phase.
-/

namespace ComplexityTheory

open Cslib.Turing Cslib.Turing.SingleTapeTM Cslib.Turing.StackTape

/-! ### The scan configuration `splitTape` -/

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

lemma splitTape_head_cons (done : List Bool) (c : Bool) (rest : List Bool) :
    (splitTape done (c :: rest)).head = some c := rfl

lemma splitTape_write_head (done : List Bool) (c : Bool) (rest : List Bool) :
    (splitTape done (c :: rest)).write (some c) = splitTape done (c :: rest) := rfl

lemma mk₁_eq (l : List Bool) :
    BiTape.mk₁ l = ⟨l.head?, ∅, StackTape.mapSome l.tail⟩ := by cases l <;> rfl

/-! ### The erase and rewind configurations -/

/-- The left half of the tape during the erase/rewind phases: `block` reversed, buried under `n`
blanks (the erased suffix cells). -/
def blanksLeft (n : ℕ) (block : List Bool) : StackTape Bool :=
  (StackTape.cons none)^[n] (StackTape.mapSome block.reverse)

lemma blanksLeft_succ (n : ℕ) (block : List Bool) :
    blanksLeft (n + 1) block = StackTape.cons none (blanksLeft n block) := by
  simp only [blanksLeft, Function.iterate_succ_apply']

/-- Tape while erasing the suffix: `block` (with `n` erased blanks) sits in the left half, `suffix`
lies under and to the right of the head. -/
def eraseTape (n : ℕ) (block suffix : List Bool) : BiTape Bool :=
  ⟨suffix.head?, blanksLeft n block, StackTape.mapSome suffix.tail⟩

/-- Tape while rewinding leftward: `block` reversed under `n` blanks, head on the blanks. -/
def rewindTape (n : ℕ) (block : List Bool) : BiTape Bool :=
  ⟨none, blanksLeft n block, ∅⟩

lemma eraseTape_nil (n : ℕ) (block : List Bool) :
    eraseTape n block [] = rewindTape n block := rfl

lemma eraseTape_zero (block suffix : List Bool) :
    eraseTape 0 block suffix = splitTape block suffix := rfl

lemma splitTape_nil_eq_rewind (done : List Bool) :
    splitTape done [] = rewindTape 0 done := rfl

end ComplexityTheory
