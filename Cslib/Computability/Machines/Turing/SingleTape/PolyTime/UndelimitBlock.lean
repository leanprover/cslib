/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Cslib.Foundations.Data.BitstringEncoding
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.TapeHelpers

/-!
# The `undelimitBlock` machine

`undelimitBlock` turns a single self-delimiting block `delimit P` into its payload `P`, i.e. strips
the framing bits. This is the genuine compaction of the pair-projection pipeline: the machine first
normalizes the input to a well-formed terminated block, then compacts the payload bits to the front
of the tape, a quadratic-time single-tape shuttle.

The main result is `PolyTimeComputable_undelimitBlock`, witnessed by `undelimitBlockComputer`.
-/

open Computability Turing

namespace ComplexityTheory

open Cslib.Turing Cslib.Turing.SingleTapeTM Cslib.Turing.StackTape
open BitstringEncoding (undelimitBlock)

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

end ComplexityTheory
