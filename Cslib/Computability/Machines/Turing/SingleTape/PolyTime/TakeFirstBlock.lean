/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Cslib.Foundations.Data.BitstringEncoding
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.TapeHelpers

/-!
# The `takeFirstBlock` machine

`takeFirstBlock` keeps the leading self-delimiting block of a bitstring, dropping everything after
it: on a pair encoding `delimit (encode x) ++ encode w` it returns `delimit (encode x)`. On a tape
this is a scan to the end of the first block followed by erasing the suffix — no compaction, since
the kept prefix stays in place.

The main result is `PolyTimeComputable_takeFirstBlock`, witnessed by `takeFirstBlockComputer`.
-/

open Computability Turing

namespace ComplexityTheory

open Cslib.Turing Cslib.Turing.SingleTapeTM Cslib.Turing.StackTape

/-- Keep the leading self-delimiting block of a bitstring, dropping everything after it. On a pair
encoding `delimit (encode x) ++ encode w` this returns `delimit (encode x)`. -/
def takeFirstBlock : List Bool → List Bool
  | [] => []
  | false :: _ => [false]
  | true :: b :: rest => true :: b :: takeFirstBlock rest
  | [true] => [true]

@[simp]
lemma takeFirstBlock_delimit_append (P Q : List Bool) :
    takeFirstBlock (BitstringEncoding.delimit P ++ Q) = BitstringEncoding.delimit P := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [BitstringEncoding.delimit, List.cons_append, takeFirstBlock, ih]

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


end ComplexityTheory
