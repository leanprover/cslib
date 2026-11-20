/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Encoding.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Subsequential
import Mathlib.Tactic.DeriveFintype

/-!
# Machines for delimited words

The encoder emits `[true, b]` for each data bit `b` and emits `[false]` at end of input.
The decoders use the tag bits to decide which data bits to emit or skip.
A subsequential transducer supplies the terminator for `delimit` and the empty-input default for
`undelimitOr`. Sequential transducers suffice for `dropDelimited` and `undelimitAll`.

## Main results

Each of the following bounds is linear in the input length and uses zero work space.

* `Turing.MultiTapeTM.computableInTimeAndSpace_delimit` bounds the cost of writing a codeword.
* `Turing.MultiTapeTM.computableInTimeAndSpace_undelimit` and
  `Turing.MultiTapeTM.computableInTimeAndSpace_undelimitOr` bound the cost of decoding the first
  word, with a configurable default on empty input for `undelimitOr`.
* `Turing.MultiTapeTM.computableInTimeAndSpace_dropDelimited` bounds the cost of copying the
  suffix after the first codeword.
* `Turing.MultiTapeTM.computableInTimeAndSpace_undelimitAll` bounds the cost of decoding all
  codewords and concatenating their contents.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Encoding Cslib.Automata

/-! ### Writing a delimited word -/

private def delimitTransducer : SubsequentialTransducer Unit Bool Bool where
  start := ()
  tr _ _ := ()
  emit _ b := [true, b]
  finalOut _ := [false]

private theorem output_delimit (w : List Bool) : delimitTransducer.outputFrom () w = delimit w := by
  induction w <;> simp_all [delimitTransducer]

/-- Writing a delimited code is computable in linear time and zero work space. -/
theorem computableInTimeAndSpace_delimit :
    ComputableInTimeAndSpace delimit encBits encBits (fun w => 3 * w.length + 2) (fun _ => 0) :=
  (computableInTimeAndSpace_of_subsequential delimitTransducer delimit
    (fun w => by simpa using output_delimit w)).mono
    (fun _ => by lia [length_delimit]) fun _ => le_rfl

/-! ### The word whose delimited code starts the input -/

/-- At the start of the input, about to read a tag, about to read a data bit, or past the
delimiter. -/
private inductive UndelimitState : Type
  | start
  | tag
  | bit
  | done
  deriving Fintype

/-- The transducer emits data bits until the delimiter and emits the default on empty input. -/
private def undelimitTransducer (e : List Bool) :
    SubsequentialTransducer UndelimitState Bool Bool where
  start := .start
  tr
    | .start, true | .tag, true => .bit
    | .start, false | .tag, false => .done
    | .bit, _ => .tag
    | .done, _ => .done
  emit
    | .bit, b => [b]
    | _, _ => []
  finalOut
    | .start => e
    | _ => []

private def undelimitFrom (e : List Bool) : UndelimitState → List Bool → List Bool
  | .start, w => undelimitOr e w
  | .tag, w => undelimit w
  | .bit, w => w.head?.toList ++ undelimit w.tail
  | .done, _ => []

private lemma outputFrom_undelimit (e : List Bool) (q : UndelimitState) (w : List Bool) :
    (undelimitTransducer e).outputFrom q w = undelimitFrom e q w := by
  apply SubsequentialTransducer.outputFrom_eq_of_spec
  · intro q
    cases q <;> rfl
  · intro q b w
    cases q <;> cases b <;> cases w <;> simp [undelimitTransducer, undelimitFrom]

/-- `undelimitOr e` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_undelimitOr (e : List Bool) :
    ComputableInTimeAndSpace (undelimitOr e) encBits encBits
      (fun w => 2 * w.length + e.length + 1) (fun _ => 0) :=
  (computableInTimeAndSpace_of_subsequential (undelimitTransducer e) (undelimitOr e)
    (fun w => by simpa using! outputFrom_undelimit e .start w)).mono
    (fun _ => by lia [length_undelimitOr_le]) fun _ => le_rfl

/-- `undelimit` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_undelimit :
    ComputableInTimeAndSpace undelimit encBits encBits (fun w => 2 * w.length + 1)
      (fun _ => 0) := by
  simpa using computableInTimeAndSpace_undelimitOr []

/-! ### What follows the first delimited code -/

/-- About to skip a tag, about to skip a data bit, or copying what follows the delimiter. -/
private inductive DropDelimitedState : Type
  | tag
  | bit
  | copy
  deriving Fintype

private def dropDelimitedTransducer : SequentialTransducer DropDelimitedState Bool Bool where
  start := .tag
  tr
    | .tag, true => .bit
    | .tag, false => .copy
    | .bit, _ => .tag
    | .copy, _ => .copy
  emit
    | .copy, b => [b]
    | _, _ => []

private def dropDelimitedFrom : DropDelimitedState → List Bool → List Bool
  | .tag, w => dropDelimited w
  | .bit, w => dropDelimited w.tail
  | .copy, w => w

private lemma outputFrom_dropDelimited (q : DropDelimitedState) (w : List Bool) :
    dropDelimitedTransducer.outputFrom q w = dropDelimitedFrom q w := by
  apply SequentialTransducer.outputFrom_eq_of_spec
  · intro q
    cases q <;> rfl
  · intro q b w
    cases q <;> cases b <;> cases w <;> simp [dropDelimitedTransducer, dropDelimitedFrom]

/-- `dropDelimited` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_dropDelimited :
    ComputableInTimeAndSpace dropDelimited encBits encBits (fun w => 2 * w.length + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_sequential dropDelimitedTransducer dropDelimited
    (fun w => by simpa using! outputFrom_dropDelimited .tag w)).mono
    (fun _ => by lia [length_dropDelimited_le]) fun _ => le_rfl

/-! ### All delimited codes -/

/-- The state records whether a data bit follows. -/
private def undelimitAllTransducer : SequentialTransducer Bool Bool Bool where
  start := false
  tr bit b := !bit && b
  emit bit b := if bit then [b] else []

private def undelimitAllFrom : Bool → List Bool → List Bool
  | false, w => undelimitAll w
  | true, w => w.head?.toList ++ undelimitAll w.tail

private lemma outputFrom_undelimitAll (q : Bool) (w : List Bool) :
    undelimitAllTransducer.outputFrom q w = undelimitAllFrom q w := by
  apply SequentialTransducer.outputFrom_eq_of_spec
  · intro q
    cases q <;> rfl
  · intro q b w
    cases q <;> cases b <;> cases w <;> simp [undelimitAllTransducer, undelimitAllFrom]

/-- `undelimitAll` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_undelimitAll :
    ComputableInTimeAndSpace undelimitAll encBits encBits (fun w => 2 * w.length + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_sequential undelimitAllTransducer undelimitAll
    (fun w => by simpa using! outputFrom_undelimitAll false w)).mono
    (fun _ => by lia [length_undelimitAll_le]) fun _ => le_rfl

end Turing.MultiTapeTM
