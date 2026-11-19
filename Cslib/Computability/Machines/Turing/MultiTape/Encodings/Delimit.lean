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
The decoders use the tag bits to decide which data bits to emit or skip. Each proof identifies
the transducer's output on arbitrary input and applies
`Turing.MultiTapeTM.computableInTimeAndSpace_of_subsequential` to obtain linear time and
zero work space.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_delimit`: writing a delimited word.
* `Turing.MultiTapeTM.computableInTimeAndSpace_undelimit`,
  `Turing.MultiTapeTM.computableInTimeAndSpace_undelimitOr`: the word whose delimited code starts
  the input.
* `Turing.MultiTapeTM.computableInTimeAndSpace_dropDelimited`: what follows the first delimited
  code.
* `Turing.MultiTapeTM.computableInTimeAndSpace_undelimitAll`: the concatenation of all words whose
  delimited codes make up the input.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Encoding Cslib.Automata

/-! ### Writing a delimited word -/

private def delimitTransducer : SubsequentialTransducer Unit Bool Bool where
  start := ()
  step _ b := ([true, b], ())
  final _ := [false]

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
  step
    | .start, true | .tag, true => ([], .bit)
    | .start, false | .tag, false => ([], .done)
    | .bit, b => ([b], .tag)
    | .done, _ => ([], .done)
  final
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

private def dropDelimitedTransducer : SubsequentialTransducer DropDelimitedState Bool Bool where
  start := .tag
  step
    | .tag, true => ([], .bit)
    | .tag, false => ([], .copy)
    | .bit, _ => ([], .tag)
    | .copy, b => ([b], .copy)
  final _ := []

private def dropDelimitedFrom : DropDelimitedState → List Bool → List Bool
  | .tag, w => dropDelimited w
  | .bit, w => dropDelimited w.tail
  | .copy, w => w

private lemma outputFrom_dropDelimited (q : DropDelimitedState) (w : List Bool) :
    dropDelimitedTransducer.outputFrom q w = dropDelimitedFrom q w := by
  apply SubsequentialTransducer.outputFrom_eq_of_spec
  · intro q
    cases q <;> rfl
  · intro q b w
    cases q <;> cases b <;> cases w <;> simp [dropDelimitedTransducer, dropDelimitedFrom]

/-- `dropDelimited` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_dropDelimited :
    ComputableInTimeAndSpace dropDelimited encBits encBits (fun w => 2 * w.length + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_subsequential dropDelimitedTransducer dropDelimited
    (fun w => by simpa using! outputFrom_dropDelimited .tag w)).mono
    (fun _ => by lia [length_dropDelimited_le]) fun _ => le_rfl

/-! ### All delimited codes -/

/-- The state records whether a data bit follows. -/
private def undelimitAllTransducer : SubsequentialTransducer Bool Bool Bool where
  start := false
  step
    | false, true => ([], true)
    | false, false => ([], false)
    | true, b => ([b], false)
  final _ := []

private def undelimitAllFrom : Bool → List Bool → List Bool
  | false, w => undelimitAll w
  | true, w => w.head?.toList ++ undelimitAll w.tail

private lemma outputFrom_undelimitAll (q : Bool) (w : List Bool) :
    undelimitAllTransducer.outputFrom q w = undelimitAllFrom q w := by
  apply SubsequentialTransducer.outputFrom_eq_of_spec
  · intro q
    cases q <;> rfl
  · intro q b w
    cases q <;> cases b <;> cases w <;> simp [undelimitAllTransducer, undelimitAllFrom]

/-- `undelimitAll` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_undelimitAll :
    ComputableInTimeAndSpace undelimitAll encBits encBits (fun w => 2 * w.length + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_subsequential undelimitAllTransducer undelimitAll
    (fun w => by simpa using! outputFrom_undelimitAll false w)).mono
    (fun _ => by lia [length_undelimitAll_le]) fun _ => le_rfl

end Turing.MultiTapeTM
