/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Encoding.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.TransduceOutput
public import Cslib.Computability.Machines.Turing.MultiTape.Transducer
import Mathlib.Tactic.DeriveFintype

/-!
# Complexity of operations on delimited Boolean words

The functions `delimit`, `undelimit`, `undelimitOr`, `dropDelimited` and `undelimitAll` are
computable by multitape Turing machines in linear time and zero work space.
The constructions use subsequential transducers for `delimit` and `undelimitOr`.
Taking the empty default gives `undelimit`. Sequential transducers suffice for `dropDelimited`
and `undelimitAll`.

## Main definitions

* `Cslib.Encoding.undelimitOr` decodes the first word like `Cslib.Encoding.undelimit` and
  supplies a default on empty input.
* `Cslib.Encoding.undelimitAll` concatenates all decoded words.

## Main results

* `Cslib.Encoding.undelimitAll_delimit_append` decodes a leading codeword and continues
  decoding the suffix.
* `Turing.MultiTapeTM.computableInTimeAndSpace_delimit` bounds the cost of writing a codeword.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.delimit`: a computable function is computable with
  the delimited output encoding `Cslib.Encoding.encDelimited`, in time `2 * t + 1`.
* `Turing.MultiTapeTM.computableInTimeAndSpace_undelimit` and
  `Turing.MultiTapeTM.computableInTimeAndSpace_undelimitOr` bound the cost of decoding the first
  word, with a configurable default on empty input for `undelimitOr`.
* `Turing.MultiTapeTM.computableInTimeAndSpace_dropDelimited` bounds the cost of copying the
  suffix after the first codeword.
* `Turing.MultiTapeTM.computableInTimeAndSpace_undelimitAll` bounds the cost of decoding all
  codewords and concatenating their contents.
-/

public section

namespace Cslib.Encoding

/-- Decode the first word with `undelimit`, and use `e` when the input is empty. -/
@[expose]
def undelimitOr (e : List Bool) : List Bool → List Bool
  | [] => e
  | b :: w => undelimit (b :: w)

attribute [simp] undelimitOr.eq_1 undelimitOr.eq_2

@[simp]
theorem undelimitOr_nil_left : undelimitOr [] = undelimit := by
  funext w
  cases w <;> rfl

@[simp, scoped grind =]
theorem undelimitOr_delimit_append (e w u : List Bool) :
    undelimitOr e (delimit w ++ u) = w := by
  cases w <;> simp

/-- The concatenation of the words whose delimited codes make up `w`: removes all tags and
delimiters. A trailing tag `true` without a data bit is ignored. -/
@[expose, simp]
def undelimitAll : List Bool → List Bool
  | true :: b :: v => b :: undelimitAll v
  | false :: v => undelimitAll v
  | [] | [true] => []

@[simp, scoped grind =]
theorem undelimitAll_delimit_append (w u : List Bool) :
    undelimitAll (delimit w ++ u) = w ++ undelimitAll u := by
  induction w <;> simp [*]

/-- Decoding with a default adds at most the length of the default. -/
theorem length_undelimitOr_le (e w : List Bool) :
    (undelimitOr e w).length ≤ w.length + e.length := by
  cases w <;> grind [undelimitOr, length_undelimit_le]

/-- Decoding all codewords does not make a word longer. -/
theorem length_undelimitAll_le (w : List Bool) : (undelimitAll w).length ≤ w.length := by
  fun_induction undelimitAll w <;> grind

end Cslib.Encoding

namespace Turing.MultiTapeTM

open Cslib.Encoding Cslib.Automata

/-! ### Writing a delimited word -/

private def delimitTransducer : SubsequentialTransducer Unit Bool Bool where
  start := ()
  tr _ _ := ()
  emit _ b := [true, b]
  finalOut _ := [false]

private lemma evalFrom_delimit (w : List Bool) : delimitTransducer.evalFrom () w = delimit w := by
  induction w <;> simp_all [delimitTransducer]

/-- Writing a delimited code is computable in linear time and zero work space. -/
theorem computableInTimeAndSpace_delimit :
    ComputableInTimeAndSpace delimit encBits encBits (fun w => 3 * w.length + 2) (fun _ => 0) :=
  (computableInTimeAndSpace_of_subsequential delimitTransducer delimit evalFrom_delimit).mono
    (fun _ => by lia [length_delimit]) fun _ => le_rfl

/-- A function computable with some output encoding is computable with the delimited output
encoding, in at most twice the time plus one step, and in the same space. -/
theorem ComputableInTimeAndSpace.delimit {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {t s : α → ℕ} (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ComputableInTimeAndSpace f encIn (encDelimited encOut) (fun a => 2 * t a + 1) s :=
  h.transduce (g := id) delimitTransducer (m := 2) (l := 1) (by simp [delimitTransducer])
    (by simp [delimitTransducer]) fun b => evalFrom_delimit _

/-! ### The word whose delimited code starts the input -/

/-- At the start of the input, about to read a tag, about to read a data bit, or past the
delimiter. -/
private inductive UndelimitState : Type
  | start
  | tag
  | bit
  | done
  deriving Fintype

/-- The transducer emits data bits until the delimiter and emits the default `e` on empty input. -/
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

private def undelimitFrom (e : List Bool) (q : UndelimitState) (w : List Bool) : List Bool :=
  match q with
  | .start => undelimitOr e w
  | .tag => undelimit w
  | .bit => w.head?.toList ++ undelimit w.tail
  | .done => []

private lemma evalFrom_undelimit (e : List Bool) :
    (undelimitTransducer e).evalFrom = undelimitFrom e := by
  apply SubsequentialTransducer.evalFrom_unique
  · intro q
    cases q <;> rfl
  · intro q b w
    cases q <;> cases b <;> cases w <;> rfl

/-- `undelimitOr e` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_undelimitOr (e : List Bool) :
    ComputableInTimeAndSpace (undelimitOr e) encBits encBits
      (fun w => 2 * w.length + e.length + 1) (fun _ => 0) :=
  (computableInTimeAndSpace_of_subsequential (undelimitTransducer e) (undelimitOr e)
    (fun w => congrFun₂ (evalFrom_undelimit e) _ w)).mono
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

private def dropDelimitedFrom (q : DropDelimitedState) (w : List Bool) : List Bool :=
  match q with
  | .tag => dropDelimited w
  | .bit => dropDelimited w.tail
  | .copy => w

private lemma evalFrom_dropDelimited :
    dropDelimitedTransducer.evalFrom = dropDelimitedFrom := by
  apply SequentialTransducer.evalFrom_unique
  · intro q
    cases q <;> rfl
  · intro q b w
    cases q <;> cases b <;> cases w <;> rfl

/-- `dropDelimited` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_dropDelimited :
    ComputableInTimeAndSpace dropDelimited encBits encBits (fun w => 2 * w.length + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_sequential dropDelimitedTransducer dropDelimited
    (fun w => congrFun₂ evalFrom_dropDelimited _ w)).mono
    (fun _ => by lia [length_dropDelimited_le]) fun _ => le_rfl

/-! ### All delimited codes -/

/-- The state records whether a data bit follows. -/
private def undelimitAllTransducer : SequentialTransducer Bool Bool Bool where
  start := false
  tr bit b := !bit && b
  emit bit b := if bit then [b] else []

private def undelimitAllFrom (q : Bool) (w : List Bool) : List Bool :=
  match q with
  | false => undelimitAll w
  | true => w.head?.toList ++ undelimitAll w.tail

private lemma evalFrom_undelimitAll :
    undelimitAllTransducer.evalFrom = undelimitAllFrom := by
  apply SequentialTransducer.evalFrom_unique
  · intro q
    cases q <;> rfl
  · intro q b w
    cases q <;> cases b <;> cases w <;> rfl

/-- `undelimitAll` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_undelimitAll :
    ComputableInTimeAndSpace undelimitAll encBits encBits (fun w => 2 * w.length + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_sequential undelimitAllTransducer undelimitAll
    (fun w => congrFun₂ evalFrom_undelimitAll _ w)).mono
    (fun _ => by lia [length_undelimitAll_le]) fun _ => le_rfl

end Turing.MultiTapeTM
