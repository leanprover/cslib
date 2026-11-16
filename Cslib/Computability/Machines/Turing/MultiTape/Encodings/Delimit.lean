/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Basic

/-!
# Machines for delimited words

One-way machines computing the functions on Boolean words that take delimited codes apart. They
take linear time and no space.

## Main results

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

open Cslib.Encoding

/-! ### The word whose delimited code starts the input -/

/-- At the start of the input, about to read a tag, about to read a data bit, or past the
delimiter. -/
private inductive UndelimitState : Type
  | start
  | tag
  | bit
  | done
  deriving DecidableEq

private instance : Fintype UndelimitState :=
  ⟨{.start, .tag, .bit, .done}, fun q => by cases q <;> simp⟩

/-- The tag `true` announces a data bit, which is emitted, and the tag `false` ends the code,
after which nothing is emitted. -/
private def undelimitStep : UndelimitState → Bool → List Bool × UndelimitState
  | .start, true | .tag, true => ([], .bit)
  | .start, false | .tag, false => ([], .done)
  | .bit, b => ([b], .tag)
  | .done, _ => ([], .done)

/-- The default `e` is emitted at the end of an empty input. -/
private def undelimitFinal (e : List Bool) : UndelimitState → List Bool
  | .start => e
  | _ => []

private def undelimitFrom (e : List Bool) : UndelimitState → List Bool → List Bool
  | .start, w => undelimitOr e w
  | .tag, w => undelimit w
  | .bit, w => w.head?.toList ++ undelimit w.tail
  | .done, _ => []

private lemma oneWayOutput_undelimit (e : List Bool) (q : UndelimitState) (w : List Bool) :
    oneWayOutput undelimitStep (undelimitFinal e) q w = undelimitFrom e q w := by
  induction w generalizing q with
  | nil => cases q <;> simp [undelimitFinal, undelimitFrom]
  | cons a w ih => cases q <;> cases a <;> cases w <;> simp [undelimitStep, undelimitFrom, ih]

/-- `undelimitOr e` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_undelimitOr (e : List Bool) :
    ComputableInTimeAndSpace (undelimitOr e) encBits encBits
      (fun w => 2 * w.length + e.length + 1) (fun _ => 0) :=
  (computableInTimeAndSpace_of_oneWayOutput_eq .start undelimitStep (undelimitFinal e)
    fun w => by rw [oneWayOutput_undelimit, undelimitFrom]).mono
    (fun w => by have := length_undelimitOr_le e w; lia) fun _ => le_rfl

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
  deriving DecidableEq

private instance : Fintype DropDelimitedState :=
  ⟨{.tag, .bit, .copy}, fun q => by cases q <;> simp⟩

private def dropDelimitedStep : DropDelimitedState → Bool → List Bool × DropDelimitedState
  | .tag, true => ([], .bit)
  | .tag, false => ([], .copy)
  | .bit, _ => ([], .tag)
  | .copy, b => ([b], .copy)

private def dropDelimitedFrom : DropDelimitedState → List Bool → List Bool
  | .tag, w => dropDelimited w
  | .bit, w => dropDelimited w.tail
  | .copy, w => w

private lemma oneWayOutput_dropDelimited (q : DropDelimitedState) (w : List Bool) :
    oneWayOutput dropDelimitedStep (fun _ => []) q w = dropDelimitedFrom q w := by
  induction w generalizing q with
  | nil => cases q <;> simp [dropDelimitedFrom]
  | cons a w ih =>
    cases q <;> cases a <;> cases w <;> simp [dropDelimitedStep, dropDelimitedFrom, ih]

/-- `dropDelimited` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_dropDelimited :
    ComputableInTimeAndSpace dropDelimited encBits encBits (fun w => 2 * w.length + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_oneWayOutput_eq .tag dropDelimitedStep (fun _ => [])
    fun w => by rw [oneWayOutput_dropDelimited, dropDelimitedFrom]).mono
    (fun w => by have := length_dropDelimited_le w; lia) fun _ => le_rfl

/-! ### All delimited codes -/

/-- The state records whether a data bit follows. -/
private def undelimitAllStep : Bool → Bool → List Bool × Bool
  | false, true => ([], true)
  | false, false => ([], false)
  | true, b => ([b], false)

private def undelimitAllFrom : Bool → List Bool → List Bool
  | false, w => undelimitAll w
  | true, w => w.head?.toList ++ undelimitAll w.tail

private lemma oneWayOutput_undelimitAll (q : Bool) (w : List Bool) :
    oneWayOutput undelimitAllStep (fun _ => []) q w = undelimitAllFrom q w := by
  induction w generalizing q with
  | nil => cases q <;> simp [undelimitAllFrom]
  | cons a w ih => cases q <;> cases a <;> cases w <;> simp [undelimitAllStep, undelimitAllFrom, ih]

/-- `undelimitAll` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_undelimitAll :
    ComputableInTimeAndSpace undelimitAll encBits encBits (fun w => 2 * w.length + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_oneWayOutput_eq false undelimitAllStep (fun _ => [])
    fun w => by rw [oneWayOutput_undelimitAll, undelimitAllFrom]).mono
    (fun w => by have := length_undelimitAll_le w; lia) fun _ => le_rfl

end Turing.MultiTapeTM
