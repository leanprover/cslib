/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Encoding.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Transducer
import Mathlib.Data.Fintype.Option

/-!
# Complexity of operations on the first bit of a Boolean word

A multitape Turing machine computes `headCases e g keep` in linear time and zero work space.
This function is useful when reading a sum tag or the least significant bit of a number.
The construction uses a subsequential transducer that reads the first bit to decide whether to copy
or discard the tail.

## Main definitions

* `Cslib.Encoding.headCases` replaces the first bit with a word and uses that bit to decide
  whether to copy the remaining input. It returns a supplied default on empty input.

## Main results

* `Cslib.Encoding.length_headCases_le` bounds the output length by the input length plus the
  maximum length of the default and the two replacement words.
* `Turing.MultiTapeTM.computableInTimeAndSpace_headCases` bounds the running time by twice the
  input length plus a constant depending on `e` and `g`, using zero work space.
-/

public section

namespace Cslib.Encoding

/-- Return `e` on empty input. Otherwise replace the first bit `b` with `g b` and
copy the tail if `keep b` is true. -/
@[expose]
def headCases (e : List Bool) (g : Bool → List Bool) (keep : Bool → Bool) : List Bool → List Bool
  | [] => e
  | b :: w => g b ++ if keep b then w else []

attribute [simp] headCases.eq_1 headCases.eq_2

variable (e : List Bool) (g : Bool → List Bool) (keep : Bool → Bool)

/-- The output is at most as long as the input plus the longest of `e`, `g false` and
`g true`. -/
theorem length_headCases_le (w : List Bool) :
    (headCases e g keep w).length ≤
      w.length + max e.length (max (g false).length (g true).length) := by
  cases w with
  | nil => simp
  | cons b w => cases b <;> grind [headCases]

end Cslib.Encoding

namespace Turing.MultiTapeTM

open Cslib.Encoding Cslib.Automata

/-- Start in `none` and emit `e` if the input is empty. After reading the first bit,
`some true` copies the tail and `some false` discards it. -/
private def headCasesTransducer (e : List Bool) (g : Bool → List Bool) (keep : Bool → Bool) :
    SubsequentialTransducer (Option Bool) Bool Bool where
  start := none
  tr
    | none, b => some (keep b)
    | some k, _ => some k
  emit
    | none, b => g b
    | some true, b => [b]
    | some false, _ => []
  finalOut
    | none => e
    | some _ => []

private def headCasesFrom (e : List Bool) (g : Bool → List Bool) (keep : Bool → Bool)
    (q : Option Bool) (w : List Bool) : List Bool :=
  match q with
  | none => headCases e g keep w
  | some true => w
  | some false => []

private lemma evalFrom_headCases (e : List Bool) (g : Bool → List Bool) (keep : Bool → Bool) :
    (headCasesTransducer e g keep).evalFrom = headCasesFrom e g keep := by
  apply SubsequentialTransducer.evalFrom_unique
  · rintro (_ | (_ | _)) <;> rfl
  · rintro (_ | (_ | _)) b w <;> cases h : keep b <;> simp [headCasesTransducer, headCasesFrom, h]

/-- `headCases e g keep` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_headCases (e : List Bool) (g : Bool → List Bool)
    (keep : Bool → Bool) :
    ComputableInTimeAndSpace (headCases e g keep) encBits encBits
      (fun w => 2 * w.length + max e.length (max (g false).length (g true).length) + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_subsequential (headCasesTransducer e g keep)
    (headCases e g keep) fun w => congrFun₂ (evalFrom_headCases e g keep) _ w).mono
    (fun _ => by lia [length_headCases_le]) fun _ => le_rfl

end Turing.MultiTapeTM
