/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Encoding.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Subsequential
import Mathlib.Data.Fintype.Option

/-!
# Machines inspecting the first bit of a word

Many accessors of the default encodings only inspect or change the first bit of a code word, which
is the tag of a sum or the least significant bit of a number. `Cslib.Encoding.headCases` captures
these functions on words. Its subsequential transducer emits `g b` on the first bit `b`,
then copies or discards the remaining bits according to `keep b`. On empty input its final
output is `e`.

## Main definitions

* `Cslib.Encoding.headCases`: a function on words that depends only on the first bit, and either
  keeps or drops the rest.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_headCases`: `headCases` is computable in linear
  time and zero space.
-/

public section

namespace Cslib.Encoding

/-- A function on words that depends only on the first bit: the empty word is mapped to `e`, and
a word starting with `b` to `g b`, followed by the rest of the word if `keep b`. -/
@[expose]
def headCases (e : List Bool) (g : Bool → List Bool) (keep : Bool → Bool) : List Bool → List Bool
  | [] => e
  | b :: w => g b ++ if keep b then w else []

variable (e : List Bool) (g : Bool → List Bool) (keep : Bool → Bool)

@[simp]
theorem headCases_nil : headCases e g keep [] = e := rfl

@[simp]
theorem headCases_cons (b : Bool) (w : List Bool) :
    headCases e g keep (b :: w) = g b ++ if keep b then w else [] := rfl

theorem length_headCases_le (w : List Bool) :
    (headCases e g keep w).length ≤
      w.length + max e.length (max (g false).length (g true).length) := by
  cases w with
  | nil => simp
  | cons b w => cases b <;> grind [headCases_cons]

end Cslib.Encoding

namespace Turing.MultiTapeTM

open Cslib.Encoding Cslib.Automata

/-- At the start of the input (`none`), or past the first bit and keeping the rest of the input or
not. -/
private def headCasesTransducer (e : List Bool) (g : Bool → List Bool) (keep : Bool → Bool) :
    SubsequentialTransducer (Option Bool) Bool Bool where
  start := none
  step
    | none, b => (g b, some (keep b))
    | some true, b => ([b], some true)
    | some false, _ => ([], some false)
  final
    | none => e
    | some _ => []

private lemma outputFrom_headCases_some {e : List Bool} {g : Bool → List Bool}
    {keep : Bool → Bool} (k : Bool) (w : List Bool) :
    (headCasesTransducer e g keep).outputFrom (some k) w = if k then w else [] := by
  induction w <;> cases k <;> simp_all [headCasesTransducer]

/-- `headCases e g keep` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_headCases (e : List Bool) (g : Bool → List Bool)
    (keep : Bool → Bool) :
    ComputableInTimeAndSpace (headCases e g keep) encBits encBits
      (fun w => 2 * w.length + max e.length (max (g false).length (g true).length) + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_subsequential (headCasesTransducer e g keep)
    (headCases e g keep) fun w => by
      rw [SubsequentialTransducer.translates_iff_output_eq]
      cases w with
      | nil => rfl
      | cons b w => exact congrArg (g b ++ ·) (outputFrom_headCases_some (keep b) w)).mono
    (fun _ => by lia [length_headCases_le]) fun _ => le_rfl

end Turing.MultiTapeTM
