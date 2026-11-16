/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Basic

/-!
# Machines inspecting the first bit of a word

Many accessors of the default encodings only inspect or change the first bit of a code word, which
is the tag of a sum or the least significant bit of a number. `Cslib.Encoding.headCases` captures
all of these functions on words, and a single one-way machine computes them.

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
  rcases w with _ | ⟨b, w⟩
  · simp
  · have : (if keep b then w else []).length ≤ w.length := by split <;> simp
    cases b <;> simp only [headCases_cons, List.length_append, List.length_cons] <;> lia

end Cslib.Encoding

namespace Turing.MultiTapeTM

open Cslib.Encoding

/-- At the start of the input (`none`), or past the first bit and keeping the rest of the input or
not. -/
private def headCasesStep (g : Bool → List Bool) (keep : Bool → Bool) :
    Option Bool → Bool → List Bool × Option Bool
  | none, b => (g b, some (keep b))
  | some true, b => ([b], some true)
  | some false, _ => ([], some false)

/-- `e` is emitted at the end of an empty input. -/
private def headCasesFinal (e : List Bool) : Option Bool → List Bool
  | none => e
  | some _ => []

private lemma oneWayOutput_headCases_some {e : List Bool} {g : Bool → List Bool}
    {keep : Bool → Bool} (k : Bool) (w : List Bool) :
    oneWayOutput (headCasesStep g keep) (headCasesFinal e) (some k) w = if k then w else [] := by
  induction w <;> cases k <;> simp_all [headCasesStep, headCasesFinal]

/-- `headCases e g keep` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_headCases (e : List Bool) (g : Bool → List Bool)
    (keep : Bool → Bool) :
    ComputableInTimeAndSpace (headCases e g keep) encBits encBits
      (fun w => 2 * w.length + max e.length (max (g false).length (g true).length) + 1)
      (fun _ => 0) :=
  (computableInTimeAndSpace_of_oneWayOutput_eq none (headCasesStep g keep) (headCasesFinal e)
    fun w => by
      cases w <;> simp [headCasesStep, headCasesFinal, oneWayOutput_headCases_some]).mono
    (fun w => by have := length_headCases_le e g keep w; lia) fun _ => le_rfl

end Turing.MultiTapeTM
